#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import BinaryIO

EVENT_SCHEMA = "fln.lsp-interleaved-event/1"
RECEIPT_SCHEMA = "fln.lsp-timeline-fixture-build/1"
SOURCE_FORMAT = "direction-tab-json-v1"
MAX_EVENTS = 1_000_000
MAX_MESSAGE_BYTES = 64 * 1024 * 1024
MAX_TIMELINE_BYTES = 256 * 1024 * 1024
MAX_INPUT_BYTES = 256 * 1024 * 1024
MAX_LINE_BYTES = MAX_MESSAGE_BYTES + 16


class TimelineBuildError(ValueError):
    pass


@dataclass(frozen=True)
class BuildResult:
    data: bytes
    events: int
    body_bytes: int
    input_bytes: int
    input_sha256: str
    output_sha256: str


def _object_without_duplicates(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise TimelineBuildError(f"duplicate JSON object key {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> object:
    raise TimelineBuildError(f"non-JSON numeric constant {value!r}")


def _validate_message(message: str, line_number: int) -> bytes:
    if not message:
        raise TimelineBuildError(f"line {line_number}: inner JSON-RPC message is empty")
    if message != message.strip():
        raise TimelineBuildError(
            f"line {line_number}: inner message must not have surrounding whitespace"
        )
    try:
        decoded = json.loads(
            message,
            object_pairs_hook=_object_without_duplicates,
            parse_constant=_reject_constant,
        )
    except TimelineBuildError as error:
        raise TimelineBuildError(f"line {line_number}: {error}") from error
    except json.JSONDecodeError as error:
        raise TimelineBuildError(
            f"line {line_number}: malformed inner JSON at column {error.colno}: {error.msg}"
        ) from error
    if not isinstance(decoded, dict):
        raise TimelineBuildError(
            f"line {line_number}: inner JSON-RPC message must be an object"
        )
    encoded = message.encode("utf-8")
    if len(encoded) > MAX_MESSAGE_BYTES:
        raise TimelineBuildError(
            f"line {line_number}: inner message is {len(encoded)} bytes; limit is {MAX_MESSAGE_BYTES}"
        )
    return encoded


def build_timeline(stream: BinaryIO) -> BuildResult:
    output = bytearray()
    events = 0
    body_bytes = 0
    input_bytes = 0
    input_hash = hashlib.sha256()
    line_number = 0

    while True:
        raw_line = stream.readline(MAX_LINE_BYTES + 1)
        if not raw_line:
            break
        line_number += 1
        input_bytes += len(raw_line)
        input_hash.update(raw_line)
        if input_bytes > MAX_INPUT_BYTES:
            raise TimelineBuildError(
                f"input exceeds the {MAX_INPUT_BYTES}-byte aggregate limit"
            )
        if len(raw_line) > MAX_LINE_BYTES:
            raise TimelineBuildError(
                f"line {line_number} exceeds the {MAX_LINE_BYTES}-byte line limit"
            )
        line = raw_line.removesuffix(b"\n").removesuffix(b"\r")
        if not line:
            continue
        try:
            text = line.decode("utf-8")
        except UnicodeDecodeError as error:
            raise TimelineBuildError(
                f"line {line_number}: input is not valid UTF-8 at byte {error.start}"
            ) from error
        direction, separator, message = text.partition("\t")
        if not separator:
            raise TimelineBuildError(
                f"line {line_number}: expected DIRECTION, one tab, then raw JSON"
            )
        if direction not in {"client", "server"}:
            raise TimelineBuildError(
                f"line {line_number}: direction must be 'client' or 'server', got {direction!r}"
            )
        message_bytes = _validate_message(message, line_number)
        events += 1
        if events > MAX_EVENTS:
            raise TimelineBuildError(
                f"input exceeds the {MAX_EVENTS}-event timeline limit"
            )
        body = (
            b'{"schema":"'
            + EVENT_SCHEMA.encode("ascii")
            + b'","direction":"'
            + direction.encode("ascii")
            + b'","message":'
            + message_bytes
            + b"}"
        )
        if len(body) > MAX_MESSAGE_BYTES:
            raise TimelineBuildError(
                f"line {line_number}: wrapped event is {len(body)} bytes; frame limit is {MAX_MESSAGE_BYTES}"
            )
        frame = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body
        if len(output) + len(frame) > MAX_TIMELINE_BYTES:
            raise TimelineBuildError(
                f"output exceeds the {MAX_TIMELINE_BYTES}-byte timeline limit"
            )
        output.extend(frame)
        body_bytes += len(body)

    if events == 0:
        raise TimelineBuildError("input contains no timeline events")
    data = bytes(output)
    return BuildResult(
        data=data,
        events=events,
        body_bytes=body_bytes,
        input_bytes=input_bytes,
        input_sha256=input_hash.hexdigest(),
        output_sha256=hashlib.sha256(data).hexdigest(),
    )


def _fsync_directory(path: Path) -> None:
    flags = os.O_RDONLY
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    try:
        descriptor = os.open(path, flags)
    except OSError:
        return
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def publish_new(path: Path, data: bytes) -> None:
    parent = path.parent if path.parent != Path("") else Path(".")
    if not parent.is_dir():
        raise TimelineBuildError(f"output parent directory does not exist: {parent}")
    if path.exists() or path.is_symlink():
        raise TimelineBuildError(f"refusing to overwrite existing output: {path}")
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".partial", dir=parent
    )
    temporary = Path(temporary_name)
    linked = False
    try:
        with os.fdopen(descriptor, "wb", closefd=True) as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        try:
            os.link(temporary, path)
            linked = True
        except FileExistsError as error:
            raise TimelineBuildError(
                f"refusing to overwrite existing output: {path}"
            ) from error
        except OSError as error:
            raise TimelineBuildError(f"could not publish output {path}: {error}") from error
        _fsync_directory(parent)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
        except OSError as error:
            if linked:
                raise TimelineBuildError(
                    f"output {path} is complete, but staging cleanup failed: {error}"
                ) from error


def _input_stream(path: str) -> tuple[BinaryIO, bool]:
    if path == "-":
        return sys.stdin.buffer, False
    source = Path(path)
    try:
        metadata = source.lstat()
    except OSError as error:
        raise TimelineBuildError(f"could not inspect input {source}: {error}") from error
    if source.is_symlink():
        raise TimelineBuildError(f"refusing symlink input: {source}")
    if not stat.S_ISREG(metadata.st_mode):
        raise TimelineBuildError(f"input is not a regular file: {source}")
    if metadata.st_size > MAX_INPUT_BYTES:
        raise TimelineBuildError(
            f"input is {metadata.st_size} bytes; limit is {MAX_INPUT_BYTES}"
        )
    try:
        return source.open("rb"), True
    except OSError as error:
        raise TimelineBuildError(f"could not open input {source}: {error}") from error


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Build a deterministic fixture-only FrankenLean interleaved LSP timeline "
            "from lines formatted as DIRECTION<TAB>RAW_JSON. Raw inner JSON is "
            "validated but not reserialized, preserving number lexemes and string escapes."
        )
    )
    parser.add_argument("input", help="input path, or - for stdin")
    parser.add_argument("output", help="new output timeline path")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    arguments = parse_args(sys.argv[1:] if argv is None else argv)
    output = Path(arguments.output)
    if arguments.output == "-":
        print("build_lsp_timeline.py: output '-' is not supported", file=sys.stderr)
        return 2
    stream: BinaryIO | None = None
    close_stream = False
    try:
        stream, close_stream = _input_stream(arguments.input)
        result = build_timeline(stream)
        publish_new(output, result.data)
    except TimelineBuildError as error:
        print(f"build_lsp_timeline.py: {error}", file=sys.stderr)
        return 1
    except OSError as error:
        print(f"build_lsp_timeline.py: I/O error: {error}", file=sys.stderr)
        return 1
    finally:
        if close_stream and stream is not None:
            stream.close()
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "authority": False,
        "purpose": "fixture-generation",
        "sourceFormat": SOURCE_FORMAT,
        "eventSchema": EVENT_SCHEMA,
        "events": result.events,
        "inputBytes": result.input_bytes,
        "inputSha256": result.input_sha256,
        "bodyBytes": result.body_bytes,
        "wireBytes": len(result.data),
        "timelineSha256": result.output_sha256,
        "output": str(output),
    }
    print(json.dumps(receipt, ensure_ascii=False, separators=(",", ":"), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
