#!/usr/bin/env python3
from __future__ import annotations

import contextlib
import importlib.util
import io
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name("build_lsp_timeline.py")
SPEC = importlib.util.spec_from_file_location("build_lsp_timeline", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class BuildTimelineTests(unittest.TestCase):
    def test_preserves_request_identity_lexemes_and_unicode_lengths(self) -> None:
        source = (
            "client\t"
            + r'{"jsonrpc":"2.0","id":1.25e2,"method":"x","params":{"s":"\u0069🤖"}}'
            + "\n"
            + 'server\t{"jsonrpc":"2.0","id":1.25e2,"result":null}\n'
        ).encode()
        result = MODULE.build_timeline(io.BytesIO(source))
        self.assertEqual(result.events, 2)
        self.assertIn(b'"id":1.25e2', result.data)
        self.assertIn(b'"s":"\\u0069\xf0\x9f\xa4\x96"', result.data)
        self.assertNotIn(b'"id":125.0', result.data)
        first_body = result.data.split(b"\r\n\r\n", 1)[1]
        first_length = int(result.data.split(b"\r\n", 1)[0].split(b":", 1)[1])
        self.assertEqual(len(first_body[:first_length]), first_length)

    def test_rejects_duplicate_keys_invalid_directions_and_empty_inputs(self) -> None:
        with self.assertRaisesRegex(MODULE.TimelineBuildError, "duplicate JSON object key"):
            MODULE.build_timeline(io.BytesIO(b'client\t{"id":1,"id":2}\n'))
        with self.assertRaisesRegex(MODULE.TimelineBuildError, "direction must be"):
            MODULE.build_timeline(io.BytesIO(b'upstream\t{}\n'))
        with self.assertRaisesRegex(MODULE.TimelineBuildError, "no timeline events"):
            MODULE.build_timeline(io.BytesIO(b"\n"))

    def test_publication_is_no_clobber(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "timeline.frames"
            MODULE.publish_new(path, b"complete")
            self.assertEqual(path.read_bytes(), b"complete")
            with self.assertRaisesRegex(MODULE.TimelineBuildError, "refusing to overwrite"):
                MODULE.publish_new(path, b"replacement")
            self.assertEqual(path.read_bytes(), b"complete")

    def test_main_writes_a_non_authoritative_fixture_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "events.txt"
            output = Path(directory) / "timeline.frames"
            source.write_text(
                'client\t{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}\n'
            )
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(MODULE.main([str(source), str(output)]), 0)
            self.assertTrue(output.is_file())
            self.assertIn('"authority":false', stdout.getvalue())
            self.assertIn('"purpose":"fixture-generation"', stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
