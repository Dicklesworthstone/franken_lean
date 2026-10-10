use super::*;

fn limits(max_work: u64, max_output_bytes: usize) -> FormatRenderLimits {
    FormatRenderLimits {
        max_work,
        max_output_bytes,
    }
}

#[test]
fn utf8_columns_hard_lines_and_negative_indentation_keep_exact_byte_limits() {
    let words = || {
        Format::text("α")
            .then(Format::Line)
            .then(Format::text("β"))
            .then(Format::Line)
            .then(Format::text("γ"))
            .then(Format::Line)
            .then(Format::text("δ"))
    };
    for (format, width, expected) in [
        (words().fill(), 4, "α β\nγ δ"),
        (Format::text("é\n😀").nest(2).group(), 120, "é\n  😀"),
        (Format::text("é\n\nβ\n").nest(2), 120, "é\n  \n  β\n  "),
        (
            Format::text("a")
                .then(Format::Line)
                .then(Format::text("b"))
                .nest(-8)
                .group(),
            1,
            "a\nb",
        ),
        (
            Format::text("a")
                .then(Format::Align(true))
                .then(Format::text("b"))
                .nest(-8),
            120,
            "a\nb",
        ),
    ] {
        let exact = limits(100_000, expected.len());
        assert_eq!(format.try_pretty(width, exact), Ok(expected.to_owned()));
        let one_byte_short = limits(exact.max_work, exact.max_output_bytes - 1);
        assert!(matches!(
            format.try_pretty(width, one_byte_short),
            Err(FormatRenderError::OutputLimit { limit, requested })
                if limit == expected.len() - 1 && requested > limit
        ));
    }
}

#[test]
fn lookahead_and_text_scans_share_the_work_allowance_with_emission() {
    // The plain text needs one scan and one emission. Grouping adds a complete
    // lookahead over the same text; that extra traversal must not be free.
    let text = "é".repeat(2_048);
    let allowance = limits(9_000, text.len());
    assert_eq!(
        Format::text(&text).try_pretty(3_000, allowance),
        Ok(text.clone())
    );
    assert_eq!(
        Format::text(&text).group().try_pretty(3_000, allowance),
        Err(FormatRenderError::WorkLimit { limit: 9_000 })
    );

    // Lookahead stops before any emission: an output allowance of zero cannot
    // turn a stopped traversal into an output-limit error or an empty success.
    assert_eq!(
        Format::text(text).group().try_pretty(3_000, limits(100, 0)),
        Err(FormatRenderError::WorkLimit { limit: 100 })
    );
}

#[test]
fn fill_trials_have_a_reproducible_exact_work_boundary() {
    let mut format = Format::text("α");
    for word in ["beta", "γ", "delta", "ε", "zeta", "η", "theta"] {
        format = format.then(Format::Line).then(Format::text(word));
    }
    let format = format.nest(2).fill();
    let expected = "α beta γ\n  delta ε\n  zeta η\n  theta";
    assert_eq!(
        format.try_pretty(9, limits(100_000, expected.len())),
        Ok(expected.to_owned())
    );

    // Locate the public API's first successful allowance, then check both sides
    // of that exact boundary again. No private meter value supplies the answer.
    let (mut low, mut high) = (0, 100_000);
    while low < high {
        let middle = low + (high - low) / 2;
        match format.try_pretty(9, limits(middle, expected.len())) {
            Ok(text) => {
                assert_eq!(text, expected);
                high = middle;
            }
            Err(FormatRenderError::WorkLimit { limit }) => {
                assert_eq!(limit, middle);
                low = middle + 1;
            }
            other => panic!("unexpected bounded fill result: {other:?}"),
        }
    }
    assert!(low > 1);
    assert_eq!(
        format.try_pretty(9, limits(low, expected.len())),
        Ok(expected.to_owned())
    );
    assert_eq!(
        format.try_pretty(9, limits(low - 1, expected.len())),
        Err(FormatRenderError::WorkLimit { limit: low - 1 })
    );
}

#[test]
fn indentation_is_bounded_before_any_padding_allocation() {
    let line = Format::Line.nest(8);
    assert_eq!(
        line.try_pretty(120, limits(100, 9)),
        Ok("\n        ".to_owned())
    );
    assert_eq!(
        line.try_pretty(120, limits(100, 8)),
        Err(FormatRenderError::OutputLimit {
            limit: 8,
            requested: 9,
        })
    );
    let align = Format::Align(true).nest(8);
    assert_eq!(
        align.try_pretty(120, limits(100, 8)),
        Ok("        ".to_owned())
    );
    assert_eq!(
        align.try_pretty(120, limits(100, 7)),
        Err(FormatRenderError::OutputLimit {
            limit: 7,
            requested: 8,
        })
    );

    // This is a valid i64 indentation, but it must never be allocated under a
    // small output ceiling. A 32-bit target cannot represent it at all.
    for format in [
        Format::Line.nest(i64::MAX),
        Format::Align(true).nest(i64::MAX),
    ] {
        assert!(matches!(
            format.try_pretty(120, limits(100, 32)),
            Err(FormatRenderError::OutputLimit { limit: 32, .. })
                | Err(FormatRenderError::ArithmeticOverflow)
        ));
    }
}

#[test]
fn signed_nesting_overflow_is_a_typed_stop_and_wide_measurement_stays_exact() {
    for format in [
        Format::Line.nest(i64::MAX).nest(1),
        Format::Line.nest(i64::MIN).nest(-1),
    ] {
        assert_eq!(
            format.try_pretty(120, limits(100, 32)),
            Err(FormatRenderError::ArithmeticOverflow)
        );
    }

    // Both endpoints are individually valid. Lookahead must not saturate the
    // unsigned width or overflow while subtracting a large negative indent.
    let format = Format::text("a")
        .then(Format::Line)
        .then(Format::text("b"))
        .nest(i64::MIN)
        .group();
    assert_eq!(
        format.try_pretty(usize::MAX, limits(100, 3)),
        Ok("a b".to_owned())
    );
    assert_eq!(
        Format::Line.nest(i64::MIN).try_pretty(0, limits(100, 1)),
        Ok("\n".to_owned())
    );
}

#[test]
fn empty_deep_formats_spend_control_work_on_a_small_stack() {
    std::thread::Builder::new()
        .name("bounded-format-stack".to_owned())
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut format = Format::Nil;
            for _ in 0..256 {
                format = Format::Append(Box::new(Format::Nil), Box::new(format));
            }
            assert_eq!(format.try_pretty(0, limits(10_000, 0)), Ok(String::new()));
            assert_eq!(
                format.try_pretty(0, limits(64, 0)),
                Err(FormatRenderError::WorkLimit { limit: 64 })
            );
            assert_eq!(
                Format::Nil.try_pretty(0, limits(0, 0)),
                Err(FormatRenderError::WorkLimit { limit: 0 })
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn impossible_storage_requests_use_the_real_fallible_allocation_path() {
    let mut renderer = Renderer::new(limits(u64::MAX, usize::MAX));
    assert_eq!(
        renderer.reserve_output(usize::MAX),
        Err(FormatRenderError::AllocationFailure)
    );
    assert!(renderer.out.is_empty());

    let mut meter = Meter {
        limits: limits(u64::MAX, 0),
        work: 0,
    };
    let mut values = Vec::<u64>::new();
    assert_eq!(
        meter.reserve(&mut values, usize::MAX),
        Err(FormatRenderError::AllocationFailure)
    );
    assert!(values.is_empty());

    let mut renderer = Renderer::new(limits(1, usize::MAX));
    assert_eq!(
        renderer.reserve_output(usize::MAX),
        Err(FormatRenderError::WorkLimit { limit: 1 })
    );
}
