//! Pinned String folds and predicates use ordinary VM call frames. Each
//! character schedules a checked callback; no callback executes on the host
//! stack, and every stop drops the pending traversal and its owned handles.

use super::{
    ApplyPlan, ArgumentOwnership, BigNat, CallableResultOwnership, FunctionId, Obj, PreparedApply,
    ValidatedProgram, VmRefusal, bool_value, exact_owned_args, finish_apply, nat_from_big_nat,
    nat_magnitude_bytes, plan_apply, string_bytes, string_value, strings, with_nat_view,
};

const ROW: &str = "extern:String.Internal.foldl";
const OPERATION: &str = "String.Internal.foldl";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    Foldl,
    Any,
    NextWhile,
    All,
    TakeWhile,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            ROW => Self::Foldl,
            "extern:String.Internal.any" => Self::Any,
            "extern:String.Internal.nextWhile" => Self::NextWhile,
            "extern:Substring.Raw.Internal.all" => Self::All,
            "extern:Substring.Raw.Internal.takeWhile" => Self::TakeWhile,
            _ => return None,
        })
    }

    fn operation(self) -> &'static str {
        match self {
            Self::Foldl => OPERATION,
            Self::Any => "String.Internal.any",
            Self::NextWhile => "String.Internal.nextWhile",
            Self::All => "Substring.Raw.Internal.all",
            Self::TakeWhile => "Substring.Raw.Internal.takeWhile",
        }
    }
}

pub(super) enum Failure {
    Refused(VmRefusal),
    NatMagnitudeLimit { allowed: u64, observed: u64 },
}

impl From<VmRefusal> for Failure {
    fn from(refusal: VmRefusal) -> Self {
        Self::Refused(refusal)
    }
}

pub(super) enum State {
    Fold(FoldState),
    Predicate(PredicateState),
}

pub(super) struct FoldState {
    callback: Obj,
    // Decode the borrowed input once. The offset advances only by the width
    // of a decoded scalar, so a continuation never starts inside UTF-8.
    input: String,
    offset: usize,
    // A curried callback first consumes the accumulator, then its returned
    // closure consumes this scalar. Flat callbacks leave the slot empty.
    pending_character: Option<Obj>,
}

pub(super) struct PredicateState {
    intrinsic: Intrinsic,
    callback: Obj,
    input: Obj,
    start: Obj,
    position: BigNat,
    stop: BigNat,
    max_nat_magnitude_bytes: u64,
}

pub(super) enum Step {
    Complete(Obj),
    Call {
        function: FunctionId,
        args: Vec<Obj>,
        state: State,
    },
}

pub(super) fn start(
    program: &ValidatedProgram,
    intrinsic: Intrinsic,
    row: &str,
    args: Vec<Obj>,
    max_nat_magnitude_bytes: u64,
) -> Result<Step, Failure> {
    if intrinsic == Intrinsic::Foldl {
        return fold_start(program, args).map_err(Failure::from);
    }
    let operation = intrinsic.operation();
    let (input, start, stop, callback) = match intrinsic {
        Intrinsic::Any => {
            let [input, callback] = exact_owned_args::<2>(row, args)?;
            let end = strings::string_buffer(&input, operation, 0)?.len() - 1;
            (input, Obj::mk_nat(0), Obj::mk_nat(end), callback)
        }
        Intrinsic::NextWhile => {
            let [input, callback, start] = exact_owned_args::<3>(row, args)?;
            let end = strings::string_buffer(&input, operation, 0)?.len() - 1;
            (input, start, Obj::mk_nat(end), callback)
        }
        Intrinsic::All | Intrinsic::TakeWhile => {
            let [source, callback] = exact_owned_args::<2>(row, args)?;
            let raw = strings::Substring::read(&source, operation, 0)?;
            (raw.string, raw.start, raw.stop, callback)
        }
        Intrinsic::Foldl => unreachable!("folds use their accumulator continuation"),
    };
    let position = read_position(&start, operation, max_nat_magnitude_bytes)?;
    let stop = read_position(&stop, operation, max_nat_magnitude_bytes)?;
    let buffer = strings::string_buffer(&input, operation, 0)?;
    predicate_plan(program, &callback)?;
    if intrinsic == Intrinsic::All {
        // The pin's all export first calls toSlice?.get!. An invalid raw
        // record reports the recoverable Option panic, then uses the default
        // empty slice. It never visits the supplied predicate in that case.
        let text = std::str::from_utf8(&buffer[..buffer.len() - 1])
            .map_err(|_| VmRefusal::InvalidStringObject)?;
        let valid = |position: &BigNat| {
            position
                .to_u64()
                .and_then(|position| usize::try_from(position).ok())
                .is_some_and(|position| text.is_char_boundary(position))
        };
        if position > stop || !valid(&position) || !valid(&stop) {
            fln_rt::diagnostics::report_panic(
                b"PANIC at Option.get! Init.Data.Option.BasicAux:22:14: value is none",
            );
            if let Some(error) = fln_rt::obj::StdoutCapture::current_error() {
                return Err(VmRefusal::NativeStdoutCapture { error }.into());
            }
            return Ok(Step::Complete(Obj::mk_nat(1)));
        }
    }
    predicate_next(
        program,
        PredicateState {
            intrinsic,
            callback,
            input,
            start,
            position,
            stop,
            max_nat_magnitude_bytes,
        },
    )
}

pub(super) fn resume(
    program: &ValidatedProgram,
    state: State,
    value: Obj,
) -> Result<Step, Failure> {
    let mut state = match state {
        State::Fold(state) => return fold_resume(program, state, value).map_err(Failure::from),
        State::Predicate(state) => state,
    };
    let matched = bool_value(&value, state.intrinsic.operation(), 0)?;
    if (state.intrinsic == Intrinsic::Any && matched)
        || (state.intrinsic != Intrinsic::Any && !matched)
    {
        return Ok(Step::Complete(state.complete(Some(matched))));
    }
    let buffer = strings::string_buffer(&state.input, state.intrinsic.operation(), 0)?;
    let width = state
        .position
        .to_u64()
        .and_then(|position| usize::try_from(position).ok())
        .filter(|position| *position < buffer.len() - 1)
        .map_or(1, |position| strings::utf8_fast_width(buffer[position]));
    let next = state.position.add(&BigNat::from_u64(width as u64));
    check_position_limit(&next, state.max_nat_magnitude_bytes)?;
    state.position = next;
    predicate_next(program, state)
}

fn check_position_limit(value: &BigNat, allowed: u64) -> Result<(), Failure> {
    let observed = nat_magnitude_bytes(u128::from(value.bit_length()));
    if observed > allowed {
        return Err(Failure::NatMagnitudeLimit { allowed, observed });
    }
    Ok(())
}

fn read_position(value: &Obj, operation: &'static str, allowed: u64) -> Result<BigNat, Failure> {
    with_nat_view(value, operation, 0, |value| {
        let observed = nat_magnitude_bytes(u128::from(value.bit_length()));
        if observed > allowed {
            return Err(Failure::NatMagnitudeLimit { allowed, observed });
        }
        Ok(value.to_owned())
    })?
}

impl PredicateState {
    fn complete(self, predicate: Option<bool>) -> Obj {
        match self.intrinsic {
            Intrinsic::Any => Obj::mk_nat(usize::from(predicate.unwrap_or(false))),
            Intrinsic::All => Obj::mk_nat(usize::from(predicate.unwrap_or(true))),
            Intrinsic::NextWhile => nat_from_big_nat(&self.position),
            Intrinsic::TakeWhile => {
                strings::Substring::make(self.input, self.start, nat_from_big_nat(&self.position))
            }
            Intrinsic::Foldl => unreachable!("folds use their accumulator continuation"),
        }
    }
}

fn predicate_plan(program: &ValidatedProgram, callback: &Obj) -> Result<ApplyPlan, VmRefusal> {
    // Scalar and erased/boxed callback return conventions are both valid:
    // the normal Return path enforces the declared convention, and resume
    // separately requires the actual Boolean scalar. No native closure runs.
    let plan = plan_apply(program, callback, 1, None, None)?;
    if plan.required != 1 {
        return Err(VmRefusal::MalformedClosure {
            reason: "String predicate callback requires exactly one remaining argument",
        });
    }
    let function = program
        .function(plan.function)
        .ok_or(VmRefusal::MalformedClosure {
            reason: "target function is absent",
        })?;
    if function.parameter_ownership[plan.captures.len()] == ArgumentOwnership::Unique {
        return Err(VmRefusal::ApplyOwnershipMismatch {
            function: plan.function,
            argument: 0,
            expected: ArgumentOwnership::Unique,
            actual: ArgumentOwnership::Scalar,
        });
    }
    Ok(plan)
}

fn predicate_next(program: &ValidatedProgram, state: PredicateState) -> Result<Step, Failure> {
    if state.position >= state.stop {
        return Ok(Step::Complete(state.complete(None)));
    }
    let buffer = strings::string_buffer(&state.input, state.intrinsic.operation(), 0)?;
    let bytes = &buffer[..buffer.len() - 1];
    let character = state
        .position
        .to_u64()
        .and_then(|position| usize::try_from(position).ok())
        .filter(|position| *position < bytes.len())
        .and_then(|position| strings::utf8_get_core(bytes, position))
        .unwrap_or('A' as u32);
    let plan = predicate_plan(program, &state.callback)?;
    match finish_apply(plan, vec![Obj::mk_nat(character as usize)], None) {
        PreparedApply::Call { function, args, .. } => Ok(Step::Call {
            function,
            args,
            state: State::Predicate(state),
        }),
        PreparedApply::Partial { .. } => {
            unreachable!("the predicate consumes exactly one argument")
        }
    }
}

fn fold_start(program: &ValidatedProgram, args: Vec<Obj>) -> Result<Step, VmRefusal> {
    let [callback, initial, source] = exact_owned_args::<3>(ROW, args)?;
    string_bytes(&initial, OPERATION, 1)?;
    let input = string_value(&source, OPERATION, 2)?;
    // Even an empty fold requires the row's callable shape, but never runs
    // its body or creates a callback frame.
    if input.is_empty() {
        callback_plan(program, &callback, &[false, true])?;
        return Ok(Step::Complete(initial));
    }
    next(
        program,
        FoldState {
            callback,
            input,
            offset: 0,
            pending_character: None,
        },
        initial,
    )
}

fn fold_resume(
    program: &ValidatedProgram,
    mut state: FoldState,
    value: Obj,
) -> Result<Step, VmRefusal> {
    if let Some(character) = state.pending_character.take() {
        let (function, args, remainder) = prepare(program, &value, vec![character])?;
        state.pending_character = remainder;
        return Ok(Step::Call {
            function,
            args,
            state: State::Fold(state),
        });
    }
    // Callable ownership alone does not establish the String result type:
    // an owned array or closure is still a malformed fold callback result.
    string_bytes(&value, OPERATION, 0)?;
    next(program, state, value)
}

fn next(
    program: &ValidatedProgram,
    mut state: FoldState,
    accumulator: Obj,
) -> Result<Step, VmRefusal> {
    let suffix = state
        .input
        .get(state.offset..)
        .ok_or(VmRefusal::InvalidStringObject)?;
    let Some(character) = suffix.chars().next() else {
        return Ok(Step::Complete(accumulator));
    };
    state.offset += character.len_utf8();
    let (function, args, remainder) = prepare(
        program,
        &state.callback,
        vec![accumulator, Obj::mk_nat(character as usize)],
    )?;
    state.pending_character = remainder;
    Ok(Step::Call {
        function,
        args,
        state: State::Fold(state),
    })
}

fn callback_plan(
    program: &ValidatedProgram,
    callback: &Obj,
    scalar_arguments: &[bool],
) -> Result<ApplyPlan, VmRefusal> {
    let plan = plan_apply(
        program,
        callback,
        scalar_arguments.len(),
        None,
        Some(CallableResultOwnership::Owned),
    )?;
    if plan.required > scalar_arguments.len() {
        return Err(VmRefusal::MalformedClosure {
            reason: "String.Internal.foldl callback requires too many arguments",
        });
    }
    let function = program
        .function(plan.function)
        .ok_or(VmRefusal::MalformedClosure {
            reason: "target function is absent",
        })?;
    let parameters =
        &function.parameter_ownership[plan.captures.len()..plan.captures.len() + plan.required];
    for (argument, (expected, scalar)) in parameters
        .iter()
        .copied()
        .zip(scalar_arguments.iter().copied())
        .enumerate()
    {
        // The fold owns references acquired from its borrowed arguments and
        // from preceding callback results. It can give a reference away or
        // lend it, but cannot promise uniqueness. Character words may use
        // any of the ordinary scalar/owned/borrowed calling dispositions.
        let actual = match expected {
            ArgumentOwnership::Unique => Some(ArgumentOwnership::Borrowed),
            ArgumentOwnership::Scalar if !scalar => Some(ArgumentOwnership::Owned),
            ArgumentOwnership::Borrowed | ArgumentOwnership::Owned | ArgumentOwnership::Scalar => {
                None
            }
        };
        if let Some(actual) = actual {
            return Err(VmRefusal::ApplyOwnershipMismatch {
                function: plan.function,
                argument,
                expected,
                actual,
            });
        }
    }
    Ok(plan)
}

fn prepare(
    program: &ValidatedProgram,
    callback: &Obj,
    args: Vec<Obj>,
) -> Result<(FunctionId, Vec<Obj>, Option<Obj>), VmRefusal> {
    let scalar_arguments: Vec<_> = args.iter().map(Obj::is_scalar).collect();
    let plan = callback_plan(program, callback, &scalar_arguments)?;
    match finish_apply(plan, args, None) {
        PreparedApply::Call {
            function,
            args,
            remainder,
            remainder_ownership: _,
        } => {
            // At most two arguments entered this helper and every checked
            // closure consumes at least one. A remainder is exactly the
            // character waiting for the second half of a curried callback.
            Ok((function, args, remainder.into_iter().next()))
        }
        PreparedApply::Partial { .. } => Err(VmRefusal::MalformedClosure {
            reason: "String.Internal.foldl callback requires too many arguments",
        }),
    }
}
