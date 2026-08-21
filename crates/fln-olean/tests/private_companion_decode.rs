//! Module-system companion-chain decode (bead `franken_lean-timy`): the
//! `.olean.private` part is the authoritative constant array, and decoding the
//! chain must recover the `_private` equation-compiler auxiliary family that the
//! exported `.olean` part omits.
//!
//! WHY THIS SUITE EXISTS. `franken_lean-timy` reported 24 corpus
//! `UnknownConstant` rejections whose missing dependencies were all `_private`
//! equation-compiler auxiliaries (`match_N`, `_proof_N`, `.loop`). The named
//! localisation was intra-module decode coverage: `Init.Data.List.ToArrayImpl`
//! decoded FIVE declarations and
//! `_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1` was not among
//! them. That is exactly what reading the exported part alone produces. The
//! repair is to read the companion chain, whose private part carries a superset
//! of the exported constant array. Before this file, `fln-olean` had no test
//! over a real module-system chain at all, so a decoder that silently returned
//! the exported array again would reintroduce the whole bead unnoticed.
//!
//! EVERY NUMBER BELOW IS MEASURED against the pinned Reference stdlib
//! (leanprover/lean4 v4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35),
//! not assumed. The exported-part counts are asserted alongside the chain counts
//! so a change that made the exported part already complete would fail here
//! rather than turn these assertions vacuous.
//!
//! SCOPE. This suite pins `fln-olean`'s chain-decode capability: given the three
//! parts, the private region decodes to the superset. Which array a downstream
//! consumer chooses to admit is that consumer's surface and is not judged here.

#![forbid(unsafe_code)]

use std::path::PathBuf;

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_olean::decl::{
    ChainLimits, ConstantOrigin, DeclDecoder, DeclError, decode_chain_constants,
    decode_chain_constants_from_parts, decode_chain_constants_with_origin,
};
use fln_olean::region::{OleanView, WalkBudget};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};

/// The pinned Reference stdlib. `FLN_REFERENCE_LIB` overrides; the
/// elan-installed pin is the default. No checked-in fixture carries the
/// `.olean.server`/`.olean.private` companion parts, so an absent toolchain is a
/// loud skip rather than a silent pass.
fn reference_lib() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("FLN_REFERENCE_LIB") {
        let path = PathBuf::from(dir);
        return path.is_dir().then_some(path);
    }
    let home = std::env::var("HOME").ok()?;
    let path = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    path.is_dir().then_some(path)
}

macro_rules! lib_or_skip {
    ($what:expr) => {
        match reference_lib() {
            Some(lib) => lib,
            None => {
                eprintln!(
                    "SKIP {}: pinned Reference stdlib absent (set FLN_REFERENCE_LIB \
                     or install leanprover--lean4---v4.32.0)",
                    $what
                );
                return;
            }
        }
    };
}

/// The three parts of one module-system module, read whole.
struct ChainBytes {
    exported: Vec<u8>,
    server: Vec<u8>,
    private: Vec<u8>,
}

fn chain_bytes(lib: &PathBuf, relative: &str) -> ChainBytes {
    let exported_path = lib.join(format!("{relative}.olean"));
    let server_path = lib.join(format!("{relative}.olean.server"));
    let private_path = lib.join(format!("{relative}.olean.private"));
    let read = |path: &PathBuf| -> Vec<u8> {
        std::fs::read(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
    };
    ChainBytes {
        exported: read(&exported_path),
        server: read(&server_path),
        private: read(&private_path),
    }
}

/// `constNames` of the exported part alone, and of the full chain's private
/// part, as display strings.
fn exported_and_private_names(chain: &ChainBytes) -> (Vec<String>, Vec<String>) {
    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported = exported_view
        .module_data(WalkBudget::default())
        .expect("exported ModuleData decodes");
    assert!(
        exported.is_module,
        "fixture must be a module-system module, else the chain law does not apply"
    );

    let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
        .expect("server part parses against the exported region");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against the exported and server regions");
    let private = private_view
        .module_data(WalkBudget::default())
        .expect("private ModuleData decodes");

    (exported.const_names, private.const_names)
}

/// The exact constant `franken_lean-timy` names as never decoded.
const TIMY_WITNESS: &str = "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1";

/// A private-mangled declaration that is deliberately present in Init.Prelude's
/// exported array as well as its companion chain.
const HEAD_INFO_LOOP_UNSAFE_REC: &str =
    "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec";
/// Its private-only dependency, which must be recovered from the companion.
const HEAD_INFO_LOOP_MATCH_1: &str =
    "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1";
/// The matching public-overlap loop helper for `Lean.Syntax.getTailPos?`.
const TAIL_POS_LOOP_UNSAFE_REC: &str =
    "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec";
/// Its companion-only equation-compiler dependency.
const TAIL_POS_LOOP_MATCH_1: &str = "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop.match_1";
/// Private proof helpers required by the exported `Lean.Name` hash/number
/// overrides in the pinned Prelude artifact.
const NAME_HASH_PROOF_AUXILIARIES: [&str; 2] = [
    "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
    "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
];
/// A generated recursion helper from the pinned `Array.mapM'` companion delta.
const ARRAY_MAP_M_GO: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go";
/// The accompanying compiler proof helpers for `Array.mapM'`.
const ARRAY_MAP_M_PROOF_AUXILIARIES: [&str; 2] = [
    "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
    "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
];
/// The private match definition generated for `Array.of_push_eq_push`.
const ARRAY_OF_PUSH_EQ_PUSH_MATCH_1_1: &str =
    "_private.Init.Data.Array.BasicAux.0.Array.of_push_eq_push.match_1_1";
/// The pin's private array stores this definition in the BasicAux module.
const ARRAY_OF_PUSH_EQ_PUSH_MATCH_1_1_MODULE: &str = "Init/Data/Array/BasicAux";
/// The private theorem relating `List.of` to `List.toArrayAux`.
const LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX: &str =
    "_private.Init.Data.Array.BasicAux.0.List.of_toArrayAux_eq_toArrayAux";
/// The pin's private array stores this theorem in the BasicAux module.
const LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MODULE: &str = "Init/Data/Array/BasicAux";
/// The private recursion helper for `List.of_toArrayAux_eq_toArrayAux`.
const LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_F: &str =
    "_private.Init.Data.Array.BasicAux.0.List.of_toArrayAux_eq_toArrayAux._f";
/// The pin's private array stores this helper in the BasicAux module.
const LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_F_MODULE: &str = "Init/Data/Array/BasicAux";
/// The first private match definition for `List.of_toArrayAux_eq_toArrayAux`.
const LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_1: &str =
    "_private.Init.Data.Array.BasicAux.0.List.of_toArrayAux_eq_toArrayAux.match_1_1";
/// The pin's private array stores this definition in the BasicAux module.
const LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_1_MODULE: &str = "Init/Data/Array/BasicAux";
/// The private size theorem for `List.toArrayAux`.
const LIST_SIZE_TO_ARRAY_AUX: &str = "_private.Init.Data.Array.BasicAux.0.List.size_toArrayAux";
/// The pin's private array stores this theorem in the BasicAux module.
const LIST_SIZE_TO_ARRAY_AUX_MODULE: &str = "Init/Data/Array/BasicAux";
/// The first private equation theorem for `List.toArrayAux`.
const LIST_TO_ARRAY_AUX_EQ_1: &str = "_private.Init.Data.Array.BasicAux.0.List.toArrayAux.eq_1";
/// The pin's private array stores this theorem in the BasicAux module.
const LIST_TO_ARRAY_AUX_EQ_1_MODULE: &str = "Init/Data/Array/BasicAux";
/// The generated argument pusher for `PSigma.casesOn`.
const PSIGMA_CASES_ON_ARG_PUSHER: &str =
    "_private.Init.Data.Array.Basic.0.PSigma.casesOn._arg_pusher";
/// The pin's private array stores this theorem in the Basic module.
const PSIGMA_CASES_ON_ARG_PUSHER_MODULE: &str = "Init/Data/Array/Basic";
/// The first generated equation theorem for `GetElem?.match_1`.
const GET_ELEM_MATCH_1_EQ_1: &str = "_private.Init.Data.Array.Basic.0.GetElem?.match_1.eq_1";
/// The pin's private array stores this theorem in the Basic module.
const GET_ELEM_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Array/Basic";
/// The second generated equation theorem for `GetElem?.match_1`.
const GET_ELEM_MATCH_1_EQ_2: &str = "_private.Init.Data.Array.Basic.0.GetElem?.match_1.eq_2";
/// The pin's private array stores this theorem in the Basic module.
const GET_ELEM_MATCH_1_EQ_2_MODULE: &str = "Init/Data/Array/Basic";
/// The generated splitter definition for `GetElem?.match_1`.
const GET_ELEM_MATCH_1_SPLITTER: &str =
    "_private.Init.Data.Array.Basic.0.GetElem?.match_1.splitter";
/// The pin's private array stores this definition in the Basic module.
const GET_ELEM_MATCH_1_SPLITTER_MODULE: &str = "Init/Data/Array/Basic";
/// The private simp theorem relating `List.mem_toArray`.
const LIST_MEM_TO_ARRAY_SIMP_1_1: &str =
    "_private.Init.Data.Array.Basic.0.List.mem_toArray._simp_1_1";
/// The census stores this theorem in Array/Basic's private companion.
const LIST_MEM_TO_ARRAY_SIMP_1_1_MODULE: &str = "Init/Data/Array/Basic";
/// The second private equation theorem for `List.toArrayAux` in Array/Basic.
const LIST_TO_ARRAY_AUX_BASIC_EQ_2: &str =
    "_private.Init.Data.Array.Basic.0.List.toArrayAux.eq_2";
/// The census stores this theorem in Array/Basic's private companion.
const LIST_TO_ARRAY_AUX_BASIC_EQ_2_MODULE: &str = "Init/Data/Array/Basic";
/// The private defining equation theorem for `List.toArrayAux` in Array/Basic.
const LIST_TO_ARRAY_AUX_BASIC_EQ_DEF: &str =
    "_private.Init.Data.Array.Basic.0.List.toArrayAux.eq_def";
/// The census stores this theorem in Array/Basic's private companion.
const LIST_TO_ARRAY_AUX_BASIC_EQ_DEF_MODULE: &str = "Init/Data/Array/Basic";
/// The private match equation theorem for `List.toArrayAux` in Array/Basic.
const LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_1: &str =
    "_private.Init.Data.Array.Basic.0.List.toArrayAux.match_1.eq_1";
/// The census stores this theorem in Array/Basic's private companion.
const LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Array/Basic";
/// The second private match equation theorem for `List.toArrayAux` in Array/Basic.
const LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_2: &str =
    "_private.Init.Data.Array.Basic.0.List.toArrayAux.match_1.eq_2";
/// The census stores this theorem in Array/Basic's private companion.
const LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_2_MODULE: &str = "Init/Data/Array/Basic";
/// The private match splitter definition for `List.toArrayAux` in Array/Basic.
const LIST_TO_ARRAY_AUX_BASIC_MATCH_1_SPLITTER: &str =
    "_private.Init.Data.Array.Basic.0.List.toArrayAux.match_1.splitter";
/// The census stores this definition in Array/Basic's private companion.
const LIST_TO_ARRAY_AUX_BASIC_MATCH_1_SPLITTER_MODULE: &str = "Init/Data/Array/Basic";
const ARRAY_MAP_M_GO_UNARY_PROOF_1: &str =
    "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary._proof_1";
const ARRAY_MAP_M_GO_UNARY_PROOF_1_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNARY_PROOF_2: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary._proof_2";
const ARRAY_MAP_M_GO_UNARY_PROOF_2_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNARY_PROOF_3: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary._proof_3";
const ARRAY_MAP_M_GO_UNARY_PROOF_3_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNARY_PROOF_4: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary._proof_4";
const ARRAY_MAP_M_GO_UNARY_PROOF_4_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNARY_PROOF_5: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary._proof_5";
const ARRAY_MAP_M_GO_UNARY_PROOF_5_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNARY_PROOF_6: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary._proof_6";
const ARRAY_MAP_M_GO_UNARY_PROOF_6_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNARY_PROOF_7: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary._proof_7";
const ARRAY_MAP_M_GO_UNARY_PROOF_7_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNARY_PROOF_8: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary._proof_8";
const ARRAY_MAP_M_GO_UNARY_PROOF_8_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNARY_EQ_DEF: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary.eq_def";
const ARRAY_MAP_M_GO_UNARY_EQ_DEF_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNSAFE_REC: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unsafe_rec";
const ARRAY_MAP_M_GO_UNSAFE_REC_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_EQ_DEF: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go.eq_def";
const ARRAY_MAP_M_GO_EQ_DEF_MODULE: &str = "Init/Data/Array/BasicAux";
const LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_6: &str = "_private.Init.Data.Array.BasicAux.0.List.of_toArrayAux_eq_toArrayAux.match_1_6";
const LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_6_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_PROOF_1: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._proof_1";
const ARRAY_MAP_M_GO_PROOF_1_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_PROOF_2: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._proof_2";
const ARRAY_MAP_M_GO_PROOF_2_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_MAP_M_GO_UNARY: &str = "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go._unary";
const ARRAY_MAP_M_GO_UNARY_MODULE: &str = "Init/Data/Array/BasicAux";
const MAP_MONO_M_IMP_GO: &str = "_private.Init.Data.Array.BasicAux.0.mapMonoMImp.go";
const MAP_MONO_M_IMP_GO_MODULE: &str = "Init/Data/Array/BasicAux";
const LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_2: &str = "_private.Init.Data.Array.BasicAux.0.List.toArrayAux.eq_2";
const LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_2_MODULE: &str = "Init/Data/Array/BasicAux";
const LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_DEF: &str = "_private.Init.Data.Array.BasicAux.0.List.toArrayAux.eq_def";
const LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_DEF_MODULE: &str = "Init/Data/Array/BasicAux";
const LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_1: &str = "_private.Init.Data.Array.BasicAux.0.List.toArrayAux.match_1.eq_1";
const LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Array/BasicAux";
const LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_2: &str = "_private.Init.Data.Array.BasicAux.0.List.toArrayAux.match_1.eq_2";
const LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_2_MODULE: &str = "Init/Data/Array/BasicAux";
const LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_SPLITTER: &str = "_private.Init.Data.Array.BasicAux.0.List.toArrayAux.match_1.splitter";
const LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_SPLITTER_MODULE: &str = "Init/Data/Array/BasicAux";
const PSIGMA_CASES_ON_ARG_PUSHER_BASIC_AUX: &str = "_private.Init.Data.Array.BasicAux.0.PSigma.casesOn._arg_pusher";
const PSIGMA_CASES_ON_ARG_PUSHER_BASIC_AUX_MODULE: &str = "Init/Data/Array/BasicAux";
const ARRAY_ALL_DIFF_AUX_EQ_DEF: &str = "_private.Init.Data.Array.Basic.0.Array.allDiffAux.eq_def";
const ARRAY_ALL_DIFF_AUX_EQ_DEF_MODULE: &str = "Init/Data/Array/Basic";
const ARRAY_FIND_FIN_IDX_EQ_1: &str = "_private.Init.Data.Array.Basic.0.Array.findFinIdx?.eq_1";
const ARRAY_FIND_FIN_IDX_EQ_1_MODULE: &str = "Init/Data/Array/Basic";
const ARRAY_FIND_FIN_IDX_LOOP_EQ_DEF: &str = "_private.Init.Data.Array.Basic.0.Array.findFinIdx?.loop.eq_def";
const ARRAY_FIND_FIN_IDX_LOOP_EQ_DEF_MODULE: &str = "Init/Data/Array/Basic";
const ARRAY_FIND_FIN_IDX_LOOP_PROOF_1: &str = "_private.Init.Data.Array.Basic.0.Array.findFinIdx?.loop._proof_1";
const ARRAY_FIND_FIN_IDX_LOOP_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
const ARRAY_FIND_FIN_IDX_LOOP_UNSAFE_REC: &str = "_private.Init.Data.Array.Basic.0.Array.findFinIdx?.loop._unsafe_rec";
const ARRAY_FIND_FIN_IDX_LOOP_UNSAFE_REC_MODULE: &str = "Init/Data/Array/Basic";
const ARRAY_FIND_SOME_REV_M_FIND: &str = "_private.Init.Data.Array.Basic.0.Array.findSomeRevM?.find";
const ARRAY_FIND_SOME_REV_M_FIND_MODULE: &str = "Init/Data/Array/Basic";
/// The private implementation backing `mapMonoMImp`.
const MAP_MONO_M_IMP: &str = "_private.Init.Data.Array.BasicAux.0.mapMonoMImp";
/// The pin's private array stores this definition in the BasicAux module.
const MAP_MONO_M_IMP_MODULE: &str = "Init/Data/Array/BasicAux";
/// The private UTF-8 decode success characterization theorem.
const BYTE_ARRAY_IS_SOME_UTF8_DECODE_GO_IFF: &str =
    "_private.Init.Data.String.Basic.0.ByteArray.isSome_utf8Decode?go_iff";
/// The pin's private string companion stores this theorem in the Basic module.
const BYTE_ARRAY_IS_SOME_UTF8_DECODE_GO_IFF_MODULE: &str = "Init/Data/String/Basic";
/// The first generated equation theorem for `ByteArray.utf8Decode?.go.match_1`.
const BYTE_ARRAY_UTF8_DECODE_GO_MATCH_1_EQ_1: &str =
    "_private.Init.Data.String.Basic.0.ByteArray.utf8Decode?.go.match_1.eq_1";
/// The pin's private string companion stores this theorem in the Basic module.
const BYTE_ARRAY_UTF8_DECODE_GO_MATCH_1_EQ_1_MODULE: &str = "Init/Data/String/Basic";
/// The first generated equation theorem for `String.Pos.Raw.get?.match_1`.
const STRING_POS_RAW_GET_MATCH_1_EQ_1: &str =
    "_private.Init.Data.String.Basic.0.String.Pos.Raw.get?.match_1.eq_1";
/// The pin's private string companion stores this theorem in the Basic module.
const STRING_POS_RAW_GET_MATCH_1_EQ_1_MODULE: &str = "Init/Data/String/Basic";
/// The private match implementation for the UTF-8 singleton append theorem.
const BYTE_ARRAY_IS_VALID_UTF8_SINGLETON_APPEND_MATCH_1_1: &str =
    "_private.Init.Data.String.Basic.0.ByteArray.isValidUTF8_utf8Encode_singleton_append_iff.match_1_1";
/// The pin's private string companion stores this definition in the Basic module.
const BYTE_ARRAY_IS_VALID_UTF8_SINGLETON_APPEND_MATCH_1_1_MODULE: &str =
    "Init/Data/String/Basic";
/// The private simp theorem characterizing a failed UTF-8 validation.
const BYTE_ARRAY_VALIDATE_UTF8_EQ_FALSE_IFF_SIMP_1_1: &str =
    "_private.Init.Data.String.Basic.0.ByteArray.validateUTF8_eq_false_iff._simp_1_1";
/// The pin's private string companion stores this theorem in the Basic module.
const BYTE_ARRAY_VALIDATE_UTF8_EQ_FALSE_IFF_SIMP_1_1_MODULE: &str = "Init/Data/String/Basic";
/// The private simp theorem for left-append string-position validity.
const STRING_POS_RAW_IS_VALID_APPEND_LEFT_SIMP_1_1: &str =
    "_private.Init.Data.String.Basic.0.String.Pos.Raw.IsValid.append_left._simp_1_1";
/// The pin's private string companion stores this theorem in the Basic module.
const STRING_POS_RAW_IS_VALID_APPEND_LEFT_SIMP_1_1_MODULE: &str = "Init/Data/String/Basic";
/// The private match implementation for `Nat.add_assoc`.
const NAT_ADD_ASSOC_MATCH_1_1: &str = "_private.Init.Data.Nat.Basic.0.Nat.add_assoc.match_1_1";
/// The pin's private natural-number companion stores this definition in Basic.
const NAT_ADD_ASSOC_MATCH_1_1_MODULE: &str = "Init/Data/Nat/Basic";
/// The private match implementation for `Nat.mul_assoc`.
const NAT_MUL_ASSOC_MATCH_1_1: &str = "_private.Init.Data.Nat.Basic.0.Nat.mul_assoc.match_1_1";
/// The pin's private natural-number companion stores this definition in Basic.
const NAT_MUL_ASSOC_MATCH_1_1_MODULE: &str = "Init/Data/Nat/Basic";
/// The first private equation theorem for `Nat.beq.match_1`.
const NAT_BEQ_MATCH_1_EQ_1: &str = "_private.Init.Data.Nat.Basic.0.Nat.beq.match_1.eq_1";
/// The pin's private natural-number companion stores this theorem in Basic.
const NAT_BEQ_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Nat/Basic";
/// The first private equation theorem for `Nat.repeat.match_1`.
const NAT_REPEAT_MATCH_1_EQ_1: &str = "_private.Init.Data.Nat.Basic.0.Nat.repeat.match_1.eq_1";
/// The pin's private natural-number companion stores this theorem in Basic.
const NAT_REPEAT_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Nat/Basic";
/// The private match implementation for `Int.zero_ne_one`.
const INT_ZERO_NE_ONE_MATCH_1_1: &str =
    "_private.Init.Data.Int.Basic.0.Int.zero_ne_one.match_1_1";
/// The pin's private integer companion stores this definition in Basic.
const INT_ZERO_NE_ONE_MATCH_1_1_MODULE: &str = "Init/Data/Int/Basic";
/// The private match implementation for `Int.not`.
const INT_NOT_MATCH_1: &str = "_private.Init.Data.Int.Bitwise.Basic.0.Int.not.match_1";
/// The pin's private integer-bitwise companion stores this definition in Basic.
const INT_NOT_MATCH_1_MODULE: &str = "Init/Data/Int/Bitwise/Basic";
/// The private match implementation for `Bool.exists_bool'`.
const BOOL_EXISTS_BOOL_MATCH_1_1: &str = "_private.Init.Data.Bool.0.Bool.exists_bool'.match_1_1";
/// The pin's private Boolean companion stores this definition in its module.
const BOOL_EXISTS_BOOL_MATCH_1_1_MODULE: &str = "Init/Data/Bool";
/// The private match implementation for `Option.map_id`.
const OPTION_MAP_ID_MATCH_1_1: &str =
    "_private.Init.Data.Option.Basic.0.Option.map_id.match_1_1";
/// The pin's private option companion stores this definition in Basic.
const OPTION_MAP_ID_MATCH_1_1_MODULE: &str = "Init/Data/Option/Basic";
/// The private simp theorem for `Prod.swap_inj`.
const PROD_SWAP_INJ_SIMP_1_1: &str = "_private.Init.Data.Prod.0.Prod.swap_inj._simp_1_1";
/// The pin's private product companion stores this theorem in its module.
const PROD_SWAP_INJ_SIMP_1_1_MODULE: &str = "Init/Data/Prod";
/// The private match implementation for `Sum.lex_inr_inl`.
const SUM_LEX_INR_INL_MATCH_1_1: &str =
    "_private.Init.Data.Sum.Basic.0.Sum.lex_inr_inl.match_1_1";
/// The pin's private sum companion stores this definition in Basic.
const SUM_LEX_INR_INL_MATCH_1_1_MODULE: &str = "Init/Data/Sum/Basic";
/// The private theorem defining the strict order on `Fin`.
const FIN_MLT: &str = "_private.Init.Data.Fin.Basic.0.Fin.mlt";
/// The pin's private finite-index companion stores this theorem in Basic.
const FIN_MLT_MODULE: &str = "Init/Data/Fin/Basic";
/// The private match implementation for `Char.isValidUInt32`.
const CHAR_IS_VALID_UINT32_MATCH_1_1: &str =
    "_private.Init.Data.Char.Basic.0.Char.isValidUInt32.match_1_1";
/// The pin's private character companion stores this definition in Basic.
const CHAR_IS_VALID_UINT32_MATCH_1_1_MODULE: &str = "Init/Data/Char/Basic";
/// The private simp theorem for `UInt16.and_le_left`.
const UINT16_AND_LE_LEFT_SIMP_1_1: &str =
    "_private.Init.Data.UInt.Bitwise.0.UInt16.and_le_left._simp_1_1";
/// The pin's private unsigned-integer companion stores this theorem in Bitwise.
const UINT16_AND_LE_LEFT_SIMP_1_1_MODULE: &str = "Init/Data/UInt/Bitwise";
/// The private proof theorem for `Float.ofBits`.
const FLOAT_OF_BITS_PROOF_1: &str = "_private.Init.Data.Float.0.Float.ofBits._proof_1";
/// The pin's private floating-point companion stores this theorem in its module.
const FLOAT_OF_BITS_PROOF_1_MODULE: &str = "Init/Data/Float";
/// The private simp theorem for `Rat.mul`.
const RAT_MUL_SIMP_1: &str = "_private.Init.Data.Rat.Basic.0.Rat.mul._simp_1";
/// The pin's private rational companion stores this theorem in Basic.
const RAT_MUL_SIMP_1_MODULE: &str = "Init/Data/Rat/Basic";
/// The private simp theorem for `ByteArray.fastAppend_eq`.
const BYTE_ARRAY_FAST_APPEND_EQ_SIMP_1_1: &str =
    "_private.Init.Data.ByteArray.Basic.0.ByteArray.fastAppend_eq._simp_1_1";
/// The pin's private byte-array companion stores this theorem in Basic.
const BYTE_ARRAY_FAST_APPEND_EQ_SIMP_1_1_MODULE: &str = "Init/Data/ByteArray/Basic";
/// The private simp theorem for `Dyadic.neg_add_cancel`.
const DYADIC_NEG_ADD_CANCEL_SIMP_1_1: &str =
    "_private.Init.Data.Dyadic.Basic.0.Dyadic.neg_add_cancel._simp_1_1";
/// The pin's private dyadic companion stores this theorem in Basic.
const DYADIC_NEG_ADD_CANCEL_SIMP_1_1_MODULE: &str = "Init/Data/Dyadic/Basic";
/// The private proof theorem for `BitVec.getMsb`.
const BIT_VEC_GET_MSB_PROOF_1: &str = "_private.Init.Data.BitVec.Basic.0.BitVec.getMsb._proof_1";
/// The pin's private bit-vector companion stores this theorem in Basic.
const BIT_VEC_GET_MSB_PROOF_1_MODULE: &str = "Init/Data/BitVec/Basic";
/// The private match implementation for `FlattenAllowability.shouldFlatten`.
const FORMAT_SHOULD_FLATTEN_MATCH_1: &str =
    "_private.Init.Data.Format.Basic.0.Std.Format.FlattenAllowability.shouldFlatten.match_1";
/// The pin's private formatting companion stores this definition in Basic.
const FORMAT_SHOULD_FLATTEN_MATCH_1_MODULE: &str = "Init/Data/Format/Basic";
/// The private match implementation for `Vector.elimAsArray`.
const VECTOR_ELIM_AS_ARRAY_MATCH_1: &str =
    "_private.Init.Data.Vector.Basic.0.Vector.elimAsArray.match_1";
/// The pin's private vector companion stores this definition in Basic.
const VECTOR_ELIM_AS_ARRAY_MATCH_1_MODULE: &str = "Init/Data/Vector/Basic";
/// The private match implementation for `Bool.forall_bool'`.
const BOOL_FORALL_BOOL_MATCH_1_1: &str = "_private.Init.Data.Bool.0.Bool.forall_bool'.match_1_1";
/// The pin's private Boolean companion stores this definition in its module.
const BOOL_FORALL_BOOL_MATCH_1_1_MODULE: &str = "Init/Data/Bool";
/// The private match implementation for `Option.some_get`.
const OPTION_SOME_GET_MATCH_1_1: &str =
    "_private.Init.Data.Option.Basic.0.Option.some_get.match_1_1";
/// The pin's private option companion stores this definition in Basic.
const OPTION_SOME_GET_MATCH_1_1_MODULE: &str = "Init/Data/Option/Basic";
/// The private match implementation for `Option.isNone_filter`.
const OPTION_IS_NONE_FILTER_MATCH_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isNone_filter.match_1_1";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_IS_NONE_FILTER_MATCH_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private first equation for `Option.isSome`.
const OPTION_IS_SOME_MATCH_1_EQ_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isSome.match_1.eq_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_IS_SOME_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private second equation for `Option.isSome`.
const OPTION_IS_SOME_MATCH_1_EQ_2: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isSome.match_1.eq_2";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_IS_SOME_MATCH_1_EQ_2_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private splitter for the `Option.isSome` match.
const OPTION_LEMMAS_IS_SOME_MATCH_1_SPLITTER: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isSome.match_1.splitter";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_LEMMAS_IS_SOME_MATCH_1_SPLITTER_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private match implementation for `Option.join_eq_none_iff`.
const OPTION_JOIN_EQ_NONE_IFF_MATCH_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.join_eq_none_iff.match_1_1";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_JOIN_EQ_NONE_IFF_MATCH_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simplifier theorem for `Option.join_eq_some_iff`.
const OPTION_JOIN_EQ_SOME_IFF_SIMP_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.join_eq_some_iff._simp_1_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_JOIN_EQ_SOME_IFF_SIMP_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The second private simplifier theorem for `Option.join_eq_some_iff`.
const OPTION_JOIN_EQ_SOME_IFF_SIMP_1_2: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.join_eq_some_iff._simp_1_2";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_JOIN_EQ_SOME_IFF_SIMP_1_2_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private match implementation for `Option.join_filter`.
const OPTION_JOIN_FILTER_MATCH_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.join_filter.match_1_1";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_JOIN_FILTER_MATCH_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simplifier theorem for `Option.join_ne_none`.
const OPTION_JOIN_NE_NONE_SIMP_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.join_ne_none._simp_1_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_JOIN_NE_NONE_SIMP_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simplifier theorem for `Option.mem_toArray`.
const OPTION_MEM_TO_ARRAY_SIMP_1_1: &str =
    "_private.Init.Data.Option.Array.0.Option.mem_toArray._simp_1_1";
/// The pin's private option companion stores this theorem in Array.
const OPTION_MEM_TO_ARRAY_SIMP_1_1_MODULE: &str = "Init/Data/Option/Array";
/// The private simplifier theorem for `Option.toArray_join`.
const OPTION_TO_ARRAY_JOIN_SIMP_1_1: &str =
    "_private.Init.Data.Option.Array.0.Option.toArray_join._simp_1_1";
/// The pin's private option companion stores this theorem in Array.
const OPTION_TO_ARRAY_JOIN_SIMP_1_1_MODULE: &str = "Init/Data/Option/Array";
/// The private match implementation for `Option.attach_eq_some`.
const OPTION_ATTACH_EQ_SOME_MATCH_1_1: &str =
    "_private.Init.Data.Option.Attach.0.Option.attach_eq_some.match_1_1";
/// The pin's private option companion stores this definition in Attach.
const OPTION_ATTACH_EQ_SOME_MATCH_1_1_MODULE: &str = "Init/Data/Option/Attach";
/// The private match implementation for `Option.unattach_eq_some_iff`.
const OPTION_UNATTACH_EQ_SOME_IFF_MATCH_1_1: &str =
    "_private.Init.Data.Option.Attach.0.Option.unattach_eq_some_iff.match_1_1";
/// The pin's private option companion stores this definition in Attach.
const OPTION_UNATTACH_EQ_SOME_IFF_MATCH_1_1_MODULE: &str = "Init/Data/Option/Attach";
/// The private simplifier theorem for `Option.attach_filter`.
const OPTION_ATTACH_FILTER_SIMP_1_1: &str =
    "_private.Init.Data.Option.Attach.0.Option.attach_filter._simp_1_1";
/// The pin's private option companion stores this theorem in Attach.
const OPTION_ATTACH_FILTER_SIMP_1_1_MODULE: &str = "Init/Data/Option/Attach";
/// The second private simplifier theorem for `Option.attach_filter`.
const OPTION_ATTACH_FILTER_SIMP_1_2: &str =
    "_private.Init.Data.Option.Attach.0.Option.attach_filter._simp_1_2";
/// The pin's private option companion stores this theorem in Attach.
const OPTION_ATTACH_FILTER_SIMP_1_2_MODULE: &str = "Init/Data/Option/Attach";
/// The private simplifier theorem for `Option.attach_pfilter`.
const OPTION_ATTACH_PFILTER_SIMP_2: &str =
    "_private.Init.Data.Option.Attach.0.Option.attach_pfilter._simp_2";
/// The pin's private option companion stores this theorem in Attach.
const OPTION_ATTACH_PFILTER_SIMP_2_MODULE: &str = "Init/Data/Option/Attach";
/// The private first equation for `Option.instDecidableEq`.
const OPTION_DECIDABLE_EQ_MATCH_1_EQ_1: &str =
    "_private.Init.Data.Option.Attach.0.Option.instDecidableEq.match_1.eq_1";
/// The pin's private option companion stores this theorem in Attach.
const OPTION_DECIDABLE_EQ_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Option/Attach";
/// The private second equation for `Option.instDecidableEq`.
const OPTION_DECIDABLE_EQ_MATCH_1_EQ_2: &str =
    "_private.Init.Data.Option.Attach.0.Option.instDecidableEq.match_1.eq_2";
/// The pin's private option companion stores this theorem in Attach.
const OPTION_DECIDABLE_EQ_MATCH_1_EQ_2_MODULE: &str = "Init/Data/Option/Attach";
/// The private splitter for the `Option.instDecidableEq` match.
const OPTION_ATTACH_DECIDABLE_EQ_MATCH_1_SPLITTER: &str =
    "_private.Init.Data.Option.Attach.0.Option.instDecidableEq.match_1.splitter";
/// The pin's private option companion stores this definition in Attach.
const OPTION_ATTACH_DECIDABLE_EQ_MATCH_1_SPLITTER_MODULE: &str = "Init/Data/Option/Attach";
/// The private simplifier theorem for `Option.instLawfulMonadAttach`.
const OPTION_LAWFUL_MONAD_ATTACH_SIMP_1: &str =
    "_private.Init.Data.Option.Attach.0.Option.instLawfulMonadAttach._simp_1";
/// The pin's private option companion stores this theorem in Attach.
const OPTION_LAWFUL_MONAD_ATTACH_SIMP_1_MODULE: &str = "Init/Data/Option/Attach";
/// The second private simplifier theorem for `Option.instLawfulMonadAttach`.
const OPTION_LAWFUL_MONAD_ATTACH_SIMP_2: &str =
    "_private.Init.Data.Option.Attach.0.Option.instLawfulMonadAttach._simp_2";
/// The pin's private option companion stores this theorem in Attach.
const OPTION_LAWFUL_MONAD_ATTACH_SIMP_2_MODULE: &str = "Init/Data/Option/Attach";
/// The private simplifier theorem for `Option.isNone_choice_eq_false`.
const OPTION_IS_NONE_CHOICE_EQ_FALSE_SIMP_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isNone_choice_eq_false._simp_1_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_IS_NONE_CHOICE_EQ_FALSE_SIMP_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simplifier theorem for `Option.isNone_merge`.
const OPTION_IS_NONE_MERGE_SIMP_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isNone_merge._simp_1_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_IS_NONE_MERGE_SIMP_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simplifier theorem for `Option.isNone_pfilter_iff`.
const OPTION_IS_NONE_PFILTER_IFF_SIMP_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isNone_pfilter_iff._simp_1_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_IS_NONE_PFILTER_IFF_SIMP_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The second private simplifier theorem for `Option.isNone_pfilter_iff`.
const OPTION_IS_NONE_PFILTER_IFF_SIMP_1_2: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isNone_pfilter_iff._simp_1_2";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_IS_NONE_PFILTER_IFF_SIMP_1_2_MODULE: &str = "Init/Data/Option/Lemmas";
/// The third private simplifier theorem for `Option.isNone_pfilter_iff`.
const OPTION_IS_NONE_PFILTER_IFF_SIMP_1_3: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isNone_pfilter_iff._simp_1_3";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_IS_NONE_PFILTER_IFF_SIMP_1_3_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simplifier theorem for `Option.isSome_merge`.
const OPTION_IS_SOME_MERGE_SIMP_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isSome_merge._simp_1_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_IS_SOME_MERGE_SIMP_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private match implementation for `Option.isSome_filter`.
const OPTION_IS_SOME_FILTER_MATCH_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isSome_filter.match_1_1";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_IS_SOME_FILTER_MATCH_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private third match implementation for `Option.isSome_filter`.
const OPTION_IS_SOME_FILTER_MATCH_1_3: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.isSome_filter.match_1_3";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_IS_SOME_FILTER_MATCH_1_3_MODULE: &str = "Init/Data/Option/Lemmas";
/// The second private simplifier theorem for `Option.join_ne_none`.
const OPTION_JOIN_NE_NONE_SIMP_1_2: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.join_ne_none._simp_1_2";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_JOIN_NE_NONE_SIMP_1_2_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private first equation for `Option.le`.
const OPTION_LE_MATCH_1_EQ_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.le.match_1.eq_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_LE_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private second equation for `Option.le`.
const OPTION_LE_MATCH_1_EQ_2: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.le.match_1.eq_2";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_LE_MATCH_1_EQ_2_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private splitter for the `Option.le` match.
const OPTION_LE_MATCH_1_SPLITTER: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.le.match_1.splitter";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_LE_MATCH_1_SPLITTER_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private first equation for `Option.pmap`.
const OPTION_PMAP_MATCH_1_EQ_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pmap.match_1.eq_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_PMAP_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private second equation for `Option.pmap`.
const OPTION_PMAP_MATCH_1_EQ_2: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pmap.match_1.eq_2";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_PMAP_MATCH_1_EQ_2_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private splitter for the `Option.pmap` match.
const OPTION_PMAP_MATCH_1_SPLITTER: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pmap.match_1.splitter";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_PMAP_MATCH_1_SPLITTER_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simplifier theorem for `Option.pmap_eq_some_iff`.
const OPTION_PMAP_EQ_SOME_IFF_SIMP_1_4: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pmap_eq_some_iff._simp_1_4";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_PMAP_EQ_SOME_IFF_SIMP_1_4_MODULE: &str = "Init/Data/Option/Lemmas";
/// The second private simplifier theorem for `Option.pmap_eq_some_iff`.
const OPTION_PMAP_EQ_SOME_IFF_SIMP_1_5: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pmap_eq_some_iff._simp_1_5";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_PMAP_EQ_SOME_IFF_SIMP_1_5_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private first equation for `Option.pfilter`.
const OPTION_PFILTER_MATCH_1_EQ_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pfilter.match_1.eq_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_PFILTER_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private second equation for `Option.pfilter`.
const OPTION_PFILTER_MATCH_1_EQ_2: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pfilter.match_1.eq_2";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_PFILTER_MATCH_1_EQ_2_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private splitter for the `Option.pfilter` match.
const OPTION_PFILTER_MATCH_1_SPLITTER: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pfilter.match_1.splitter";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_PFILTER_MATCH_1_SPLITTER_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simplifier theorem for `Option.pfilter_eq_some_iff`.
const OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pfilter_eq_some_iff._simp_1_1";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The second private simplifier theorem for `Option.pfilter_eq_some_iff`.
const OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_2: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pfilter_eq_some_iff._simp_1_2";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_2_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simplifier theorem for `Option.pmap_eq_some_iff`.
const OPTION_PMAP_EQ_SOME_IFF_SIMP_1_6: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.pmap_eq_some_iff._simp_1_6";
/// The pin's private option companion stores this theorem in Lemmas.
const OPTION_PMAP_EQ_SOME_IFF_SIMP_1_6_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private match implementation for `Option.rel_some_some`.
const OPTION_REL_SOME_SOME_MATCH_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.rel_some_some.match_1_1";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_REL_SOME_SOME_MATCH_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private match implementation for `Option.some_get!`.
const OPTION_SOME_GET_BANG_MATCH_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.some_get!.match_1_1";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_SOME_GET_BANG_MATCH_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private match implementation for `Option.some_ne_none`.
const OPTION_SOME_NE_NONE_MATCH_1_1: &str =
    "_private.Init.Data.Option.Lemmas.0.Option.some_ne_none.match_1_1";
/// The pin's private option companion stores this definition in Lemmas.
const OPTION_SOME_NE_NONE_MATCH_1_1_MODULE: &str = "Init/Data/Option/Lemmas";
/// The private simp theorem relating `Option.mem_toList`.
const OPTION_MEM_TO_LIST_SIMP_1_1: &str =
    "_private.Init.Data.Option.List.0.Option.mem_toList._simp_1_1";
/// The census places the theorem in Option/List's private companion.
const OPTION_MEM_TO_LIST_SIMP_1_1_MODULE: &str = "Init/Data/Option/List";
/// The private match implementation for `Option.toList_filter`.
const OPTION_TO_LIST_FILTER_MATCH_1_1: &str =
    "_private.Init.Data.Option.List.0.Option.toList_filter.match_1_1";
/// The census places the implementation in Option/List's private companion.
const OPTION_TO_LIST_FILTER_MATCH_1_1_MODULE: &str = "Init/Data/Option/List";
/// The second private match implementation for `Option.toList_filter`.
const OPTION_TO_LIST_FILTER_MATCH_1_3: &str =
    "_private.Init.Data.Option.List.0.Option.toList_filter.match_1_3";
/// The census places the implementation in Option/List's private companion.
const OPTION_TO_LIST_FILTER_MATCH_1_3_MODULE: &str = "Init/Data/Option/List";
/// The private simp theorem relating `Option.toList_join`.
const OPTION_TO_LIST_JOIN_SIMP_1_1: &str =
    "_private.Init.Data.Option.List.0.Option.toList_join._simp_1_1";
/// The census places the theorem in Option/List's private companion.
const OPTION_TO_LIST_JOIN_SIMP_1_1_MODULE: &str = "Init/Data/Option/List";
/// The private equation theorem for Option's inferred membership `forIn` instance.
const OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_1: &str =
    "_private.Init.Data.Option.Monadic.0.Option.instForIn'InferInstanceMembershipOfMonad.match_1.eq_1";
/// The census stores the theorem in Option/Monadic's private companion.
const OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_1_MODULE: &str = "Init/Data/Option/Monadic";
/// The second private equation theorem for Option's inferred membership `forIn` instance.
const OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_2: &str =
    "_private.Init.Data.Option.Monadic.0.Option.instForIn'InferInstanceMembershipOfMonad.match_1.eq_2";
/// The census stores the theorem in Option/Monadic's private companion.
const OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_2_MODULE: &str = "Init/Data/Option/Monadic";
/// The private stored definition implementing `List.hasDecEq`.
const LIST_HAS_DEC_EQ: &str = "List.hasDecEq";
/// The census places the implementation in Prelude's private companion.
const LIST_HAS_DEC_EQ_MODULE: &str = "Init/Prelude";
/// The third private match helper for `List.hasDecEq`.
const LIST_HAS_DEC_EQ_MATCH_3: &str = "List.hasDecEq.match_3";
/// The census places this equation helper in Prelude's private companion.
const LIST_HAS_DEC_EQ_MATCH_3_MODULE: &str = "Init/Prelude";
/// The first private match helper for `List.hasDecEq`.
const LIST_HAS_DEC_EQ_MATCH_1: &str = "List.hasDecEq.match_1";
/// The census places this equation helper in Prelude's private companion.
const LIST_HAS_DEC_EQ_MATCH_1_MODULE: &str = "Init/Prelude";
/// The first private proof helper for `List.hasDecEq`.
const LIST_HAS_DEC_EQ_PROOF_1: &str = "List.hasDecEq._proof_1";
/// The census places this theorem in Prelude's private companion.
const LIST_HAS_DEC_EQ_PROOF_1_MODULE: &str = "Init/Prelude";
/// The fifth private match helper for `List.hasDecEq`.
const LIST_HAS_DEC_EQ_MATCH_5: &str = "List.hasDecEq.match_5";
/// The census places this equation helper in Prelude's private companion.
const LIST_HAS_DEC_EQ_MATCH_5_MODULE: &str = "Init/Prelude";
/// A private equation-compiler match helper used by Prelude's name equality.
const NAME_BEQ_MATCH_1: &str = "_private.Init.Prelude.0.Lean.Name.beq.match_1";
/// The direct Syntax match helpers required by the public partial functions.
const SYNTAX_MATCH_AUXILIARIES: [&str; 2] = [
    "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
    "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
];
/// `_private.`-mangled helpers that the `Init.Data.String.Extra` exported part
/// intentionally declares itself.
const STRING_EXTRA_EXPORTED_UNSAFE_RECS: [&str; 2] = [
    "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
    "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
];
/// The analogous exported-mangled helpers for `removeNumLeadingSpaces`.
const STRING_REMOVE_LEADING_SPACES_EXPORTED_UNSAFE_RECS: [&str; 2] = [
    "_private.Init.Data.String.Extra.0.String.removeNumLeadingSpaces.consumeSpaces._unsafe_rec",
    "_private.Init.Data.String.Extra.0.String.removeNumLeadingSpaces.saveLine._unsafe_rec",
];
/// A private unary helper nested under Prelude's syntax insertion loop.
/// The pin's only `insertIdx.loop._unary`, and it is not in `Init.Prelude`.
///
/// A corpus-wide search finds exactly ONE declaration with this suffix, in
/// `Init.Data.Array.Basic`, where it is private-only and decodes as a
/// definition. `Init.Prelude` declares nothing of the sort — zero matches in
/// its constants and zero in its extraConstNames, chain included — so the
/// module this cell reads has to be the one that owns the declaration.
const INSERT_IDX_LOOP_UNARY: &str = "_private.Init.Data.Array.Basic.0.Array.insertIdx.loop._unary";
/// The module that actually declares it.
const INSERT_IDX_LOOP_UNARY_MODULE: &str = "Init/Data/Array/Basic";
/// The first generated proof theorem for `Array.insertIdx.loop._unary`.
const INSERT_IDX_LOOP_UNARY_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.insertIdx.loop._unary._proof_1";
/// The pin's private array stores this theorem in the basic module.
const INSERT_IDX_LOOP_UNARY_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The first generated proof theorem for `Array.insertIdx.loop`.
const INSERT_IDX_LOOP_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.insertIdx.loop._proof_1";
/// The pin's private array stores this theorem in the basic module.
const INSERT_IDX_LOOP_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The second generated proof theorem for `Array.insertIdx.loop`.
const INSERT_IDX_LOOP_PROOF_2: &str =
    "_private.Init.Data.Array.Basic.0.Array.insertIdx.loop._proof_2";
/// The pin's private array stores this theorem in the basic module.
const INSERT_IDX_LOOP_PROOF_2_MODULE: &str = "Init/Data/Array/Basic";
/// The third generated proof theorem for `Array.insertIdx.loop`.
const INSERT_IDX_LOOP_PROOF_3: &str =
    "_private.Init.Data.Array.Basic.0.Array.insertIdx.loop._proof_3";
/// The pin's private array stores this theorem in the basic module.
const INSERT_IDX_LOOP_PROOF_3_MODULE: &str = "Init/Data/Array/Basic";
/// The exported shell name for `Array.zipWithMAux`'s unary compiler helper.
const ARRAY_ZIP_WITH_M_AUX_UNARY: &str = "Array.zipWithMAux._unary";
/// The generated proof theorem for `Array.zipWithMAux._unary`.
const ARRAY_ZIP_WITH_M_AUX_UNARY_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.zipWithMAux._unary._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ZIP_WITH_M_AUX_UNARY_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The equation theorem for `Array.zipWithMAux._unary`.
const ARRAY_ZIP_WITH_M_AUX_UNARY_EQ_DEF: &str =
    "_private.Init.Data.Array.Basic.0.Array.zipWithMAux._unary.eq_def";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ZIP_WITH_M_AUX_UNARY_EQ_DEF_MODULE: &str = "Init/Data/Array/Basic";
/// The exact private proof generated for the unary wrapper of `Nat.gcd`.
///
/// The pin census records this theorem under `Init.Data.Nat.Gcd`; its private
/// companion owns the declaration rather than the exported interface.
const NAT_GCD_UNARY_PROOF_1: &str =
    "_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary._proof_1";
/// A generated theorem whose privacy prefix names `Array.Basic`, while the
/// pin's private array stores it in the module that generated the simp lemma.
const ARRAY_OF_FN_GO_CONGR_SIMP: &str =
    "_private.Init.Data.Array.Basic.0.Array.ofFn.go.congr_simp";
/// The actual storage module from the pin's private constant array.
const ARRAY_OF_FN_GO_CONGR_SIMP_MODULE: &str = "Init/Data/Array/Lemmas";
/// The exact private simp theorem generated by `Array.foldl_attach`.
const ARRAY_FOLDL_ATTACH_SIMP_1_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.foldl_attach._simp_1_1";
/// The module whose private array owns the generated simp theorem at the pin.
const ARRAY_FOLDL_ATTACH_SIMP_1_1_MODULE: &str = "Init/Data/Array/Attach";
/// The distinct generated simp theorem for `Array.foldr_attach`.
const ARRAY_FOLDR_ATTACH_SIMP_1_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.foldr_attach._simp_1_1";
/// The pin's private array stores this sibling theorem in the attach module.
const ARRAY_FOLDR_ATTACH_SIMP_1_1_MODULE: &str = "Init/Data/Array/Attach";
/// The generated match definition for `Array.mem_attach`.
const ARRAY_MEM_ATTACH_MATCH_1_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.mem_attach.match_1_1";
/// The pin's private array stores this match helper in the attach module.
const ARRAY_MEM_ATTACH_MATCH_1_1_MODULE: &str = "Init/Data/Array/Attach";
/// The generated match definition for `Array.pmapImpl`.
const ARRAY_PMAP_IMPL_MATCH_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.pmapImpl.match_1";
/// The pin's private array stores this match helper in the attach module.
const ARRAY_PMAP_IMPL_MATCH_1_MODULE: &str = "Init/Data/Array/Attach";
/// The generated simp theorem for `Array.pmap_congr_left`.
const ARRAY_PMAP_CONGR_LEFT_SIMP_1_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.pmap_congr_left._simp_1_1";
/// The pin's private array stores this simp theorem in the attach module.
const ARRAY_PMAP_CONGR_LEFT_SIMP_1_1_MODULE: &str = "Init/Data/Array/Attach";
/// The generated simp theorem for `Array.pmap_eq_self`.
const ARRAY_PMAP_EQ_SELF_SIMP_1_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.pmap_eq_self._simp_1_1";
/// The pin's private array stores this simp theorem in the attach module.
const ARRAY_PMAP_EQ_SELF_SIMP_1_1_MODULE: &str = "Init/Data/Array/Attach";
/// The generated simp theorem for `Array.pmap_push`.
const ARRAY_PMAP_PUSH_SIMP_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.pmap_push._simp_1";
/// The pin's private array stores this simp theorem in the attach module.
const ARRAY_PMAP_PUSH_SIMP_1_MODULE: &str = "Init/Data/Array/Attach";
/// The generated simp theorem for `Array.toList_attachWith`.
const ARRAY_TO_LIST_ATTACH_WITH_SIMP_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.toList_attachWith._simp_1";
/// The pin's private array stores this simp theorem in the attach module.
const ARRAY_TO_LIST_ATTACH_WITH_SIMP_1_MODULE: &str = "Init/Data/Array/Attach";
/// The generated simp theorem for `Array.mem_unattach`.
const ARRAY_MEM_UNATTACH_SIMP_1_2: &str =
    "_private.Init.Data.Array.Attach.0.Array.mem_unattach._simp_1_2";
/// The pin's private array stores this simp theorem in the attach module.
const ARRAY_MEM_UNATTACH_SIMP_1_2_MODULE: &str = "Init/Data/Array/Attach";
/// The first generated simp theorem for `Array.mem_pmap`.
const ARRAY_MEM_PMAP_SIMP_1_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.mem_pmap._simp_1_1";
/// The pin's private array stores this simp theorem in the attach module.
const ARRAY_MEM_PMAP_SIMP_1_1_MODULE: &str = "Init/Data/Array/Attach";
/// The second generated simp theorem for `Array.mem_pmap`.
const ARRAY_MEM_PMAP_SIMP_1_2: &str =
    "_private.Init.Data.Array.Attach.0.Array.mem_pmap._simp_1_2";
/// The pin's private array stores this simp theorem in the attach module.
const ARRAY_MEM_PMAP_SIMP_1_2_MODULE: &str = "Init/Data/Array/Attach";
/// The third generated simp theorem for `Array.mem_pmap`.
const ARRAY_MEM_PMAP_SIMP_1_3: &str =
    "_private.Init.Data.Array.Attach.0.Array.mem_pmap._simp_1_3";
/// The pin's private array stores this simp theorem in the attach module.
const ARRAY_MEM_PMAP_SIMP_1_3_MODULE: &str = "Init/Data/Array/Attach";
/// The private implementation definition behind `Array.attachWith`.
const ARRAY_ATTACH_WITH_IMPL: &str =
    "_private.Init.Data.Array.Attach.0.Array.attachWithImpl";
/// The pin's private array stores this implementation in the attach module.
const ARRAY_ATTACH_WITH_IMPL_MODULE: &str = "Init/Data/Array/Attach";
/// The private equation theorem generated for `Array.unattach`.
const ARRAY_UNATTACH_EQ_1: &str =
    "_private.Init.Data.Array.Attach.0.Array.unattach.eq_1";
/// The pin's private array stores this theorem in the attach module.
const ARRAY_UNATTACH_EQ_1_MODULE: &str = "Init/Data/Array/Attach";
/// The private implementation definition for `Array.allDiffAux`.
const ARRAY_ALL_DIFF_AUX: &str =
    "_private.Init.Data.Array.Basic.0.Array.allDiffAux";
/// The pin's private array stores this implementation in the basic module.
const ARRAY_ALL_DIFF_AUX_MODULE: &str = "Init/Data/Array/Basic";
/// The generated proof theorem for `Array.allDiffAux`.
const ARRAY_ALL_DIFF_AUX_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.allDiffAux._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ALL_DIFF_AUX_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unsafe recursion helper for `Array.allDiffAux`.
const ARRAY_ALL_DIFF_AUX_UNSAFE_REC: &str =
    "_private.Init.Data.Array.Basic.0.Array.allDiffAux._unsafe_rec";
/// The pin's private array stores this helper in the basic module.
const ARRAY_ALL_DIFF_AUX_UNSAFE_REC_MODULE: &str = "Init/Data/Array/Basic";
/// The private monadic scan implementation behind `Array.anyMUnsafe`.
const ARRAY_ANY_M_UNSAFE_ANY: &str =
    "_private.Init.Data.Array.Basic.0.Array.anyMUnsafe.any";
/// The pin's private array stores this implementation in the basic module.
const ARRAY_ANY_M_UNSAFE_ANY_MODULE: &str = "Init/Data/Array/Basic";
/// The generated proof theorem for `Array.back`.
const ARRAY_BACK_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.back._proof_1";
/// The pin's private array stores this proof in the basic module.
const ARRAY_BACK_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated proof theorem for `Array.erase`.
const ARRAY_ERASE_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.erase._proof_1";
/// The pin's private array stores this proof in the basic module.
const ARRAY_ERASE_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.erase`.
const ARRAY_ERASE_MATCH_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.erase.match_1";
/// The pin's private array stores this match helper in the basic module.
const ARRAY_ERASE_MATCH_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated proof theorem for `Array.eraseIdx`.
const ARRAY_ERASE_IDX_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.eraseIdx._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ERASE_IDX_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The unary generated proof theorem for `Array.eraseIdx`.
const ARRAY_ERASE_IDX_UNARY_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.eraseIdx._unary._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ERASE_IDX_UNARY_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The second unary generated proof theorem for `Array.eraseIdx`.
const ARRAY_ERASE_IDX_UNARY_PROOF_2: &str =
    "_private.Init.Data.Array.Basic.0.Array.eraseIdx._unary._proof_2";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ERASE_IDX_UNARY_PROOF_2_MODULE: &str = "Init/Data/Array/Basic";
/// The third unary generated proof theorem for `Array.eraseIdx`.
const ARRAY_ERASE_IDX_UNARY_PROOF_3: &str =
    "_private.Init.Data.Array.Basic.0.Array.eraseIdx._unary._proof_3";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ERASE_IDX_UNARY_PROOF_3_MODULE: &str = "Init/Data/Array/Basic";
/// The fourth unary generated proof theorem for `Array.eraseIdx`.
const ARRAY_ERASE_IDX_UNARY_PROOF_4: &str =
    "_private.Init.Data.Array.Basic.0.Array.eraseIdx._unary._proof_4";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ERASE_IDX_UNARY_PROOF_4_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.eraseReps`.
const ARRAY_ERASE_REPS_MATCH_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.eraseReps.match_1";
/// The pin's private array stores this match helper in the basic module.
const ARRAY_ERASE_REPS_MATCH_1_MODULE: &str = "Init/Data/Array/Basic";
/// The private extensionality theorem generated for arrays.
const ARRAY_EXT_AUX: &str =
    "_private.Init.Data.Array.Basic.0.Array.ext.extAux";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_EXT_AUX_MODULE: &str = "Init/Data/Array/Basic";
/// The private search loop generated for `Array.findFinIdx?`.
const ARRAY_FIND_FIN_IDX_LOOP: &str =
    "_private.Init.Data.Array.Basic.0.Array.findFinIdx?.loop";
/// The pin's private array stores this loop in the basic module.
const ARRAY_FIND_FIN_IDX_LOOP_MODULE: &str = "Init/Data/Array/Basic";
/// The private theorem relating `findIdx?` to `findFinIdx?`'s loop.
const ARRAY_FIND_IDX_LOOP_EQ_MAP_FIND_FIN_IDX_LOOP_VAL: &str =
    "_private.Init.Data.Array.Basic.0.Array.findIdx?_loop_eq_map_findFinIdx?_loop_val";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_FIND_IDX_LOOP_EQ_MAP_FIND_FIN_IDX_LOOP_VAL_MODULE: &str = "Init/Data/Array/Basic";
/// The private fixpoint helper generated for `Array.findSomeRevM?`.
const ARRAY_FIND_SOME_REV_M_FIND_F: &str =
    "_private.Init.Data.Array.Basic.0.Array.findSomeRevM?.find._f";
/// The pin's private array stores this helper in the basic module.
const ARRAY_FIND_SOME_REV_M_FIND_F_MODULE: &str = "Init/Data/Array/Basic";
/// The private recursion helper generated for `Array.firstM`.
const ARRAY_FIRST_M_GO: &str =
    "_private.Init.Data.Array.Basic.0.Array.firstM.go";
/// The pin's private array stores this helper in the basic module.
const ARRAY_FIRST_M_GO_MODULE: &str = "Init/Data/Array/Basic";
/// The private monadic left-fold implementation helper.
const ARRAY_FOLDL_M_UNSAFE_FOLD: &str =
    "_private.Init.Data.Array.Basic.0.Array.foldlMUnsafe.fold";
/// The pin's private array stores this helper in the basic module.
const ARRAY_FOLDL_M_UNSAFE_FOLD_MODULE: &str = "Init/Data/Array/Basic";
/// The private monadic right-fold implementation helper.
const ARRAY_FOLDR_M_UNSAFE_FOLD: &str =
    "_private.Init.Data.Array.Basic.0.Array.foldrMUnsafe.fold";
/// The pin's private array stores this helper in the basic module.
const ARRAY_FOLDR_M_UNSAFE_FOLD_MODULE: &str = "Init/Data/Array/Basic";
/// The private iterator loop generated for `Array.forIn'Unsafe`.
const ARRAY_FOR_IN_UNSAFE_LOOP: &str =
    "_private.Init.Data.Array.Basic.0.Array.forIn'Unsafe.loop";
/// The pin's private array stores this loop in the basic module.
const ARRAY_FOR_IN_UNSAFE_LOOP_MODULE: &str = "Init/Data/Array/Basic";
/// The private monadic map implementation helper.
const ARRAY_MAP_M_UNSAFE_MAP: &str =
    "_private.Init.Data.Array.Basic.0.Array.mapMUnsafe.map";
/// The pin's private array stores this helper in the basic module.
const ARRAY_MAP_M_UNSAFE_MAP_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.getEvenElems`.
const ARRAY_GET_EVEN_ELEMS_MATCH_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.getEvenElems.match_1";
/// The pin's private array stores this helper in the basic module.
const ARRAY_GET_EVEN_ELEMS_MATCH_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated proof theorem for `Array.idxOfAux`.
const ARRAY_IDX_OF_AUX_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.idxOfAux._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_IDX_OF_AUX_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.isEqvAux`.
const ARRAY_IS_EQV_AUX_MATCH_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.isEqvAux.match_1";
/// The pin's private array stores this helper in the basic module.
const ARRAY_IS_EQV_AUX_MATCH_1_MODULE: &str = "Init/Data/Array/Basic";
/// The first generated proof theorem for `Array.isEqvAux`.
const ARRAY_IS_EQV_AUX_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.isEqvAux._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_IS_EQV_AUX_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The second generated proof theorem for `Array.isEqvAux`.
const ARRAY_IS_EQV_AUX_PROOF_2: &str =
    "_private.Init.Data.Array.Basic.0.Array.isEqvAux._proof_2";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_IS_EQV_AUX_PROOF_2_MODULE: &str = "Init/Data/Array/Basic";
/// The generated proof theorem for `Array.isEqv`.
const ARRAY_IS_EQV_PROOF_1: &str = "_private.Init.Data.Array.Basic.0.Array.isEqv._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_IS_EQV_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The first generated proof theorem for `Array.isPrefixOfAux`.
const ARRAY_IS_PREFIX_OF_AUX_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.isPrefixOfAux._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_IS_PREFIX_OF_AUX_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The second generated proof theorem for `Array.isPrefixOfAux`.
const ARRAY_IS_PREFIX_OF_AUX_PROOF_2: &str =
    "_private.Init.Data.Array.Basic.0.Array.isPrefixOfAux._proof_2";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_IS_PREFIX_OF_AUX_PROOF_2_MODULE: &str = "Init/Data/Array/Basic";
/// The third generated proof theorem for `Array.isPrefixOfAux`.
const ARRAY_IS_PREFIX_OF_AUX_PROOF_3: &str =
    "_private.Init.Data.Array.Basic.0.Array.isPrefixOfAux._proof_3";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_IS_PREFIX_OF_AUX_PROOF_3_MODULE: &str = "Init/Data/Array/Basic";
/// The fourth generated proof theorem for `Array.isPrefixOfAux`.
const ARRAY_IS_PREFIX_OF_AUX_PROOF_4: &str =
    "_private.Init.Data.Array.Basic.0.Array.isPrefixOfAux._proof_4";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_IS_PREFIX_OF_AUX_PROOF_4_MODULE: &str = "Init/Data/Array/Basic";
/// The generated equation theorem for `Array.isPrefixOfAux`.
const ARRAY_IS_PREFIX_OF_AUX_EQ_DEF: &str =
    "_private.Init.Data.Array.Basic.0.Array.isPrefixOfAux.eq_def";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_IS_PREFIX_OF_AUX_EQ_DEF_MODULE: &str = "Init/Data/Array/Basic";
/// The generated recursion helper for `Array.allDiffAuxAux`.
const ARRAY_ALL_DIFF_AUX_AUX_F: &str =
    "_private.Init.Data.Array.Basic.0.Array.allDiffAuxAux._f";
/// The pin's private array stores this helper in the basic module.
const ARRAY_ALL_DIFF_AUX_AUX_F_MODULE: &str = "Init/Data/Array/Basic";
/// The generated proof theorem for `Array.allDiffAuxAux`.
const ARRAY_ALL_DIFF_AUX_AUX_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.allDiffAuxAux._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ALL_DIFF_AUX_AUX_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unfolding helper for `Array.allDiffAuxAux`.
const ARRAY_ALL_DIFF_AUX_AUX_SUNFOLD: &str =
    "_private.Init.Data.Array.Basic.0.Array.allDiffAuxAux._sunfold";
/// The pin's private array stores this helper in the basic module.
const ARRAY_ALL_DIFF_AUX_AUX_SUNFOLD_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unsafe recursion helper for `Array.allDiffAuxAux`.
const ARRAY_ALL_DIFF_AUX_AUX_UNSAFE_REC: &str =
    "_private.Init.Data.Array.Basic.0.Array.allDiffAuxAux._unsafe_rec";
/// The pin's private array stores this helper in the basic module.
const ARRAY_ALL_DIFF_AUX_AUX_UNSAFE_REC_MODULE: &str = "Init/Data/Array/Basic";
/// The generated congruence theorem for `Array.allDiffAuxAux`.
const ARRAY_ALL_DIFF_AUX_AUX_CONGR_SIMP: &str =
    "_private.Init.Data.Array.Basic.0.Array.allDiffAuxAux.congr_simp";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_ALL_DIFF_AUX_AUX_CONGR_SIMP_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.allDiffAuxAux`.
const ARRAY_ALL_DIFF_AUX_AUX_MATCH_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.allDiffAuxAux.match_1";
/// The pin's private array stores this match helper in the basic module.
const ARRAY_ALL_DIFF_AUX_AUX_MATCH_1_MODULE: &str = "Init/Data/Array/Basic";
/// The private monadic map implementation helper generated for `Array.mapM`.
const ARRAY_MAP_M_MAP: &str = "_private.Init.Data.Array.Basic.0.Array.mapM.map";
/// The pin's private array stores this helper in the basic module.
const ARRAY_MAP_M_MAP_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unary helper for `Array.mapM.map`.
const ARRAY_MAP_M_MAP_UNARY: &str = "_private.Init.Data.Array.Basic.0.Array.mapM.map._unary";
/// The pin's private array stores this helper in the basic module.
const ARRAY_MAP_M_MAP_UNARY_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unsafe recursion helper for `Array.mapM.map`.
const ARRAY_MAP_M_MAP_UNSAFE_REC: &str =
    "_private.Init.Data.Array.Basic.0.Array.mapM.map._unsafe_rec";
/// The pin's private array stores this helper in the basic module.
const ARRAY_MAP_M_MAP_UNSAFE_REC_MODULE: &str = "Init/Data/Array/Basic";
/// The generated induction theorem for `Array.mapM.map`.
const ARRAY_MAP_M_MAP_INDUCT: &str = "_private.Init.Data.Array.Basic.0.Array.mapM.map.induct";
/// The pin stores this induction theorem in the internal order lemmas module.
const ARRAY_MAP_M_MAP_INDUCT_MODULE: &str = "Init/Internal/Order/Lemmas";
/// The private recursion helper generated for `Array.takeWhile`.
const ARRAY_TAKE_WHILE_GO: &str = "_private.Init.Data.Array.Basic.0.Array.takeWhile.go";
/// The pin's private array stores this helper in the basic module.
const ARRAY_TAKE_WHILE_GO_MODULE: &str = "Init/Data/Array/Basic";
/// The private recursion helper generated for `Array.zipWithAll`.
const ARRAY_ZIP_WITH_ALL_GO: &str = "_private.Init.Data.Array.Basic.0.Array.zipWithAll.go";
/// The pin's private array stores this helper in the basic module.
const ARRAY_ZIP_WITH_ALL_GO_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.unzip`.
const ARRAY_UNZIP_MATCH_1: &str = "_private.Init.Data.Array.Basic.0.Array.unzip.match_1";
/// The pin's private array stores this match helper in the basic module.
const ARRAY_UNZIP_MATCH_1_MODULE: &str = "Init/Data/Array/Basic";
/// A second generated match definition for `Array.unzip`.
const ARRAY_UNZIP_MATCH_3: &str = "_private.Init.Data.Array.Basic.0.Array.unzip.match_3";
/// The pin's private array stores this match helper in the basic module.
const ARRAY_UNZIP_MATCH_3_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.size_pop`.
const ARRAY_SIZE_POP_MATCH_1_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.size_pop.match_1_1";
/// The pin's private array stores this match helper in the basic module.
const ARRAY_SIZE_POP_MATCH_1_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.shrink`.
const ARRAY_SHRINK_MATCH_1: &str = "_private.Init.Data.Array.Basic.0.Array.shrink.match_1";
/// The pin's private array stores this match helper in the basic module.
const ARRAY_SHRINK_MATCH_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unfolding helper for `Array.shrink.loop`.
const ARRAY_SHRINK_LOOP_SUNFOLD: &str =
    "_private.Init.Data.Array.Basic.0.Array.shrink.loop._sunfold";
/// The pin's private array stores this helper in the basic module.
const ARRAY_SHRINK_LOOP_SUNFOLD_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unsafe recursion helper for `Array.shrink.loop`.
const ARRAY_SHRINK_LOOP_UNSAFE_REC: &str =
    "_private.Init.Data.Array.Basic.0.Array.shrink.loop._unsafe_rec";
/// The pin's private array stores this helper in the basic module.
const ARRAY_SHRINK_LOOP_UNSAFE_REC_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unsafe helper for `Array.modifyMUnsafe`.
const ARRAY_MODIFY_M_UNSAFE_PROOF_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.modifyMUnsafe._proof_1";
/// The pin's private array stores this definition in the basic module.
const ARRAY_MODIFY_M_UNSAFE_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated recursion helper for `Array.ofFn.go`.
const ARRAY_OF_FN_GO_F: &str = "_private.Init.Data.Array.Basic.0.Array.ofFn.go._f";
/// The pin's private array stores this helper in the basic module.
const ARRAY_OF_FN_GO_F_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unfolding helper for `Array.ofFn.go`.
const ARRAY_OF_FN_GO_SUNFOLD: &str = "_private.Init.Data.Array.Basic.0.Array.ofFn.go._sunfold";
/// The pin's private array stores this helper in the basic module.
const ARRAY_OF_FN_GO_SUNFOLD_MODULE: &str = "Init/Data/Array/Basic";
/// The generated unsafe recursion helper for `Array.ofFn.go`.
const ARRAY_OF_FN_GO_UNSAFE_REC: &str =
    "_private.Init.Data.Array.Basic.0.Array.ofFn.go._unsafe_rec";
/// The pin's private array stores this helper in the basic module.
const ARRAY_OF_FN_GO_UNSAFE_REC_MODULE: &str = "Init/Data/Array/Basic";
/// The generated proof theorem for `Array.ofFn.go`.
const ARRAY_OF_FN_GO_PROOF_1: &str = "_private.Init.Data.Array.Basic.0.Array.ofFn.go._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_OF_FN_GO_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.ofFn.go`.
const ARRAY_OF_FN_GO_MATCH_1: &str = "_private.Init.Data.Array.Basic.0.Array.ofFn.go.match_1";
/// The pin's private array stores this match helper in the basic module.
const ARRAY_OF_FN_GO_MATCH_1_MODULE: &str = "Init/Data/Array/Basic";
/// The first generated proof theorem for `Array.popWhile`.
const ARRAY_POP_WHILE_PROOF_1: &str = "_private.Init.Data.Array.Basic.0.Array.popWhile._proof_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_POP_WHILE_PROOF_1_MODULE: &str = "Init/Data/Array/Basic";
/// The second generated proof theorem for `Array.popWhile`.
const ARRAY_POP_WHILE_PROOF_2: &str = "_private.Init.Data.Array.Basic.0.Array.popWhile._proof_2";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_POP_WHILE_PROOF_2_MODULE: &str = "Init/Data/Array/Basic";
/// The third generated proof theorem for `Array.popWhile`.
const ARRAY_POP_WHILE_PROOF_3: &str = "_private.Init.Data.Array.Basic.0.Array.popWhile._proof_3";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_POP_WHILE_PROOF_3_MODULE: &str = "Init/Data/Array/Basic";
/// The generated equation theorem for `Array.popWhile`.
const ARRAY_POP_WHILE_EQ_1: &str = "_private.Init.Data.Array.Basic.0.Array.popWhile.eq_1";
/// The pin's private array stores this theorem in the basic module.
const ARRAY_POP_WHILE_EQ_1_MODULE: &str = "Init/Data/Array/Basic";
/// The generated match definition for `Array.mem_def`.
const ARRAY_MEM_DEF_MATCH_1_1: &str =
    "_private.Init.Data.Array.Basic.0.Array.mem_def.match_1_1";
/// The pin's private array stores this match helper in the basic module.
const ARRAY_MEM_DEF_MATCH_1_1_MODULE: &str = "Init/Data/Array/Basic";
/// The splitter definition generated for `Option.isSome.match_1`.
const OPTION_IS_SOME_MATCH_1_SPLITTER: &str =
    "_private.Init.Data.AC.0.Option.isSome.match_1.splitter";
/// The pin's private array stores the generated splitter in this module.
const OPTION_IS_SOME_MATCH_1_SPLITTER_MODULE: &str = "Init/Data/AC";
/// A private-mangled unary equation helper deliberately exported by the pinned
/// array-sort lemmas module.
const SUBARRAY_MERGE_SORT_UNARY_EQ_DEF: &str =
    "_private.Init.Data.Array.Sort.Lemmas.0.Subarray.mergeSort._unary.eq_def";
/// The two tail-recursive merge-sort implementation helpers in the pinned
/// `Init.Data.List.Sort.Impl` companion delta.
/// `mergeSortTR₂` helpers that are `_private.`-mangled AND declared by the
/// EXPORTED part of `Init.Data.List.Sort.Impl`.
///
/// Note the subscript. `mergeSortTR₂.run` is exported; `mergeSortTR.run`
/// without it is companion-only (see [`MERGE_SORT_TR_COMPANION_ONLY_UNSAFE_RECS`]).
/// Two declarations one character apart sit on opposite sides of the export
/// boundary, which is why the `_private.` prefix cannot be used to tell them
/// apart and why both directions are asserted below.
const MERGE_SORT_TR_EXPORTED_UNSAFE_RECS: [&str; 2] = [
    "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR₂.run._unsafe_rec",
    "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR₂.run'._unsafe_rec",
];

/// `_unsafe_rec` helpers of the same module that the exported part genuinely
/// omits — the population the companion chain has to restore.
const MERGE_SORT_TR_COMPANION_ONLY_UNSAFE_RECS: [&str; 3] = [
    "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR.run._unsafe_rec",
    "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeTR.go._unsafe_rec",
    "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.splitRevAt.go._unsafe_rec",
];

/// A recovered private declaration must retain a concrete declaration kind.
/// Keep this exhaustive so a future placeholder kind cannot silently satisfy
/// the companion-recovery tests.
fn is_concrete_recovery(info: &ConstantInfo) -> bool {
    matches!(
        info,
        ConstantInfo::Defn(_)
            | ConstantInfo::Thm(_)
            | ConstantInfo::Opaque(_)
            | ConstantInfo::Quot(_)
            | ConstantInfo::Induct(_)
            | ConstantInfo::Ctor(_)
            | ConstantInfo::Rec(_)
    )
}

#[test]
fn timy_witness_module_recovers_its_private_match_auxiliary() {
    let lib = lib_or_skip!("timy_witness_module_recovers_its_private_match_auxiliary");
    let chain = chain_bytes(&lib, "Init/Data/List/ToArrayImpl");
    let (exported, private) = exported_and_private_names(&chain);

    // The precondition that made the bead real. Without this assertion the one
    // below proves nothing: if the exported part already carried the auxiliary,
    // finding it in the chain would be no evidence about chain decode at all.
    assert_eq!(
        exported.len(),
        5,
        "measured at the pin: the exported part of Init.Data.List.ToArrayImpl \
         carries five constants; got {exported:?}"
    );
    assert!(
        !exported.contains(&TIMY_WITNESS.to_owned()),
        "the exported part must NOT carry {TIMY_WITNESS}; if it does, this suite \
         no longer witnesses the bead and its assertions are vacuous"
    );

    // The repaired behaviour.
    assert_eq!(
        private.len(),
        6,
        "measured at the pin: the private part carries the five exported \
         constants plus one equation-compiler auxiliary; got {private:?}"
    );
    assert!(
        private.contains(&TIMY_WITNESS.to_owned()),
        "the private part must carry {TIMY_WITNESS} — this is the exact \
         constant franken_lean-timy reported as never decoded; got {private:?}"
    );
    for name in &exported {
        assert!(
            private.contains(name),
            "the private constant array must be a superset of the exported one; \
             {name} is missing"
        );
    }
}

#[test]
fn the_recovered_auxiliary_decodes_to_a_real_constant_info() {
    let lib = lib_or_skip!("the_recovered_auxiliary_decodes_to_a_real_constant_info");
    let chain = chain_bytes(&lib, "Init/Data/List/ToArrayImpl");

    let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
        .expect("server part parses against the exported region");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against the exported and server regions");

    // Naming a constant is not decoding it. The bead's complaint was that the
    // kernel was handed no ConstantInfo for the auxiliary, so this walks the
    // whole declaration decoder — including the Name/Level/Expr identity
    // cross-checks it enables by default — over the chain.
    let constants = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("the private part's constants decode through the chain");

    assert_eq!(
        constants.len(),
        6,
        "the private part decodes six full ConstantInfos at the pin"
    );
    let witness = constants
        .iter()
        .find(|info| info.name().to_display_string() == TIMY_WITNESS);
    assert!(
        witness.is_some(),
        "{TIMY_WITNESS} must decode to a ConstantInfo, not merely appear in \
         constNames; decoded {:?}",
        constants
            .iter()
            .map(|info| info.name().to_display_string())
            .collect::<Vec<_>>()
    );
}

#[test]
fn timy_match_1_requires_the_private_companion_for_a_non_axiom_decode() {
    let lib = lib_or_skip!("timy_match_1_requires_the_private_companion_for_a_non_axiom_decode");
    let chain = chain_bytes(&lib, "Init/Data/List/ToArrayImpl");

    // The constNames cell pins the original corpus witness. This decoder-level
    // cell supplies its RED side: the exported declaration array must still
    // omit that exact `match_1`, or companion recovery is not being tested.
    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != TIMY_WITNESS),
        "exported decoder unexpectedly recovered {TIMY_WITNESS}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == TIMY_WITNESS)
        .unwrap_or_else(|| panic!("private decoder lost {TIMY_WITNESS}"));
    assert!(
        !matches!(recovered, ConstantInfo::Axiom(_)),
        "private companion recovery weakened {TIMY_WITNESS} to an axiom"
    );
}

#[test]
fn prelude_exported_mangled_unsafe_rec_still_requires_its_private_match_companion() {
    let lib = lib_or_skip!(
        "prelude_exported_mangled_unsafe_rec_still_requires_its_private_match_companion"
    );
    let chain = chain_bytes(&lib, "Init/Prelude");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    // `_private.` is a display-name mangling convention, not an origin bit.
    // This exact loop helper is public-overlap: both arrays carry it. Its
    // `match_1` dependency is the RED companion-only member, so name-prefix
    // classification would otherwise report the wrong failure source.
    assert!(
        exported_names.contains(&HEAD_INFO_LOOP_UNSAFE_REC.to_owned()),
        "Init.Prelude's exported part must retain the public-overlap {HEAD_INFO_LOOP_UNSAFE_REC}"
    );
    assert!(
        private_names.contains(&HEAD_INFO_LOOP_UNSAFE_REC.to_owned()),
        "Init.Prelude's private chain must retain the public-overlap {HEAD_INFO_LOOP_UNSAFE_REC}"
    );
    assert!(
        !exported_names.contains(&HEAD_INFO_LOOP_MATCH_1.to_owned()),
        "the exported part must omit the companion-only {HEAD_INFO_LOOP_MATCH_1}"
    );
    assert!(
        private_names.contains(&HEAD_INFO_LOOP_MATCH_1.to_owned()),
        "the private companion must restore {HEAD_INFO_LOOP_MATCH_1}"
    );

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    assert!(
        exported_constants
            .iter()
            .any(|info| info.name().to_display_string() == HEAD_INFO_LOOP_UNSAFE_REC),
        "exported decoder lost its public-overlap private-mangled declaration"
    );
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != HEAD_INFO_LOOP_MATCH_1),
        "exported decoder unexpectedly recovered the companion-only match_1"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let private_constants = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode");
    let recovered = private_constants
        .iter()
        .find(|info| info.name().to_display_string() == HEAD_INFO_LOOP_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {HEAD_INFO_LOOP_MATCH_1}"));
    assert!(
        !matches!(recovered, ConstantInfo::Axiom(_)),
        "companion recovery weakened {HEAD_INFO_LOOP_MATCH_1} to an axiom"
    );
}

#[test]
fn prelude_tail_pos_exported_mangled_unsafe_rec_requires_its_private_match_companion() {
    let lib = lib_or_skip!(
        "prelude_tail_pos_exported_mangled_unsafe_rec_requires_its_private_match_companion"
    );
    let chain = chain_bytes(&lib, "Init/Prelude");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    // This is the second exported `_private.` collision in the Syntax pair.
    // It proves that companion origin comes from actual part membership, while
    // its private match_1 dependency must still recover concretely.
    assert!(
        exported_names.contains(&TAIL_POS_LOOP_UNSAFE_REC.to_owned()),
        "Init.Prelude's exported part must retain {TAIL_POS_LOOP_UNSAFE_REC}"
    );
    assert!(
        private_names.contains(&TAIL_POS_LOOP_UNSAFE_REC.to_owned()),
        "Init.Prelude's private chain must retain {TAIL_POS_LOOP_UNSAFE_REC}"
    );
    assert!(
        !exported_names.contains(&TAIL_POS_LOOP_MATCH_1.to_owned()),
        "the exported part must omit the companion-only {TAIL_POS_LOOP_MATCH_1}"
    );
    assert!(
        private_names.contains(&TAIL_POS_LOOP_MATCH_1.to_owned()),
        "the private companion must restore {TAIL_POS_LOOP_MATCH_1}"
    );

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    assert!(
        exported_constants
            .iter()
            .any(|info| info.name().to_display_string() == TAIL_POS_LOOP_UNSAFE_REC),
        "exported decoder lost its public-overlap private-mangled tail-position helper"
    );
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != TAIL_POS_LOOP_MATCH_1),
        "exported decoder unexpectedly recovered the companion-only tail-position match_1"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == TAIL_POS_LOOP_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {TAIL_POS_LOOP_MATCH_1}"));
    assert!(
        is_concrete_recovery(&recovered),
        "companion recovery decoded {TAIL_POS_LOOP_MATCH_1} only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn prelude_name_hash_proof_auxiliaries_recover_with_concrete_kinds() {
    let lib = lib_or_skip!("prelude_name_hash_proof_auxiliaries_recover_with_concrete_kinds");
    let chain = chain_bytes(&lib, "Init/Prelude");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let private_constants = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode");

    for name in NAME_HASH_PROOF_AUXILIARIES {
        assert!(
            !exported_names.contains(&name.to_owned()),
            "the exported Prelude part must omit the private proof helper {name}"
        );
        assert!(
            private_names.contains(&name.to_owned()),
            "the Prelude private companion must restore the proof helper {name}"
        );
        assert!(
            exported_constants
                .iter()
                .all(|info| info.name().to_display_string() != name),
            "exported decoder unexpectedly recovered {name}"
        );
        let recovered = private_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("private decoder lost {name}"));
        assert!(
            is_concrete_recovery(recovered),
            "private companion decoded {name} only as {} instead of a concrete declaration",
            recovered.kind_name()
        );
    }
}

#[test]
fn array_map_m_go_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!("array_map_m_go_requires_the_companion_and_keeps_its_real_kind");
    let chain = chain_bytes(&lib, "Init/Data/Array/BasicAux");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    assert!(
        !exported_names.contains(&ARRAY_MAP_M_GO.to_owned()),
        "the exported part must omit the private recursion helper {ARRAY_MAP_M_GO}"
    );
    assert!(
        private_names.contains(&ARRAY_MAP_M_GO.to_owned()),
        "the private companion must restore {ARRAY_MAP_M_GO}"
    );

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != ARRAY_MAP_M_GO),
        "exported decoder unexpectedly recovered {ARRAY_MAP_M_GO}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MAP_M_GO}"));
    assert!(
        is_concrete_recovery(&recovered),
        "private companion decoded {ARRAY_MAP_M_GO} only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn array_of_push_eq_push_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_of_push_eq_push_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_OF_PUSH_EQ_PUSH_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_OF_PUSH_EQ_PUSH_MATCH_1_1.to_owned()),
        "the private companion of {ARRAY_OF_PUSH_EQ_PUSH_MATCH_1_1_MODULE} must retain \
         {ARRAY_OF_PUSH_EQ_PUSH_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_OF_PUSH_EQ_PUSH_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_OF_PUSH_EQ_PUSH_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_OF_PUSH_EQ_PUSH_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn list_of_to_array_aux_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_of_to_array_aux_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX.to_owned()),
        "the private companion of {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MODULE} must retain \
         {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn list_of_to_array_aux_helper_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_of_to_array_aux_helper_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_F_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_F.to_owned()),
        "the private companion of {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_F_MODULE} must retain \
         {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_F}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_F)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_F}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_F} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn list_of_to_array_aux_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_of_to_array_aux_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_1.to_owned()),
        "the private companion of {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_1_MODULE} must retain \
         {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| {
            info.name().to_display_string() == LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_1
        })
        .unwrap_or_else(|| {
            panic!("private decoder lost {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn list_size_to_array_aux_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("list_size_to_array_aux_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_SIZE_TO_ARRAY_AUX_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_SIZE_TO_ARRAY_AUX.to_owned()),
        "the private companion of {LIST_SIZE_TO_ARRAY_AUX_MODULE} must retain \
         {LIST_SIZE_TO_ARRAY_AUX}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_SIZE_TO_ARRAY_AUX)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_SIZE_TO_ARRAY_AUX}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {LIST_SIZE_TO_ARRAY_AUX} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn list_to_array_aux_equation_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_to_array_aux_equation_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_TO_ARRAY_AUX_EQ_1.to_owned()),
        "the private companion of {LIST_TO_ARRAY_AUX_EQ_1_MODULE} must retain \
         {LIST_TO_ARRAY_AUX_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_TO_ARRAY_AUX_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_TO_ARRAY_AUX_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {LIST_TO_ARRAY_AUX_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn psigma_cases_on_arg_pusher_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("psigma_cases_on_arg_pusher_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, PSIGMA_CASES_ON_ARG_PUSHER_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&PSIGMA_CASES_ON_ARG_PUSHER.to_owned()),
        "the private companion of {PSIGMA_CASES_ON_ARG_PUSHER_MODULE} must retain \\
         {PSIGMA_CASES_ON_ARG_PUSHER}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == PSIGMA_CASES_ON_ARG_PUSHER)
        .unwrap_or_else(|| panic!("private decoder lost {PSIGMA_CASES_ON_ARG_PUSHER}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {PSIGMA_CASES_ON_ARG_PUSHER} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn get_elem_match_equation_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("get_elem_match_equation_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, GET_ELEM_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&GET_ELEM_MATCH_1_EQ_1.to_owned()),
        "the private companion of {GET_ELEM_MATCH_1_EQ_1_MODULE} must retain \\
         {GET_ELEM_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == GET_ELEM_MATCH_1_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {GET_ELEM_MATCH_1_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {GET_ELEM_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn get_elem_second_match_equation_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("get_elem_second_match_equation_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, GET_ELEM_MATCH_1_EQ_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&GET_ELEM_MATCH_1_EQ_2.to_owned()),
        "the private companion of {GET_ELEM_MATCH_1_EQ_2_MODULE} must retain \\
         {GET_ELEM_MATCH_1_EQ_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == GET_ELEM_MATCH_1_EQ_2)
        .unwrap_or_else(|| panic!("private decoder lost {GET_ELEM_MATCH_1_EQ_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {GET_ELEM_MATCH_1_EQ_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn get_elem_match_splitter_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("get_elem_match_splitter_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, GET_ELEM_MATCH_1_SPLITTER_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&GET_ELEM_MATCH_1_SPLITTER.to_owned()),
        "the private companion of {GET_ELEM_MATCH_1_SPLITTER_MODULE} must retain \\
         {GET_ELEM_MATCH_1_SPLITTER}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == GET_ELEM_MATCH_1_SPLITTER)
        .unwrap_or_else(|| panic!("private decoder lost {GET_ELEM_MATCH_1_SPLITTER}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {GET_ELEM_MATCH_1_SPLITTER} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn list_mem_to_array_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_mem_to_array_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_MEM_TO_ARRAY_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_MEM_TO_ARRAY_SIMP_1_1.to_owned()),
        "the private companion of {LIST_MEM_TO_ARRAY_SIMP_1_1_MODULE} must retain \\
         {LIST_MEM_TO_ARRAY_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_MEM_TO_ARRAY_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_MEM_TO_ARRAY_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {LIST_MEM_TO_ARRAY_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn list_to_array_aux_second_equation_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "list_to_array_aux_second_equation_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_EQ_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_TO_ARRAY_AUX_BASIC_EQ_2.to_owned()),
        "the private companion of {LIST_TO_ARRAY_AUX_BASIC_EQ_2_MODULE} must retain \\
         {LIST_TO_ARRAY_AUX_BASIC_EQ_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_EQ_2)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_TO_ARRAY_AUX_BASIC_EQ_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {LIST_TO_ARRAY_AUX_BASIC_EQ_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn list_to_array_aux_defining_equation_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "list_to_array_aux_defining_equation_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_EQ_DEF_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_TO_ARRAY_AUX_BASIC_EQ_DEF.to_owned()),
        "the private companion of {LIST_TO_ARRAY_AUX_BASIC_EQ_DEF_MODULE} must retain \\
         {LIST_TO_ARRAY_AUX_BASIC_EQ_DEF}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_EQ_DEF)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_TO_ARRAY_AUX_BASIC_EQ_DEF}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {LIST_TO_ARRAY_AUX_BASIC_EQ_DEF} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn list_to_array_aux_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_to_array_aux_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_1.to_owned()),
        "the private companion of {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_1_MODULE} must retain \\
         {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn list_to_array_aux_second_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_to_array_aux_second_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_2.to_owned()),
        "the private companion of {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_2_MODULE} must retain \\
         {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_2)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_EQ_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn list_to_array_aux_match_splitter_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_to_array_aux_match_splitter_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_MATCH_1_SPLITTER_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);
    assert!(
        private_names.contains(&LIST_TO_ARRAY_AUX_BASIC_MATCH_1_SPLITTER.to_owned()),
        "the private companion of {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_SPLITTER_MODULE} must retain \\
         {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_SPLITTER}"
    );
    let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
        .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants().expect("private constants decode").into_iter()
        .find(|info| info.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_MATCH_1_SPLITTER)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_SPLITTER}"));
    assert!(matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {LIST_TO_ARRAY_AUX_BASIC_MATCH_1_SPLITTER} as {} instead of Defn",
        recovered.kind_name());
}

#[test]
fn array_map_m_go_unary_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_go_unary_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);
    assert!(private_names.contains(&ARRAY_MAP_M_GO_UNARY_PROOF_1.to_owned()),
        "the private companion of {ARRAY_MAP_M_GO_UNARY_PROOF_1_MODULE} must retain {ARRAY_MAP_M_GO_UNARY_PROOF_1}");
    let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
        .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default()).decode_module_constants()
        .expect("private constants decode").into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO_UNARY_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MAP_M_GO_UNARY_PROOF_1}"));
    assert!(matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_MAP_M_GO_UNARY_PROOF_1} as {} instead of Thm", recovered.kind_name());
}

#[test]
fn array_map_m_go_unary_second_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_go_unary_second_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_PROOF_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);
    assert!(private_names.contains(&ARRAY_MAP_M_GO_UNARY_PROOF_2.to_owned()));
    let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap();
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO_UNARY_PROOF_2).unwrap();
    assert!(matches!(recovered, ConstantInfo::Thm(_)));
}

#[test]
fn array_map_m_go_unary_third_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_go_unary_third_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_PROOF_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);
    assert!(private_names.contains(&ARRAY_MAP_M_GO_UNARY_PROOF_3.to_owned()));
    let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap();
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO_UNARY_PROOF_3).unwrap();
    assert!(matches!(recovered, ConstantInfo::Thm(_)));
}

#[test]
fn array_map_m_go_unary_fourth_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_go_unary_fourth_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_PROOF_4_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);
    assert!(private_names.contains(&ARRAY_MAP_M_GO_UNARY_PROOF_4.to_owned()));
    let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap();
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO_UNARY_PROOF_4).unwrap();
    assert!(matches!(recovered, ConstantInfo::Thm(_)));
}

#[test]
fn array_map_m_go_unary_fifth_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_go_unary_fifth_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_PROOF_5_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);
    assert!(private_names.contains(&ARRAY_MAP_M_GO_UNARY_PROOF_5.to_owned()));
    let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap();
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO_UNARY_PROOF_5).unwrap();
    assert!(matches!(recovered, ConstantInfo::Thm(_)));
}

#[test]
fn array_map_m_go_unary_sixth_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_go_unary_sixth_proof_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_PROOF_6_MODULE); let (_, private_names) = exported_and_private_names(&chain); assert!(private_names.contains(&ARRAY_MAP_M_GO_UNARY_PROOF_6.to_owned())); let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let recovered = DeclDecoder::new(&private_view, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO_UNARY_PROOF_6).unwrap(); assert!(matches!(recovered, ConstantInfo::Thm(_)));
}

#[test]
fn array_map_m_go_unary_seventh_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_go_unary_seventh_proof_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_PROOF_7_MODULE); let (_, private_names) = exported_and_private_names(&chain); assert!(private_names.contains(&ARRAY_MAP_M_GO_UNARY_PROOF_7.to_owned())); let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let recovered = DeclDecoder::new(&private_view, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO_UNARY_PROOF_7).unwrap(); assert!(matches!(recovered, ConstantInfo::Thm(_)));
}

#[test]
fn array_map_m_go_unary_eighth_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_go_unary_eighth_proof_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_PROOF_8_MODULE); let (_, private_names) = exported_and_private_names(&chain); assert!(private_names.contains(&ARRAY_MAP_M_GO_UNARY_PROOF_8.to_owned())); let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let recovered = DeclDecoder::new(&private_view, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO_UNARY_PROOF_8).unwrap(); assert!(matches!(recovered, ConstantInfo::Thm(_)));
}

#[test]
fn array_map_m_go_unary_eq_def_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_go_unary_eq_def_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_EQ_DEF_MODULE); let (_, private_names) = exported_and_private_names(&chain); assert!(private_names.contains(&ARRAY_MAP_M_GO_UNARY_EQ_DEF.to_owned())); let private_view = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let recovered = DeclDecoder::new(&private_view, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|info| info.name().to_display_string() == ARRAY_MAP_M_GO_UNARY_EQ_DEF).unwrap(); assert!(matches!(recovered, ConstantInfo::Thm(_)));
}

#[test]
fn array_map_m_go_unsafe_rec_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_map_m_go_unsafe_rec_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNSAFE_REC_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_MAP_M_GO_UNSAFE_REC.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_MAP_M_GO_UNSAFE_REC).unwrap(); assert!(matches!(r, ConstantInfo::Defn(_))); }

#[test]
fn array_map_m_go_eq_def_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_map_m_go_eq_def_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_EQ_DEF_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_MAP_M_GO_EQ_DEF.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_MAP_M_GO_EQ_DEF).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn list_of_to_array_aux_match_six_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("list_of_to_array_aux_match_six_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_6_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_6.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == LIST_OF_TO_ARRAY_AUX_EQ_TO_ARRAY_AUX_MATCH_1_6).unwrap(); assert!(matches!(r, ConstantInfo::Defn(_))); }

#[test]
fn array_map_m_go_proof_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_map_m_go_proof_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_PROOF_1_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_MAP_M_GO_PROOF_1.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_MAP_M_GO_PROOF_1).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn array_map_m_go_second_proof_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_map_m_go_second_proof_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_PROOF_2_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_MAP_M_GO_PROOF_2.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_MAP_M_GO_PROOF_2).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn array_map_m_go_unary_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_map_m_go_unary_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_MAP_M_GO_UNARY_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_MAP_M_GO_UNARY.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_MAP_M_GO_UNARY).unwrap(); assert!(matches!(r, ConstantInfo::Defn(_))); }

#[test]
fn map_mono_m_imp_go_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("map_mono_m_imp_go_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, MAP_MONO_M_IMP_GO_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&MAP_MONO_M_IMP_GO.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == MAP_MONO_M_IMP_GO).unwrap(); assert!(matches!(r, ConstantInfo::Defn(_))); }

#[test]
fn list_to_array_aux_basic_aux_second_equation_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("list_to_array_aux_basic_aux_second_equation_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_2_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_2.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_2).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn list_to_array_aux_basic_aux_defining_equation_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("list_to_array_aux_basic_aux_defining_equation_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_DEF_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_DEF.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_AUX_EQ_DEF).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn list_to_array_aux_basic_aux_match_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("list_to_array_aux_basic_aux_match_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_1_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_1.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_1).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn list_to_array_aux_basic_aux_second_match_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("list_to_array_aux_basic_aux_second_match_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_2_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_2.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_EQ_2).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn list_to_array_aux_basic_aux_match_splitter_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("list_to_array_aux_basic_aux_match_splitter_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_SPLITTER_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_SPLITTER.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == LIST_TO_ARRAY_AUX_BASIC_AUX_MATCH_1_SPLITTER).unwrap(); assert!(matches!(r, ConstantInfo::Defn(_))); }

#[test]
fn psigma_cases_on_arg_pusher_basic_aux_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("psigma_cases_on_arg_pusher_basic_aux_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, PSIGMA_CASES_ON_ARG_PUSHER_BASIC_AUX_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&PSIGMA_CASES_ON_ARG_PUSHER_BASIC_AUX.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == PSIGMA_CASES_ON_ARG_PUSHER_BASIC_AUX).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn array_all_diff_aux_defining_equation_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_all_diff_aux_defining_equation_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_EQ_DEF_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_ALL_DIFF_AUX_EQ_DEF.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_ALL_DIFF_AUX_EQ_DEF).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn array_find_fin_idx_equation_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_find_fin_idx_equation_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_FIND_FIN_IDX_EQ_1_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_FIND_FIN_IDX_EQ_1.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_FIND_FIN_IDX_EQ_1).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn array_find_fin_idx_loop_defining_equation_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_find_fin_idx_loop_defining_equation_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_FIND_FIN_IDX_LOOP_EQ_DEF_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_FIND_FIN_IDX_LOOP_EQ_DEF.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_FIND_FIN_IDX_LOOP_EQ_DEF).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn array_find_fin_idx_loop_proof_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_find_fin_idx_loop_proof_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_FIND_FIN_IDX_LOOP_PROOF_1_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_FIND_FIN_IDX_LOOP_PROOF_1.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_FIND_FIN_IDX_LOOP_PROOF_1).unwrap(); assert!(matches!(r, ConstantInfo::Thm(_))); }

#[test]
fn array_find_fin_idx_loop_unsafe_rec_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_find_fin_idx_loop_unsafe_rec_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_FIND_FIN_IDX_LOOP_UNSAFE_REC_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_FIND_FIN_IDX_LOOP_UNSAFE_REC.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_FIND_FIN_IDX_LOOP_UNSAFE_REC).unwrap(); assert!(matches!(r, ConstantInfo::Defn(_))); }

#[test]
fn array_find_some_rev_m_find_is_decoded_from_its_private_storage_module() { let lib = lib_or_skip!("array_find_some_rev_m_find_is_decoded_from_its_private_storage_module"); let chain = chain_bytes(&lib, ARRAY_FIND_SOME_REV_M_FIND_MODULE); let (_, n) = exported_and_private_names(&chain); assert!(n.contains(&ARRAY_FIND_SOME_REV_M_FIND.to_owned())); let v = OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server]).unwrap(); let r = DeclDecoder::new(&v, WalkBudget::default()).decode_module_constants().unwrap().into_iter().find(|i| i.name().to_display_string() == ARRAY_FIND_SOME_REV_M_FIND).unwrap(); assert!(matches!(r, ConstantInfo::Defn(_))); }

#[test]
fn map_mono_m_imp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("map_mono_m_imp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, MAP_MONO_M_IMP_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&MAP_MONO_M_IMP.to_owned()),
        "the private companion of {MAP_MONO_M_IMP_MODULE} must retain {MAP_MONO_M_IMP}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == MAP_MONO_M_IMP)
        .unwrap_or_else(|| panic!("private decoder lost {MAP_MONO_M_IMP}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {MAP_MONO_M_IMP} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn byte_array_utf8_decode_success_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "byte_array_utf8_decode_success_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, BYTE_ARRAY_IS_SOME_UTF8_DECODE_GO_IFF_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&BYTE_ARRAY_IS_SOME_UTF8_DECODE_GO_IFF.to_owned()),
        "the private companion of {BYTE_ARRAY_IS_SOME_UTF8_DECODE_GO_IFF_MODULE} must retain \\
         {BYTE_ARRAY_IS_SOME_UTF8_DECODE_GO_IFF}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == BYTE_ARRAY_IS_SOME_UTF8_DECODE_GO_IFF)
        .unwrap_or_else(|| {
            panic!("private decoder lost {BYTE_ARRAY_IS_SOME_UTF8_DECODE_GO_IFF}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {BYTE_ARRAY_IS_SOME_UTF8_DECODE_GO_IFF} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn byte_array_utf8_decode_match_equation_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "byte_array_utf8_decode_match_equation_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, BYTE_ARRAY_UTF8_DECODE_GO_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&BYTE_ARRAY_UTF8_DECODE_GO_MATCH_1_EQ_1.to_owned()),
        "the private companion of {BYTE_ARRAY_UTF8_DECODE_GO_MATCH_1_EQ_1_MODULE} must retain \\
         {BYTE_ARRAY_UTF8_DECODE_GO_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == BYTE_ARRAY_UTF8_DECODE_GO_MATCH_1_EQ_1)
        .unwrap_or_else(|| {
            panic!("private decoder lost {BYTE_ARRAY_UTF8_DECODE_GO_MATCH_1_EQ_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {BYTE_ARRAY_UTF8_DECODE_GO_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn string_pos_raw_get_match_equation_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "string_pos_raw_get_match_equation_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, STRING_POS_RAW_GET_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&STRING_POS_RAW_GET_MATCH_1_EQ_1.to_owned()),
        "the private companion of {STRING_POS_RAW_GET_MATCH_1_EQ_1_MODULE} must retain \\
         {STRING_POS_RAW_GET_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == STRING_POS_RAW_GET_MATCH_1_EQ_1)
        .unwrap_or_else(|| {
            panic!("private decoder lost {STRING_POS_RAW_GET_MATCH_1_EQ_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {STRING_POS_RAW_GET_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn byte_array_utf8_singleton_append_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "byte_array_utf8_singleton_append_match_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(
        &lib,
        BYTE_ARRAY_IS_VALID_UTF8_SINGLETON_APPEND_MATCH_1_1_MODULE,
    );
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&BYTE_ARRAY_IS_VALID_UTF8_SINGLETON_APPEND_MATCH_1_1.to_owned()),
        "the private companion of {BYTE_ARRAY_IS_VALID_UTF8_SINGLETON_APPEND_MATCH_1_1_MODULE} \
         must retain {BYTE_ARRAY_IS_VALID_UTF8_SINGLETON_APPEND_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| {
            info.name().to_display_string() == BYTE_ARRAY_IS_VALID_UTF8_SINGLETON_APPEND_MATCH_1_1
        })
        .unwrap_or_else(|| {
            panic!(
                "private decoder lost {BYTE_ARRAY_IS_VALID_UTF8_SINGLETON_APPEND_MATCH_1_1}"
            )
        });
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {BYTE_ARRAY_IS_VALID_UTF8_SINGLETON_APPEND_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn byte_array_utf8_validation_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "byte_array_utf8_validation_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, BYTE_ARRAY_VALIDATE_UTF8_EQ_FALSE_IFF_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&BYTE_ARRAY_VALIDATE_UTF8_EQ_FALSE_IFF_SIMP_1_1.to_owned()),
        "the private companion of {BYTE_ARRAY_VALIDATE_UTF8_EQ_FALSE_IFF_SIMP_1_1_MODULE} \
         must retain {BYTE_ARRAY_VALIDATE_UTF8_EQ_FALSE_IFF_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| {
            info.name().to_display_string() == BYTE_ARRAY_VALIDATE_UTF8_EQ_FALSE_IFF_SIMP_1_1
        })
        .unwrap_or_else(|| {
            panic!("private decoder lost {BYTE_ARRAY_VALIDATE_UTF8_EQ_FALSE_IFF_SIMP_1_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {BYTE_ARRAY_VALIDATE_UTF8_EQ_FALSE_IFF_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn string_pos_raw_append_left_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "string_pos_raw_append_left_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, STRING_POS_RAW_IS_VALID_APPEND_LEFT_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&STRING_POS_RAW_IS_VALID_APPEND_LEFT_SIMP_1_1.to_owned()),
        "the private companion of {STRING_POS_RAW_IS_VALID_APPEND_LEFT_SIMP_1_1_MODULE} \
         must retain {STRING_POS_RAW_IS_VALID_APPEND_LEFT_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| {
            info.name().to_display_string() == STRING_POS_RAW_IS_VALID_APPEND_LEFT_SIMP_1_1
        })
        .unwrap_or_else(|| {
            panic!("private decoder lost {STRING_POS_RAW_IS_VALID_APPEND_LEFT_SIMP_1_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {STRING_POS_RAW_IS_VALID_APPEND_LEFT_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn nat_add_assoc_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("nat_add_assoc_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, NAT_ADD_ASSOC_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&NAT_ADD_ASSOC_MATCH_1_1.to_owned()),
        "the private companion of {NAT_ADD_ASSOC_MATCH_1_1_MODULE} must retain \\
         {NAT_ADD_ASSOC_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == NAT_ADD_ASSOC_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {NAT_ADD_ASSOC_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {NAT_ADD_ASSOC_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn nat_mul_assoc_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("nat_mul_assoc_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, NAT_MUL_ASSOC_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&NAT_MUL_ASSOC_MATCH_1_1.to_owned()),
        "the private companion of {NAT_MUL_ASSOC_MATCH_1_1_MODULE} must retain \\
         {NAT_MUL_ASSOC_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == NAT_MUL_ASSOC_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {NAT_MUL_ASSOC_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {NAT_MUL_ASSOC_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn nat_beq_match_equation_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("nat_beq_match_equation_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, NAT_BEQ_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&NAT_BEQ_MATCH_1_EQ_1.to_owned()),
        "the private companion of {NAT_BEQ_MATCH_1_EQ_1_MODULE} must retain \\
         {NAT_BEQ_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == NAT_BEQ_MATCH_1_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {NAT_BEQ_MATCH_1_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {NAT_BEQ_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn nat_repeat_match_equation_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("nat_repeat_match_equation_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, NAT_REPEAT_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&NAT_REPEAT_MATCH_1_EQ_1.to_owned()),
        "the private companion of {NAT_REPEAT_MATCH_1_EQ_1_MODULE} must retain \\
         {NAT_REPEAT_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == NAT_REPEAT_MATCH_1_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {NAT_REPEAT_MATCH_1_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {NAT_REPEAT_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn int_zero_ne_one_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("int_zero_ne_one_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, INT_ZERO_NE_ONE_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&INT_ZERO_NE_ONE_MATCH_1_1.to_owned()),
        "the private companion of {INT_ZERO_NE_ONE_MATCH_1_1_MODULE} must retain \\
         {INT_ZERO_NE_ONE_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == INT_ZERO_NE_ONE_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {INT_ZERO_NE_ONE_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {INT_ZERO_NE_ONE_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn int_not_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("int_not_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, INT_NOT_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&INT_NOT_MATCH_1.to_owned()),
        "the private companion of {INT_NOT_MATCH_1_MODULE} must retain {INT_NOT_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == INT_NOT_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {INT_NOT_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {INT_NOT_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn bool_exists_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("bool_exists_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, BOOL_EXISTS_BOOL_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&BOOL_EXISTS_BOOL_MATCH_1_1.to_owned()),
        "the private companion of {BOOL_EXISTS_BOOL_MATCH_1_1_MODULE} must retain \\
         {BOOL_EXISTS_BOOL_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == BOOL_EXISTS_BOOL_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {BOOL_EXISTS_BOOL_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {BOOL_EXISTS_BOOL_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_map_id_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("option_map_id_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_MAP_ID_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_MAP_ID_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_MAP_ID_MATCH_1_1_MODULE} must retain \\
         {OPTION_MAP_ID_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_MAP_ID_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_MAP_ID_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_MAP_ID_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn prod_swap_inj_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("prod_swap_inj_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, PROD_SWAP_INJ_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&PROD_SWAP_INJ_SIMP_1_1.to_owned()),
        "the private companion of {PROD_SWAP_INJ_SIMP_1_1_MODULE} must retain \\
         {PROD_SWAP_INJ_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == PROD_SWAP_INJ_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {PROD_SWAP_INJ_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {PROD_SWAP_INJ_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn sum_lex_inr_inl_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("sum_lex_inr_inl_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, SUM_LEX_INR_INL_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&SUM_LEX_INR_INL_MATCH_1_1.to_owned()),
        "the private companion of {SUM_LEX_INR_INL_MATCH_1_1_MODULE} must retain \\
         {SUM_LEX_INR_INL_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == SUM_LEX_INR_INL_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {SUM_LEX_INR_INL_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {SUM_LEX_INR_INL_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn fin_mlt_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("fin_mlt_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, FIN_MLT_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&FIN_MLT.to_owned()),
        "the private companion of {FIN_MLT_MODULE} must retain {FIN_MLT}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == FIN_MLT)
        .unwrap_or_else(|| panic!("private decoder lost {FIN_MLT}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {FIN_MLT} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn char_is_valid_uint32_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("char_is_valid_uint32_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, CHAR_IS_VALID_UINT32_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&CHAR_IS_VALID_UINT32_MATCH_1_1.to_owned()),
        "the private companion of {CHAR_IS_VALID_UINT32_MATCH_1_1_MODULE} must retain \\
         {CHAR_IS_VALID_UINT32_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == CHAR_IS_VALID_UINT32_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {CHAR_IS_VALID_UINT32_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {CHAR_IS_VALID_UINT32_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn uint16_and_le_left_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("uint16_and_le_left_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, UINT16_AND_LE_LEFT_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&UINT16_AND_LE_LEFT_SIMP_1_1.to_owned()),
        "the private companion of {UINT16_AND_LE_LEFT_SIMP_1_1_MODULE} must retain \\
         {UINT16_AND_LE_LEFT_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == UINT16_AND_LE_LEFT_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {UINT16_AND_LE_LEFT_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {UINT16_AND_LE_LEFT_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn float_of_bits_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("float_of_bits_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, FLOAT_OF_BITS_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&FLOAT_OF_BITS_PROOF_1.to_owned()),
        "the private companion of {FLOAT_OF_BITS_PROOF_1_MODULE} must retain {FLOAT_OF_BITS_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == FLOAT_OF_BITS_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {FLOAT_OF_BITS_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {FLOAT_OF_BITS_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn rat_mul_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("rat_mul_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, RAT_MUL_SIMP_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&RAT_MUL_SIMP_1.to_owned()),
        "the private companion of {RAT_MUL_SIMP_1_MODULE} must retain {RAT_MUL_SIMP_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == RAT_MUL_SIMP_1)
        .unwrap_or_else(|| panic!("private decoder lost {RAT_MUL_SIMP_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {RAT_MUL_SIMP_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn byte_array_fast_append_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("byte_array_fast_append_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, BYTE_ARRAY_FAST_APPEND_EQ_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&BYTE_ARRAY_FAST_APPEND_EQ_SIMP_1_1.to_owned()),
        "the private companion of {BYTE_ARRAY_FAST_APPEND_EQ_SIMP_1_1_MODULE} must retain \\
         {BYTE_ARRAY_FAST_APPEND_EQ_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == BYTE_ARRAY_FAST_APPEND_EQ_SIMP_1_1)
        .unwrap_or_else(|| {
            panic!("private decoder lost {BYTE_ARRAY_FAST_APPEND_EQ_SIMP_1_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {BYTE_ARRAY_FAST_APPEND_EQ_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn dyadic_neg_add_cancel_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("dyadic_neg_add_cancel_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, DYADIC_NEG_ADD_CANCEL_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&DYADIC_NEG_ADD_CANCEL_SIMP_1_1.to_owned()),
        "the private companion of {DYADIC_NEG_ADD_CANCEL_SIMP_1_1_MODULE} must retain \\
         {DYADIC_NEG_ADD_CANCEL_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == DYADIC_NEG_ADD_CANCEL_SIMP_1_1)
        .unwrap_or_else(|| {
            panic!("private decoder lost {DYADIC_NEG_ADD_CANCEL_SIMP_1_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {DYADIC_NEG_ADD_CANCEL_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn bit_vec_get_msb_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("bit_vec_get_msb_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, BIT_VEC_GET_MSB_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&BIT_VEC_GET_MSB_PROOF_1.to_owned()),
        "the private companion of {BIT_VEC_GET_MSB_PROOF_1_MODULE} must retain \\
         {BIT_VEC_GET_MSB_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == BIT_VEC_GET_MSB_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {BIT_VEC_GET_MSB_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {BIT_VEC_GET_MSB_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn format_should_flatten_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("format_should_flatten_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, FORMAT_SHOULD_FLATTEN_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&FORMAT_SHOULD_FLATTEN_MATCH_1.to_owned()),
        "the private companion of {FORMAT_SHOULD_FLATTEN_MATCH_1_MODULE} must retain \\
         {FORMAT_SHOULD_FLATTEN_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == FORMAT_SHOULD_FLATTEN_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {FORMAT_SHOULD_FLATTEN_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {FORMAT_SHOULD_FLATTEN_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn vector_elim_as_array_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("vector_elim_as_array_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, VECTOR_ELIM_AS_ARRAY_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&VECTOR_ELIM_AS_ARRAY_MATCH_1.to_owned()),
        "the private companion of {VECTOR_ELIM_AS_ARRAY_MATCH_1_MODULE} must retain \\
         {VECTOR_ELIM_AS_ARRAY_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == VECTOR_ELIM_AS_ARRAY_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {VECTOR_ELIM_AS_ARRAY_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {VECTOR_ELIM_AS_ARRAY_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn bool_forall_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("bool_forall_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, BOOL_FORALL_BOOL_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&BOOL_FORALL_BOOL_MATCH_1_1.to_owned()),
        "the private companion of {BOOL_FORALL_BOOL_MATCH_1_1_MODULE} must retain \\
         {BOOL_FORALL_BOOL_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == BOOL_FORALL_BOOL_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {BOOL_FORALL_BOOL_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {BOOL_FORALL_BOOL_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_some_get_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("option_some_get_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_SOME_GET_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_SOME_GET_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_SOME_GET_MATCH_1_1_MODULE} must retain \\
         {OPTION_SOME_GET_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_SOME_GET_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_SOME_GET_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_SOME_GET_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_is_none_filter_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_is_none_filter_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_IS_NONE_FILTER_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_NONE_FILTER_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_IS_NONE_FILTER_MATCH_1_1_MODULE} must retain \\
         {OPTION_IS_NONE_FILTER_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_NONE_FILTER_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_IS_NONE_FILTER_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_IS_NONE_FILTER_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_is_some_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("option_is_some_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_IS_SOME_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_SOME_MATCH_1_EQ_1.to_owned()),
        "the private companion of {OPTION_IS_SOME_MATCH_1_EQ_1_MODULE} must retain \\
         {OPTION_IS_SOME_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_SOME_MATCH_1_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_IS_SOME_MATCH_1_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_IS_SOME_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_is_some_second_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_is_some_second_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_IS_SOME_MATCH_1_EQ_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_SOME_MATCH_1_EQ_2.to_owned()),
        "the private companion of {OPTION_IS_SOME_MATCH_1_EQ_2_MODULE} must retain \\
         {OPTION_IS_SOME_MATCH_1_EQ_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_SOME_MATCH_1_EQ_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_IS_SOME_MATCH_1_EQ_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_IS_SOME_MATCH_1_EQ_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_lemmas_is_some_match_splitter_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_lemmas_is_some_match_splitter_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_LEMMAS_IS_SOME_MATCH_1_SPLITTER_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_LEMMAS_IS_SOME_MATCH_1_SPLITTER.to_owned()),
        "the private companion of {OPTION_LEMMAS_IS_SOME_MATCH_1_SPLITTER_MODULE} must retain \\
         {OPTION_LEMMAS_IS_SOME_MATCH_1_SPLITTER}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_LEMMAS_IS_SOME_MATCH_1_SPLITTER)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_LEMMAS_IS_SOME_MATCH_1_SPLITTER}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_LEMMAS_IS_SOME_MATCH_1_SPLITTER} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_join_eq_none_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_join_eq_none_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_JOIN_EQ_NONE_IFF_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_JOIN_EQ_NONE_IFF_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_JOIN_EQ_NONE_IFF_MATCH_1_1_MODULE} must retain \\
         {OPTION_JOIN_EQ_NONE_IFF_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_JOIN_EQ_NONE_IFF_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_JOIN_EQ_NONE_IFF_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_JOIN_EQ_NONE_IFF_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_join_eq_some_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_join_eq_some_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_JOIN_EQ_SOME_IFF_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_JOIN_EQ_SOME_IFF_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_JOIN_EQ_SOME_IFF_SIMP_1_1_MODULE} must retain \\
         {OPTION_JOIN_EQ_SOME_IFF_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_JOIN_EQ_SOME_IFF_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_JOIN_EQ_SOME_IFF_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_JOIN_EQ_SOME_IFF_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_join_eq_some_second_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_join_eq_some_second_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_JOIN_EQ_SOME_IFF_SIMP_1_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_JOIN_EQ_SOME_IFF_SIMP_1_2.to_owned()),
        "the private companion of {OPTION_JOIN_EQ_SOME_IFF_SIMP_1_2_MODULE} must retain \\
         {OPTION_JOIN_EQ_SOME_IFF_SIMP_1_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_JOIN_EQ_SOME_IFF_SIMP_1_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_JOIN_EQ_SOME_IFF_SIMP_1_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_JOIN_EQ_SOME_IFF_SIMP_1_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_join_filter_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_join_filter_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_JOIN_FILTER_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_JOIN_FILTER_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_JOIN_FILTER_MATCH_1_1_MODULE} must retain \\
         {OPTION_JOIN_FILTER_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_JOIN_FILTER_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_JOIN_FILTER_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_JOIN_FILTER_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_join_ne_none_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_join_ne_none_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_JOIN_NE_NONE_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_JOIN_NE_NONE_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_JOIN_NE_NONE_SIMP_1_1_MODULE} must retain \\
         {OPTION_JOIN_NE_NONE_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_JOIN_NE_NONE_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_JOIN_NE_NONE_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_JOIN_NE_NONE_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_mem_to_array_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_mem_to_array_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_MEM_TO_ARRAY_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_MEM_TO_ARRAY_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_MEM_TO_ARRAY_SIMP_1_1_MODULE} must retain \\
         {OPTION_MEM_TO_ARRAY_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_MEM_TO_ARRAY_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_MEM_TO_ARRAY_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_MEM_TO_ARRAY_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_to_array_join_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_to_array_join_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_TO_ARRAY_JOIN_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_TO_ARRAY_JOIN_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_TO_ARRAY_JOIN_SIMP_1_1_MODULE} must retain \\
         {OPTION_TO_ARRAY_JOIN_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_TO_ARRAY_JOIN_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_TO_ARRAY_JOIN_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_TO_ARRAY_JOIN_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_attach_eq_some_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_attach_eq_some_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_ATTACH_EQ_SOME_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_ATTACH_EQ_SOME_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_ATTACH_EQ_SOME_MATCH_1_1_MODULE} must retain \\
         {OPTION_ATTACH_EQ_SOME_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_ATTACH_EQ_SOME_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_ATTACH_EQ_SOME_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_ATTACH_EQ_SOME_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_unattach_eq_some_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_unattach_eq_some_match_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_UNATTACH_EQ_SOME_IFF_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_UNATTACH_EQ_SOME_IFF_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_UNATTACH_EQ_SOME_IFF_MATCH_1_1_MODULE} must retain \\
         {OPTION_UNATTACH_EQ_SOME_IFF_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_UNATTACH_EQ_SOME_IFF_MATCH_1_1)
        .unwrap_or_else(|| {
            panic!("private decoder lost {OPTION_UNATTACH_EQ_SOME_IFF_MATCH_1_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_UNATTACH_EQ_SOME_IFF_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_attach_filter_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_attach_filter_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_ATTACH_FILTER_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_ATTACH_FILTER_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_ATTACH_FILTER_SIMP_1_1_MODULE} must retain \\
         {OPTION_ATTACH_FILTER_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_ATTACH_FILTER_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_ATTACH_FILTER_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_ATTACH_FILTER_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_attach_filter_second_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_attach_filter_second_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_ATTACH_FILTER_SIMP_1_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_ATTACH_FILTER_SIMP_1_2.to_owned()),
        "the private companion of {OPTION_ATTACH_FILTER_SIMP_1_2_MODULE} must retain \\
         {OPTION_ATTACH_FILTER_SIMP_1_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_ATTACH_FILTER_SIMP_1_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_ATTACH_FILTER_SIMP_1_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_ATTACH_FILTER_SIMP_1_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_attach_pfilter_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_attach_pfilter_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_ATTACH_PFILTER_SIMP_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_ATTACH_PFILTER_SIMP_2.to_owned()),
        "the private companion of {OPTION_ATTACH_PFILTER_SIMP_2_MODULE} must retain \\
         {OPTION_ATTACH_PFILTER_SIMP_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_ATTACH_PFILTER_SIMP_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_ATTACH_PFILTER_SIMP_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_ATTACH_PFILTER_SIMP_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_decidable_eq_first_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_decidable_eq_first_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_DECIDABLE_EQ_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_DECIDABLE_EQ_MATCH_1_EQ_1.to_owned()),
        "the private companion of {OPTION_DECIDABLE_EQ_MATCH_1_EQ_1_MODULE} must retain \\
         {OPTION_DECIDABLE_EQ_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_DECIDABLE_EQ_MATCH_1_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_DECIDABLE_EQ_MATCH_1_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_DECIDABLE_EQ_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_decidable_eq_second_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_decidable_eq_second_match_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_DECIDABLE_EQ_MATCH_1_EQ_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_DECIDABLE_EQ_MATCH_1_EQ_2.to_owned()),
        "the private companion of {OPTION_DECIDABLE_EQ_MATCH_1_EQ_2_MODULE} must retain \\
         {OPTION_DECIDABLE_EQ_MATCH_1_EQ_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_DECIDABLE_EQ_MATCH_1_EQ_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_DECIDABLE_EQ_MATCH_1_EQ_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_DECIDABLE_EQ_MATCH_1_EQ_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_decidable_eq_match_splitter_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_decidable_eq_match_splitter_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_ATTACH_DECIDABLE_EQ_MATCH_1_SPLITTER_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_ATTACH_DECIDABLE_EQ_MATCH_1_SPLITTER.to_owned()),
        "the private companion of {OPTION_ATTACH_DECIDABLE_EQ_MATCH_1_SPLITTER_MODULE} must retain \\
         {OPTION_ATTACH_DECIDABLE_EQ_MATCH_1_SPLITTER}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| {
            info.name().to_display_string() == OPTION_ATTACH_DECIDABLE_EQ_MATCH_1_SPLITTER
        })
        .unwrap_or_else(|| {
            panic!("private decoder lost {OPTION_ATTACH_DECIDABLE_EQ_MATCH_1_SPLITTER}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_ATTACH_DECIDABLE_EQ_MATCH_1_SPLITTER} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_lawful_monad_attach_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_lawful_monad_attach_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_LAWFUL_MONAD_ATTACH_SIMP_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_LAWFUL_MONAD_ATTACH_SIMP_1.to_owned()),
        "the private companion of {OPTION_LAWFUL_MONAD_ATTACH_SIMP_1_MODULE} must retain \\
         {OPTION_LAWFUL_MONAD_ATTACH_SIMP_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_LAWFUL_MONAD_ATTACH_SIMP_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_LAWFUL_MONAD_ATTACH_SIMP_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_LAWFUL_MONAD_ATTACH_SIMP_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_lawful_monad_attach_second_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_lawful_monad_attach_second_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_LAWFUL_MONAD_ATTACH_SIMP_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_LAWFUL_MONAD_ATTACH_SIMP_2.to_owned()),
        "the private companion of {OPTION_LAWFUL_MONAD_ATTACH_SIMP_2_MODULE} must retain \\
         {OPTION_LAWFUL_MONAD_ATTACH_SIMP_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_LAWFUL_MONAD_ATTACH_SIMP_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_LAWFUL_MONAD_ATTACH_SIMP_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_LAWFUL_MONAD_ATTACH_SIMP_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_is_none_choice_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_is_none_choice_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_IS_NONE_CHOICE_EQ_FALSE_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_NONE_CHOICE_EQ_FALSE_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_IS_NONE_CHOICE_EQ_FALSE_SIMP_1_1_MODULE} must retain \\
         {OPTION_IS_NONE_CHOICE_EQ_FALSE_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_NONE_CHOICE_EQ_FALSE_SIMP_1_1)
        .unwrap_or_else(|| {
            panic!("private decoder lost {OPTION_IS_NONE_CHOICE_EQ_FALSE_SIMP_1_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_IS_NONE_CHOICE_EQ_FALSE_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_is_none_merge_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_is_none_merge_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_IS_NONE_MERGE_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_NONE_MERGE_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_IS_NONE_MERGE_SIMP_1_1_MODULE} must retain \\
         {OPTION_IS_NONE_MERGE_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_NONE_MERGE_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_IS_NONE_MERGE_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_IS_NONE_MERGE_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_is_none_pfilter_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_is_none_pfilter_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_IS_NONE_PFILTER_IFF_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_NONE_PFILTER_IFF_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_1_MODULE} must retain \\
         {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_NONE_PFILTER_IFF_SIMP_1_1)
        .unwrap_or_else(|| {
            panic!("private decoder lost {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_is_none_pfilter_second_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_is_none_pfilter_second_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_IS_NONE_PFILTER_IFF_SIMP_1_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_NONE_PFILTER_IFF_SIMP_1_2.to_owned()),
        "the private companion of {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_2_MODULE} must retain \\
         {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_NONE_PFILTER_IFF_SIMP_1_2)
        .unwrap_or_else(|| {
            panic!("private decoder lost {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_2}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_is_none_pfilter_third_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_is_none_pfilter_third_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_IS_NONE_PFILTER_IFF_SIMP_1_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_NONE_PFILTER_IFF_SIMP_1_3.to_owned()),
        "the private companion of {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_3_MODULE} must retain \\
         {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_NONE_PFILTER_IFF_SIMP_1_3)
        .unwrap_or_else(|| {
            panic!("private decoder lost {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_3}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_IS_NONE_PFILTER_IFF_SIMP_1_3} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_is_some_merge_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_is_some_merge_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_IS_SOME_MERGE_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_SOME_MERGE_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_IS_SOME_MERGE_SIMP_1_1_MODULE} must retain \\
         {OPTION_IS_SOME_MERGE_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_SOME_MERGE_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_IS_SOME_MERGE_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_IS_SOME_MERGE_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_is_some_filter_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_is_some_filter_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_IS_SOME_FILTER_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_SOME_FILTER_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_IS_SOME_FILTER_MATCH_1_1_MODULE} must retain \\
         {OPTION_IS_SOME_FILTER_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_SOME_FILTER_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_IS_SOME_FILTER_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_IS_SOME_FILTER_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_is_some_filter_third_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_is_some_filter_third_match_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_IS_SOME_FILTER_MATCH_1_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_SOME_FILTER_MATCH_1_3.to_owned()),
        "the private companion of {OPTION_IS_SOME_FILTER_MATCH_1_3_MODULE} must retain \\
         {OPTION_IS_SOME_FILTER_MATCH_1_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_SOME_FILTER_MATCH_1_3)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_IS_SOME_FILTER_MATCH_1_3}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_IS_SOME_FILTER_MATCH_1_3} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_join_ne_none_second_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_join_ne_none_second_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_JOIN_NE_NONE_SIMP_1_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_JOIN_NE_NONE_SIMP_1_2.to_owned()),
        "the private companion of {OPTION_JOIN_NE_NONE_SIMP_1_2_MODULE} must retain \\
         {OPTION_JOIN_NE_NONE_SIMP_1_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_JOIN_NE_NONE_SIMP_1_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_JOIN_NE_NONE_SIMP_1_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_JOIN_NE_NONE_SIMP_1_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_le_first_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("option_le_first_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_LE_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_LE_MATCH_1_EQ_1.to_owned()),
        "the private companion of {OPTION_LE_MATCH_1_EQ_1_MODULE} must retain \\
         {OPTION_LE_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_LE_MATCH_1_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_LE_MATCH_1_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_LE_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_le_second_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("option_le_second_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_LE_MATCH_1_EQ_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_LE_MATCH_1_EQ_2.to_owned()),
        "the private companion of {OPTION_LE_MATCH_1_EQ_2_MODULE} must retain \\
         {OPTION_LE_MATCH_1_EQ_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_LE_MATCH_1_EQ_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_LE_MATCH_1_EQ_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_LE_MATCH_1_EQ_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_le_match_splitter_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("option_le_match_splitter_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_LE_MATCH_1_SPLITTER_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_LE_MATCH_1_SPLITTER.to_owned()),
        "the private companion of {OPTION_LE_MATCH_1_SPLITTER_MODULE} must retain \\
         {OPTION_LE_MATCH_1_SPLITTER}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_LE_MATCH_1_SPLITTER)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_LE_MATCH_1_SPLITTER}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_LE_MATCH_1_SPLITTER} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_pmap_first_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("option_pmap_first_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_PMAP_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PMAP_MATCH_1_EQ_1.to_owned()),
        "the private companion of {OPTION_PMAP_MATCH_1_EQ_1_MODULE} must retain \\
         {OPTION_PMAP_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PMAP_MATCH_1_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PMAP_MATCH_1_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_PMAP_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_pmap_second_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("option_pmap_second_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_PMAP_MATCH_1_EQ_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PMAP_MATCH_1_EQ_2.to_owned()),
        "the private companion of {OPTION_PMAP_MATCH_1_EQ_2_MODULE} must retain \\
         {OPTION_PMAP_MATCH_1_EQ_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PMAP_MATCH_1_EQ_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PMAP_MATCH_1_EQ_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_PMAP_MATCH_1_EQ_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_pmap_match_splitter_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_pmap_match_splitter_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_PMAP_MATCH_1_SPLITTER_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PMAP_MATCH_1_SPLITTER.to_owned()),
        "the private companion of {OPTION_PMAP_MATCH_1_SPLITTER_MODULE} must retain \\
         {OPTION_PMAP_MATCH_1_SPLITTER}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PMAP_MATCH_1_SPLITTER)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PMAP_MATCH_1_SPLITTER}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_PMAP_MATCH_1_SPLITTER} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_pmap_eq_some_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_pmap_eq_some_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_PMAP_EQ_SOME_IFF_SIMP_1_4_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PMAP_EQ_SOME_IFF_SIMP_1_4.to_owned()),
        "the private companion of {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_4_MODULE} must retain \\
         {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_4}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PMAP_EQ_SOME_IFF_SIMP_1_4)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_4}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_4} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_pmap_eq_some_second_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_pmap_eq_some_second_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_PMAP_EQ_SOME_IFF_SIMP_1_5_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PMAP_EQ_SOME_IFF_SIMP_1_5.to_owned()),
        "the private companion of {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_5_MODULE} must retain \\
         {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_5}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PMAP_EQ_SOME_IFF_SIMP_1_5)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_5}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_5} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_pfilter_first_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_pfilter_first_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_PFILTER_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PFILTER_MATCH_1_EQ_1.to_owned()),
        "the private companion of {OPTION_PFILTER_MATCH_1_EQ_1_MODULE} must retain \\
         {OPTION_PFILTER_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PFILTER_MATCH_1_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PFILTER_MATCH_1_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_PFILTER_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_pfilter_second_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_pfilter_second_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_PFILTER_MATCH_1_EQ_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PFILTER_MATCH_1_EQ_2.to_owned()),
        "the private companion of {OPTION_PFILTER_MATCH_1_EQ_2_MODULE} must retain \\
         {OPTION_PFILTER_MATCH_1_EQ_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PFILTER_MATCH_1_EQ_2)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PFILTER_MATCH_1_EQ_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_PFILTER_MATCH_1_EQ_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_pfilter_match_splitter_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_pfilter_match_splitter_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_PFILTER_MATCH_1_SPLITTER_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PFILTER_MATCH_1_SPLITTER.to_owned()),
        "the private companion of {OPTION_PFILTER_MATCH_1_SPLITTER_MODULE} must retain \\
         {OPTION_PFILTER_MATCH_1_SPLITTER}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PFILTER_MATCH_1_SPLITTER)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PFILTER_MATCH_1_SPLITTER}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_PFILTER_MATCH_1_SPLITTER} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_pfilter_eq_some_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_pfilter_eq_some_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_1_MODULE} must retain \\
         {OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_pfilter_eq_some_second_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_pfilter_eq_some_second_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_2.to_owned()),
        "the private companion of {OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_2_MODULE} must retain \\
         {OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_2)
        .unwrap_or_else(|| {
            panic!("private decoder lost {OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_2}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_PFILTER_EQ_SOME_IFF_SIMP_1_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_pmap_eq_some_third_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_pmap_eq_some_third_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_PMAP_EQ_SOME_IFF_SIMP_1_6_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_PMAP_EQ_SOME_IFF_SIMP_1_6.to_owned()),
        "the private companion of {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_6_MODULE} must retain \\
         {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_6}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_PMAP_EQ_SOME_IFF_SIMP_1_6)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_6}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_PMAP_EQ_SOME_IFF_SIMP_1_6} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_rel_some_some_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_rel_some_some_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_REL_SOME_SOME_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_REL_SOME_SOME_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_REL_SOME_SOME_MATCH_1_1_MODULE} must retain \\
         {OPTION_REL_SOME_SOME_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_REL_SOME_SOME_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_REL_SOME_SOME_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_REL_SOME_SOME_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_some_get_bang_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_some_get_bang_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_SOME_GET_BANG_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_SOME_GET_BANG_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_SOME_GET_BANG_MATCH_1_1_MODULE} must retain \\
         {OPTION_SOME_GET_BANG_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_SOME_GET_BANG_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_SOME_GET_BANG_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_SOME_GET_BANG_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_some_ne_none_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_some_ne_none_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_SOME_NE_NONE_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_SOME_NE_NONE_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_SOME_NE_NONE_MATCH_1_1_MODULE} must retain \\
         {OPTION_SOME_NE_NONE_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_SOME_NE_NONE_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_SOME_NE_NONE_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_SOME_NE_NONE_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_mem_to_list_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_mem_to_list_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_MEM_TO_LIST_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_MEM_TO_LIST_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_MEM_TO_LIST_SIMP_1_1_MODULE} must retain \\
         {OPTION_MEM_TO_LIST_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_MEM_TO_LIST_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_MEM_TO_LIST_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_MEM_TO_LIST_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_to_list_filter_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_to_list_filter_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_TO_LIST_FILTER_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_TO_LIST_FILTER_MATCH_1_1.to_owned()),
        "the private companion of {OPTION_TO_LIST_FILTER_MATCH_1_1_MODULE} must retain \\
         {OPTION_TO_LIST_FILTER_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_TO_LIST_FILTER_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_TO_LIST_FILTER_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_TO_LIST_FILTER_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_to_list_filter_second_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_to_list_filter_second_match_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_TO_LIST_FILTER_MATCH_1_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_TO_LIST_FILTER_MATCH_1_3.to_owned()),
        "the private companion of {OPTION_TO_LIST_FILTER_MATCH_1_3_MODULE} must retain \\
         {OPTION_TO_LIST_FILTER_MATCH_1_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_TO_LIST_FILTER_MATCH_1_3)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_TO_LIST_FILTER_MATCH_1_3}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_TO_LIST_FILTER_MATCH_1_3} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_to_list_join_simp_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("option_to_list_join_simp_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, OPTION_TO_LIST_JOIN_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_TO_LIST_JOIN_SIMP_1_1.to_owned()),
        "the private companion of {OPTION_TO_LIST_JOIN_SIMP_1_1_MODULE} must retain \\
         {OPTION_TO_LIST_JOIN_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_TO_LIST_JOIN_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_TO_LIST_JOIN_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_TO_LIST_JOIN_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_for_in_infer_membership_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_for_in_infer_membership_match_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_1.to_owned()),
        "the private companion of {OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_1_MODULE} must retain \\
         {OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_1)
        .unwrap_or_else(|| {
            panic!("private decoder lost {OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_1}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn option_for_in_infer_membership_second_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_for_in_infer_membership_second_match_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_2.to_owned()),
        "the private companion of {OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_2_MODULE} must retain \\
         {OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_2)
        .unwrap_or_else(|| {
            panic!("private decoder lost {OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_2}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {OPTION_FOR_IN_INFER_MEMBERSHIP_MATCH_1_EQ_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn list_has_dec_eq_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("list_has_dec_eq_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_HAS_DEC_EQ_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_HAS_DEC_EQ.to_owned()),
        "the private companion of {LIST_HAS_DEC_EQ_MODULE} must retain {LIST_HAS_DEC_EQ}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_HAS_DEC_EQ)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_HAS_DEC_EQ}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {LIST_HAS_DEC_EQ} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn list_has_dec_eq_third_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_has_dec_eq_third_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_HAS_DEC_EQ_MATCH_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_HAS_DEC_EQ_MATCH_3.to_owned()),
        "the private companion of {LIST_HAS_DEC_EQ_MATCH_3_MODULE} must retain \\
         {LIST_HAS_DEC_EQ_MATCH_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_HAS_DEC_EQ_MATCH_3)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_HAS_DEC_EQ_MATCH_3}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {LIST_HAS_DEC_EQ_MATCH_3} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn list_has_dec_eq_first_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_has_dec_eq_first_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_HAS_DEC_EQ_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_HAS_DEC_EQ_MATCH_1.to_owned()),
        "the private companion of {LIST_HAS_DEC_EQ_MATCH_1_MODULE} must retain \\
         {LIST_HAS_DEC_EQ_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_HAS_DEC_EQ_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_HAS_DEC_EQ_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {LIST_HAS_DEC_EQ_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn list_has_dec_eq_first_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_has_dec_eq_first_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_HAS_DEC_EQ_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_HAS_DEC_EQ_PROOF_1.to_owned()),
        "the private companion of {LIST_HAS_DEC_EQ_PROOF_1_MODULE} must retain \\
         {LIST_HAS_DEC_EQ_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_HAS_DEC_EQ_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_HAS_DEC_EQ_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {LIST_HAS_DEC_EQ_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn list_has_dec_eq_fifth_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("list_has_dec_eq_fifth_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, LIST_HAS_DEC_EQ_MATCH_5_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&LIST_HAS_DEC_EQ_MATCH_5.to_owned()),
        "the private companion of {LIST_HAS_DEC_EQ_MATCH_5_MODULE} must retain \\
         {LIST_HAS_DEC_EQ_MATCH_5}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == LIST_HAS_DEC_EQ_MATCH_5)
        .unwrap_or_else(|| panic!("private decoder lost {LIST_HAS_DEC_EQ_MATCH_5}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {LIST_HAS_DEC_EQ_MATCH_5} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_map_m_proof_auxiliaries_recover_with_concrete_kinds() {
    let lib = lib_or_skip!("array_map_m_proof_auxiliaries_recover_with_concrete_kinds");
    let chain = chain_bytes(&lib, "Init/Data/Array/BasicAux");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let private_constants = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode");

    for name in ARRAY_MAP_M_PROOF_AUXILIARIES {
        assert!(
            !exported_names.contains(&name.to_owned()),
            "the exported part must omit the private proof helper {name}"
        );
        assert!(
            private_names.contains(&name.to_owned()),
            "the private companion must restore the proof helper {name}"
        );
        assert!(
            exported_constants
                .iter()
                .all(|info| info.name().to_display_string() != name),
            "exported decoder unexpectedly recovered {name}"
        );
        let recovered = private_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("private decoder lost {name}"));
        assert!(
            is_concrete_recovery(recovered),
            "private companion decoded {name} only as {} instead of a concrete declaration",
            recovered.kind_name()
        );
    }
}

#[test]
fn prelude_name_beq_match_1_requires_the_companion_and_keeps_its_real_kind() {
    let lib =
        lib_or_skip!("prelude_name_beq_match_1_requires_the_companion_and_keeps_its_real_kind");
    let chain = chain_bytes(&lib, "Init/Prelude");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    assert!(
        !exported_names.contains(&NAME_BEQ_MATCH_1.to_owned()),
        "the exported Prelude part must omit {NAME_BEQ_MATCH_1}"
    );
    assert!(
        private_names.contains(&NAME_BEQ_MATCH_1.to_owned()),
        "the Prelude private companion must restore {NAME_BEQ_MATCH_1}"
    );

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != NAME_BEQ_MATCH_1),
        "exported decoder unexpectedly recovered {NAME_BEQ_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == NAME_BEQ_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {NAME_BEQ_MATCH_1}"));
    assert!(
        is_concrete_recovery(&recovered),
        "private companion decoded {NAME_BEQ_MATCH_1} only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn prelude_syntax_match_auxiliaries_recover_with_concrete_kinds() {
    let lib = lib_or_skip!("prelude_syntax_match_auxiliaries_recover_with_concrete_kinds");
    let chain = chain_bytes(&lib, "Init/Prelude");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let private_constants = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode");

    for name in SYNTAX_MATCH_AUXILIARIES {
        assert!(
            !exported_names.contains(&name.to_owned()),
            "the exported Prelude part must omit the private match helper {name}"
        );
        assert!(
            private_names.contains(&name.to_owned()),
            "the Prelude private companion must restore the match helper {name}"
        );
        assert!(
            exported_constants
                .iter()
                .all(|info| info.name().to_display_string() != name),
            "exported decoder unexpectedly recovered {name}"
        );
        let recovered = private_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("private decoder lost {name}"));
        assert!(
            is_concrete_recovery(recovered),
            "private companion decoded {name} only as {} instead of a concrete declaration",
            recovered.kind_name()
        );
    }
}

#[test]
fn string_extra_exported_mangled_unsafe_rec_helpers_remain_concrete() {
    let lib = lib_or_skip!("string_extra_exported_mangled_unsafe_rec_helpers_remain_concrete");
    let chain = chain_bytes(&lib, "Init/Data/String/Extra");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let private_constants = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode");

    for name in STRING_EXTRA_EXPORTED_UNSAFE_RECS {
        assert!(
            exported_names.contains(&name.to_owned()),
            "the exported String.Extra part must retain its private-mangled helper {name}"
        );
        assert!(
            private_names.contains(&name.to_owned()),
            "the private chain must retain the exported helper {name}"
        );
        let exported = exported_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("exported decoder lost {name}"));
        assert!(
            is_concrete_recovery(exported),
            "exported decoder decoded {name} only as {} instead of a concrete declaration",
            exported.kind_name()
        );
        let chained = private_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("private chain lost exported helper {name}"));
        assert!(
            is_concrete_recovery(chained),
            "private chain decoded {name} only as {} instead of a concrete declaration",
            chained.kind_name()
        );
    }
}

#[test]
fn string_remove_leading_spaces_exported_mangled_helpers_remain_concrete() {
    let lib = lib_or_skip!("string_remove_leading_spaces_exported_mangled_helpers_remain_concrete");
    let chain = chain_bytes(&lib, "Init/Data/String/Extra");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let private_constants = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode");

    for name in STRING_REMOVE_LEADING_SPACES_EXPORTED_UNSAFE_RECS {
        assert!(
            exported_names.contains(&name.to_owned()),
            "the exported String.Extra part must retain its private-mangled helper {name}"
        );
        assert!(
            private_names.contains(&name.to_owned()),
            "the private chain must retain the exported helper {name}"
        );
        let exported = exported_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("exported decoder lost {name}"));
        assert!(
            is_concrete_recovery(exported),
            "exported decoder decoded {name} only as {} instead of a concrete declaration",
            exported.kind_name()
        );
        let chained = private_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("private chain lost exported helper {name}"));
        assert!(
            is_concrete_recovery(chained),
            "private chain decoded {name} only as {} instead of a concrete declaration",
            chained.kind_name()
        );
    }
}

#[test]
fn array_basic_insert_idx_loop_unary_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!(
        "array_basic_insert_idx_loop_unary_requires_the_companion_and_keeps_its_real_kind"
    );
    let chain = chain_bytes(&lib, INSERT_IDX_LOOP_UNARY_MODULE);
    let (exported_names, private_names) = exported_and_private_names(&chain);

    assert!(
        !exported_names.contains(&INSERT_IDX_LOOP_UNARY.to_owned()),
        "the exported part of {INSERT_IDX_LOOP_UNARY_MODULE} must omit {INSERT_IDX_LOOP_UNARY}"
    );
    assert!(
        private_names.contains(&INSERT_IDX_LOOP_UNARY.to_owned()),
        "the private companion of {INSERT_IDX_LOOP_UNARY_MODULE} must restore {INSERT_IDX_LOOP_UNARY}"
    );

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != INSERT_IDX_LOOP_UNARY),
        "exported decoder unexpectedly recovered {INSERT_IDX_LOOP_UNARY}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == INSERT_IDX_LOOP_UNARY)
        .unwrap_or_else(|| panic!("private decoder lost {INSERT_IDX_LOOP_UNARY}"));
    assert!(
        is_concrete_recovery(&recovered),
        "private companion decoded {INSERT_IDX_LOOP_UNARY} only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn array_insert_idx_loop_unary_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_insert_idx_loop_unary_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, INSERT_IDX_LOOP_UNARY_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&INSERT_IDX_LOOP_UNARY_PROOF_1.to_owned()),
        "the private companion of {INSERT_IDX_LOOP_UNARY_PROOF_1_MODULE} must retain \
         {INSERT_IDX_LOOP_UNARY_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == INSERT_IDX_LOOP_UNARY_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {INSERT_IDX_LOOP_UNARY_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {INSERT_IDX_LOOP_UNARY_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_insert_idx_loop_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_insert_idx_loop_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, INSERT_IDX_LOOP_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&INSERT_IDX_LOOP_PROOF_1.to_owned()),
        "the private companion of {INSERT_IDX_LOOP_PROOF_1_MODULE} must retain \
         {INSERT_IDX_LOOP_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == INSERT_IDX_LOOP_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {INSERT_IDX_LOOP_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {INSERT_IDX_LOOP_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_insert_idx_loop_second_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_insert_idx_loop_second_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, INSERT_IDX_LOOP_PROOF_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&INSERT_IDX_LOOP_PROOF_2.to_owned()),
        "the private companion of {INSERT_IDX_LOOP_PROOF_2_MODULE} must retain \
         {INSERT_IDX_LOOP_PROOF_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == INSERT_IDX_LOOP_PROOF_2)
        .unwrap_or_else(|| panic!("private decoder lost {INSERT_IDX_LOOP_PROOF_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {INSERT_IDX_LOOP_PROOF_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_insert_idx_loop_third_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_insert_idx_loop_third_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, INSERT_IDX_LOOP_PROOF_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&INSERT_IDX_LOOP_PROOF_3.to_owned()),
        "the private companion of {INSERT_IDX_LOOP_PROOF_3_MODULE} must retain \
         {INSERT_IDX_LOOP_PROOF_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == INSERT_IDX_LOOP_PROOF_3)
        .unwrap_or_else(|| panic!("private decoder lost {INSERT_IDX_LOOP_PROOF_3}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {INSERT_IDX_LOOP_PROOF_3} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_zip_with_m_aux_unary_requires_the_companion_and_keeps_its_real_kind() {
    let lib =
        lib_or_skip!("array_zip_with_m_aux_unary_requires_the_companion_and_keeps_its_real_kind");
    let chain = chain_bytes(&lib, INSERT_IDX_LOOP_UNARY_MODULE);
    let (exported_names, _) = exported_and_private_names(&chain);

    assert!(
        exported_names.contains(&ARRAY_ZIP_WITH_M_AUX_UNARY.to_owned()),
        "the exported part of {INSERT_IDX_LOOP_UNARY_MODULE} must retain the shell {ARRAY_ZIP_WITH_M_AUX_UNARY}"
    );

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ZIP_WITH_M_AUX_UNARY)
        .unwrap_or_else(|| panic!("exported decoder lost {ARRAY_ZIP_WITH_M_AUX_UNARY}"));
    assert!(
        matches!(exported, ConstantInfo::Axiom(_)),
        "the exported shell {ARRAY_ZIP_WITH_M_AUX_UNARY} must remain an axiom at the pin"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ZIP_WITH_M_AUX_UNARY)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ZIP_WITH_M_AUX_UNARY}"));
    assert!(
        is_concrete_recovery(&recovered),
        "chain decode of {ARRAY_ZIP_WITH_M_AUX_UNARY} produced only {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn array_zip_with_m_aux_unary_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_zip_with_m_aux_unary_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ZIP_WITH_M_AUX_UNARY_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ZIP_WITH_M_AUX_UNARY_PROOF_1.to_owned()),
        "the private companion of {ARRAY_ZIP_WITH_M_AUX_UNARY_PROOF_1_MODULE} must retain \
         {ARRAY_ZIP_WITH_M_AUX_UNARY_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ZIP_WITH_M_AUX_UNARY_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ZIP_WITH_M_AUX_UNARY_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ZIP_WITH_M_AUX_UNARY_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_zip_with_m_aux_unary_equation_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_zip_with_m_aux_unary_equation_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ZIP_WITH_M_AUX_UNARY_EQ_DEF_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ZIP_WITH_M_AUX_UNARY_EQ_DEF.to_owned()),
        "the private companion of {ARRAY_ZIP_WITH_M_AUX_UNARY_EQ_DEF_MODULE} must retain \
         {ARRAY_ZIP_WITH_M_AUX_UNARY_EQ_DEF}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ZIP_WITH_M_AUX_UNARY_EQ_DEF)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ZIP_WITH_M_AUX_UNARY_EQ_DEF}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ZIP_WITH_M_AUX_UNARY_EQ_DEF} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn nat_gcd_unary_proof_requires_the_companion_and_remains_a_theorem() {
    let lib = lib_or_skip!("nat_gcd_unary_proof_requires_the_companion_and_remains_a_theorem");
    let chain = chain_bytes(&lib, "Init/Data/Nat/Gcd");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    assert!(
        !exported_names.contains(&NAT_GCD_UNARY_PROOF_1.to_owned()),
        "the exported Nat gcd interface must omit {NAT_GCD_UNARY_PROOF_1}"
    );
    assert!(
        private_names.contains(&NAT_GCD_UNARY_PROOF_1.to_owned()),
        "the Nat gcd private companion must retain {NAT_GCD_UNARY_PROOF_1}"
    );

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != NAT_GCD_UNARY_PROOF_1),
        "exported decoder unexpectedly recovered {NAT_GCD_UNARY_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == NAT_GCD_UNARY_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {NAT_GCD_UNARY_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {NAT_GCD_UNARY_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_of_fn_go_congr_simp_is_decoded_from_its_actual_private_storage_module() {
    let lib = lib_or_skip!(
        "array_of_fn_go_congr_simp_is_decoded_from_its_actual_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_OF_FN_GO_CONGR_SIMP_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_OF_FN_GO_CONGR_SIMP.to_owned()),
        "the private companion of {ARRAY_OF_FN_GO_CONGR_SIMP_MODULE} must retain \
         {ARRAY_OF_FN_GO_CONGR_SIMP}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_OF_FN_GO_CONGR_SIMP)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_OF_FN_GO_CONGR_SIMP}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_OF_FN_GO_CONGR_SIMP} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_foldl_attach_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_foldl_attach_simp_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_FOLDL_ATTACH_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_FOLDL_ATTACH_SIMP_1_1.to_owned()),
        "the private companion of {ARRAY_FOLDL_ATTACH_SIMP_1_1_MODULE} must retain \
         {ARRAY_FOLDL_ATTACH_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_FOLDL_ATTACH_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_FOLDL_ATTACH_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_FOLDL_ATTACH_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_foldr_attach_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_foldr_attach_simp_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_FOLDR_ATTACH_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_FOLDR_ATTACH_SIMP_1_1.to_owned()),
        "the private companion of {ARRAY_FOLDR_ATTACH_SIMP_1_1_MODULE} must retain \
         {ARRAY_FOLDR_ATTACH_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_FOLDR_ATTACH_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_FOLDR_ATTACH_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_FOLDR_ATTACH_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_mem_attach_match_definition_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_mem_attach_match_definition_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_MEM_ATTACH_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MEM_ATTACH_MATCH_1_1.to_owned()),
        "the private companion of {ARRAY_MEM_ATTACH_MATCH_1_1_MODULE} must retain \
         {ARRAY_MEM_ATTACH_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MEM_ATTACH_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MEM_ATTACH_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_MEM_ATTACH_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_pmap_impl_match_definition_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_pmap_impl_match_definition_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_PMAP_IMPL_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_PMAP_IMPL_MATCH_1.to_owned()),
        "the private companion of {ARRAY_PMAP_IMPL_MATCH_1_MODULE} must retain \
         {ARRAY_PMAP_IMPL_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_PMAP_IMPL_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_PMAP_IMPL_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_PMAP_IMPL_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_pmap_congr_left_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_pmap_congr_left_simp_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_PMAP_CONGR_LEFT_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_PMAP_CONGR_LEFT_SIMP_1_1.to_owned()),
        "the private companion of {ARRAY_PMAP_CONGR_LEFT_SIMP_1_1_MODULE} must retain \
         {ARRAY_PMAP_CONGR_LEFT_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_PMAP_CONGR_LEFT_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_PMAP_CONGR_LEFT_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_PMAP_CONGR_LEFT_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_pmap_eq_self_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_pmap_eq_self_simp_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_PMAP_EQ_SELF_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_PMAP_EQ_SELF_SIMP_1_1.to_owned()),
        "the private companion of {ARRAY_PMAP_EQ_SELF_SIMP_1_1_MODULE} must retain \
         {ARRAY_PMAP_EQ_SELF_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_PMAP_EQ_SELF_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_PMAP_EQ_SELF_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_PMAP_EQ_SELF_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_pmap_push_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_pmap_push_simp_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_PMAP_PUSH_SIMP_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_PMAP_PUSH_SIMP_1.to_owned()),
        "the private companion of {ARRAY_PMAP_PUSH_SIMP_1_MODULE} must retain \
         {ARRAY_PMAP_PUSH_SIMP_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_PMAP_PUSH_SIMP_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_PMAP_PUSH_SIMP_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_PMAP_PUSH_SIMP_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_to_list_attach_with_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_to_list_attach_with_simp_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_TO_LIST_ATTACH_WITH_SIMP_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_TO_LIST_ATTACH_WITH_SIMP_1.to_owned()),
        "the private companion of {ARRAY_TO_LIST_ATTACH_WITH_SIMP_1_MODULE} must retain \
         {ARRAY_TO_LIST_ATTACH_WITH_SIMP_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_TO_LIST_ATTACH_WITH_SIMP_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_TO_LIST_ATTACH_WITH_SIMP_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_TO_LIST_ATTACH_WITH_SIMP_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_mem_unattach_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_mem_unattach_simp_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_MEM_UNATTACH_SIMP_1_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MEM_UNATTACH_SIMP_1_2.to_owned()),
        "the private companion of {ARRAY_MEM_UNATTACH_SIMP_1_2_MODULE} must retain \
         {ARRAY_MEM_UNATTACH_SIMP_1_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MEM_UNATTACH_SIMP_1_2)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MEM_UNATTACH_SIMP_1_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_MEM_UNATTACH_SIMP_1_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_mem_pmap_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_mem_pmap_simp_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MEM_PMAP_SIMP_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MEM_PMAP_SIMP_1_1.to_owned()),
        "the private companion of {ARRAY_MEM_PMAP_SIMP_1_1_MODULE} must retain \
         {ARRAY_MEM_PMAP_SIMP_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MEM_PMAP_SIMP_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MEM_PMAP_SIMP_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_MEM_PMAP_SIMP_1_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_mem_pmap_second_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_mem_pmap_second_simp_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_MEM_PMAP_SIMP_1_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MEM_PMAP_SIMP_1_2.to_owned()),
        "the private companion of {ARRAY_MEM_PMAP_SIMP_1_2_MODULE} must retain \
         {ARRAY_MEM_PMAP_SIMP_1_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MEM_PMAP_SIMP_1_2)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MEM_PMAP_SIMP_1_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_MEM_PMAP_SIMP_1_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_mem_pmap_third_simp_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_mem_pmap_third_simp_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_MEM_PMAP_SIMP_1_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MEM_PMAP_SIMP_1_3.to_owned()),
        "the private companion of {ARRAY_MEM_PMAP_SIMP_1_3_MODULE} must retain \
         {ARRAY_MEM_PMAP_SIMP_1_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MEM_PMAP_SIMP_1_3)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MEM_PMAP_SIMP_1_3}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_MEM_PMAP_SIMP_1_3} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_attach_with_impl_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_attach_with_impl_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ATTACH_WITH_IMPL_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ATTACH_WITH_IMPL.to_owned()),
        "the private companion of {ARRAY_ATTACH_WITH_IMPL_MODULE} must retain \
         {ARRAY_ATTACH_WITH_IMPL}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ATTACH_WITH_IMPL)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ATTACH_WITH_IMPL}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ATTACH_WITH_IMPL} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_unattach_equation_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_unattach_equation_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_UNATTACH_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_UNATTACH_EQ_1.to_owned()),
        "the private companion of {ARRAY_UNATTACH_EQ_1_MODULE} must retain {ARRAY_UNATTACH_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_UNATTACH_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_UNATTACH_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_UNATTACH_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_all_diff_aux_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_all_diff_aux_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ALL_DIFF_AUX.to_owned()),
        "the private companion of {ARRAY_ALL_DIFF_AUX_MODULE} must retain {ARRAY_ALL_DIFF_AUX}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ALL_DIFF_AUX)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ALL_DIFF_AUX}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ALL_DIFF_AUX} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_all_diff_aux_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_all_diff_aux_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ALL_DIFF_AUX_PROOF_1.to_owned()),
        "the private companion of {ARRAY_ALL_DIFF_AUX_PROOF_1_MODULE} must retain \
         {ARRAY_ALL_DIFF_AUX_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ALL_DIFF_AUX_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ALL_DIFF_AUX_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ALL_DIFF_AUX_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_all_diff_aux_unsafe_rec_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_all_diff_aux_unsafe_rec_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_UNSAFE_REC_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ALL_DIFF_AUX_UNSAFE_REC.to_owned()),
        "the private companion of {ARRAY_ALL_DIFF_AUX_UNSAFE_REC_MODULE} must retain \
         {ARRAY_ALL_DIFF_AUX_UNSAFE_REC}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ALL_DIFF_AUX_UNSAFE_REC)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ALL_DIFF_AUX_UNSAFE_REC}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ALL_DIFF_AUX_UNSAFE_REC} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_any_m_unsafe_any_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_any_m_unsafe_any_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ANY_M_UNSAFE_ANY_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ANY_M_UNSAFE_ANY.to_owned()),
        "the private companion of {ARRAY_ANY_M_UNSAFE_ANY_MODULE} must retain \
         {ARRAY_ANY_M_UNSAFE_ANY}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ANY_M_UNSAFE_ANY)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ANY_M_UNSAFE_ANY}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ANY_M_UNSAFE_ANY} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_back_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_back_proof_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_BACK_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_BACK_PROOF_1.to_owned()),
        "the private companion of {ARRAY_BACK_PROOF_1_MODULE} must retain {ARRAY_BACK_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_BACK_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_BACK_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_BACK_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_erase_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_erase_proof_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ERASE_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ERASE_PROOF_1.to_owned()),
        "the private companion of {ARRAY_ERASE_PROOF_1_MODULE} must retain {ARRAY_ERASE_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ERASE_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ERASE_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ERASE_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_erase_match_definition_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_erase_match_definition_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ERASE_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ERASE_MATCH_1.to_owned()),
        "the private companion of {ARRAY_ERASE_MATCH_1_MODULE} must retain {ARRAY_ERASE_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ERASE_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ERASE_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ERASE_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_erase_idx_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_erase_idx_proof_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ERASE_IDX_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ERASE_IDX_PROOF_1.to_owned()),
        "the private companion of {ARRAY_ERASE_IDX_PROOF_1_MODULE} must retain \
         {ARRAY_ERASE_IDX_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ERASE_IDX_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ERASE_IDX_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ERASE_IDX_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_erase_idx_unary_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_erase_idx_unary_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ERASE_IDX_UNARY_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ERASE_IDX_UNARY_PROOF_1.to_owned()),
        "the private companion of {ARRAY_ERASE_IDX_UNARY_PROOF_1_MODULE} must retain \
         {ARRAY_ERASE_IDX_UNARY_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ERASE_IDX_UNARY_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ERASE_IDX_UNARY_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ERASE_IDX_UNARY_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_erase_idx_unary_second_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_erase_idx_unary_second_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ERASE_IDX_UNARY_PROOF_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ERASE_IDX_UNARY_PROOF_2.to_owned()),
        "the private companion of {ARRAY_ERASE_IDX_UNARY_PROOF_2_MODULE} must retain \
         {ARRAY_ERASE_IDX_UNARY_PROOF_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ERASE_IDX_UNARY_PROOF_2)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ERASE_IDX_UNARY_PROOF_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ERASE_IDX_UNARY_PROOF_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_erase_idx_unary_third_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_erase_idx_unary_third_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ERASE_IDX_UNARY_PROOF_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ERASE_IDX_UNARY_PROOF_3.to_owned()),
        "the private companion of {ARRAY_ERASE_IDX_UNARY_PROOF_3_MODULE} must retain \
         {ARRAY_ERASE_IDX_UNARY_PROOF_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ERASE_IDX_UNARY_PROOF_3)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ERASE_IDX_UNARY_PROOF_3}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ERASE_IDX_UNARY_PROOF_3} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_erase_idx_unary_fourth_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_erase_idx_unary_fourth_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ERASE_IDX_UNARY_PROOF_4_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ERASE_IDX_UNARY_PROOF_4.to_owned()),
        "the private companion of {ARRAY_ERASE_IDX_UNARY_PROOF_4_MODULE} must retain \
         {ARRAY_ERASE_IDX_UNARY_PROOF_4}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ERASE_IDX_UNARY_PROOF_4)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ERASE_IDX_UNARY_PROOF_4}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ERASE_IDX_UNARY_PROOF_4} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_erase_reps_match_definition_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_erase_reps_match_definition_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ERASE_REPS_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ERASE_REPS_MATCH_1.to_owned()),
        "the private companion of {ARRAY_ERASE_REPS_MATCH_1_MODULE} must retain \
         {ARRAY_ERASE_REPS_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ERASE_REPS_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ERASE_REPS_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ERASE_REPS_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_ext_aux_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_ext_aux_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_EXT_AUX_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_EXT_AUX.to_owned()),
        "the private companion of {ARRAY_EXT_AUX_MODULE} must retain {ARRAY_EXT_AUX}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_EXT_AUX)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_EXT_AUX}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_EXT_AUX} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_find_fin_idx_loop_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_find_fin_idx_loop_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_FIND_FIN_IDX_LOOP_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_FIND_FIN_IDX_LOOP.to_owned()),
        "the private companion of {ARRAY_FIND_FIN_IDX_LOOP_MODULE} must retain \
         {ARRAY_FIND_FIN_IDX_LOOP}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_FIND_FIN_IDX_LOOP)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_FIND_FIN_IDX_LOOP}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_FIND_FIN_IDX_LOOP} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_find_idx_loop_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_find_idx_loop_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_FIND_IDX_LOOP_EQ_MAP_FIND_FIN_IDX_LOOP_VAL_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_FIND_IDX_LOOP_EQ_MAP_FIND_FIN_IDX_LOOP_VAL.to_owned()),
        "the private companion of {ARRAY_FIND_IDX_LOOP_EQ_MAP_FIND_FIN_IDX_LOOP_VAL_MODULE} must retain \
         {ARRAY_FIND_IDX_LOOP_EQ_MAP_FIND_FIN_IDX_LOOP_VAL}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| {
            info.name().to_display_string() == ARRAY_FIND_IDX_LOOP_EQ_MAP_FIND_FIN_IDX_LOOP_VAL
        })
        .unwrap_or_else(|| {
            panic!("private decoder lost {ARRAY_FIND_IDX_LOOP_EQ_MAP_FIND_FIN_IDX_LOOP_VAL}")
        });
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_FIND_IDX_LOOP_EQ_MAP_FIND_FIN_IDX_LOOP_VAL} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_find_some_rev_m_find_f_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_find_some_rev_m_find_f_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_FIND_SOME_REV_M_FIND_F_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_FIND_SOME_REV_M_FIND_F.to_owned()),
        "the private companion of {ARRAY_FIND_SOME_REV_M_FIND_F_MODULE} must retain \
         {ARRAY_FIND_SOME_REV_M_FIND_F}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_FIND_SOME_REV_M_FIND_F)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_FIND_SOME_REV_M_FIND_F}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_FIND_SOME_REV_M_FIND_F} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_first_m_go_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_first_m_go_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_FIRST_M_GO_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_FIRST_M_GO.to_owned()),
        "the private companion of {ARRAY_FIRST_M_GO_MODULE} must retain {ARRAY_FIRST_M_GO}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_FIRST_M_GO)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_FIRST_M_GO}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_FIRST_M_GO} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_foldl_m_unsafe_fold_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_foldl_m_unsafe_fold_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_FOLDL_M_UNSAFE_FOLD_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_FOLDL_M_UNSAFE_FOLD.to_owned()),
        "the private companion of {ARRAY_FOLDL_M_UNSAFE_FOLD_MODULE} must retain \
         {ARRAY_FOLDL_M_UNSAFE_FOLD}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_FOLDL_M_UNSAFE_FOLD)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_FOLDL_M_UNSAFE_FOLD}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_FOLDL_M_UNSAFE_FOLD} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_foldr_m_unsafe_fold_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_foldr_m_unsafe_fold_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_FOLDR_M_UNSAFE_FOLD_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_FOLDR_M_UNSAFE_FOLD.to_owned()),
        "the private companion of {ARRAY_FOLDR_M_UNSAFE_FOLD_MODULE} must retain \
         {ARRAY_FOLDR_M_UNSAFE_FOLD}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_FOLDR_M_UNSAFE_FOLD)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_FOLDR_M_UNSAFE_FOLD}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_FOLDR_M_UNSAFE_FOLD} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_for_in_unsafe_loop_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_for_in_unsafe_loop_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_FOR_IN_UNSAFE_LOOP_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_FOR_IN_UNSAFE_LOOP.to_owned()),
        "the private companion of {ARRAY_FOR_IN_UNSAFE_LOOP_MODULE} must retain \
         {ARRAY_FOR_IN_UNSAFE_LOOP}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_FOR_IN_UNSAFE_LOOP)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_FOR_IN_UNSAFE_LOOP}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_FOR_IN_UNSAFE_LOOP} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_map_m_unsafe_map_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_map_m_unsafe_map_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MAP_M_UNSAFE_MAP_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MAP_M_UNSAFE_MAP.to_owned()),
        "the private companion of {ARRAY_MAP_M_UNSAFE_MAP_MODULE} must retain \
         {ARRAY_MAP_M_UNSAFE_MAP}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MAP_M_UNSAFE_MAP)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MAP_M_UNSAFE_MAP}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_MAP_M_UNSAFE_MAP} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_get_even_elems_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_get_even_elems_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_GET_EVEN_ELEMS_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_GET_EVEN_ELEMS_MATCH_1.to_owned()),
        "the private companion of {ARRAY_GET_EVEN_ELEMS_MATCH_1_MODULE} must retain \
         {ARRAY_GET_EVEN_ELEMS_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_GET_EVEN_ELEMS_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_GET_EVEN_ELEMS_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_GET_EVEN_ELEMS_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_idx_of_aux_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_idx_of_aux_proof_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_IDX_OF_AUX_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IDX_OF_AUX_PROOF_1.to_owned()),
        "the private companion of {ARRAY_IDX_OF_AUX_PROOF_1_MODULE} must retain \
         {ARRAY_IDX_OF_AUX_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IDX_OF_AUX_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IDX_OF_AUX_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_IDX_OF_AUX_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_is_eqv_aux_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_is_eqv_aux_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_IS_EQV_AUX_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IS_EQV_AUX_MATCH_1.to_owned()),
        "the private companion of {ARRAY_IS_EQV_AUX_MATCH_1_MODULE} must retain \
         {ARRAY_IS_EQV_AUX_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IS_EQV_AUX_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IS_EQV_AUX_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_IS_EQV_AUX_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_is_eqv_aux_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_is_eqv_aux_proof_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_IS_EQV_AUX_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IS_EQV_AUX_PROOF_1.to_owned()),
        "the private companion of {ARRAY_IS_EQV_AUX_PROOF_1_MODULE} must retain \
         {ARRAY_IS_EQV_AUX_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IS_EQV_AUX_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IS_EQV_AUX_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_IS_EQV_AUX_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_is_eqv_aux_second_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_is_eqv_aux_second_proof_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_IS_EQV_AUX_PROOF_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IS_EQV_AUX_PROOF_2.to_owned()),
        "the private companion of {ARRAY_IS_EQV_AUX_PROOF_2_MODULE} must retain \
         {ARRAY_IS_EQV_AUX_PROOF_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IS_EQV_AUX_PROOF_2)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IS_EQV_AUX_PROOF_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_IS_EQV_AUX_PROOF_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_is_eqv_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_is_eqv_proof_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_IS_EQV_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IS_EQV_PROOF_1.to_owned()),
        "the private companion of {ARRAY_IS_EQV_PROOF_1_MODULE} must retain {ARRAY_IS_EQV_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IS_EQV_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IS_EQV_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_IS_EQV_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_is_prefix_of_aux_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_is_prefix_of_aux_proof_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_IS_PREFIX_OF_AUX_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IS_PREFIX_OF_AUX_PROOF_1.to_owned()),
        "the private companion of {ARRAY_IS_PREFIX_OF_AUX_PROOF_1_MODULE} must retain \
         {ARRAY_IS_PREFIX_OF_AUX_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IS_PREFIX_OF_AUX_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IS_PREFIX_OF_AUX_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_IS_PREFIX_OF_AUX_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_is_prefix_of_aux_second_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_is_prefix_of_aux_second_proof_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_IS_PREFIX_OF_AUX_PROOF_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IS_PREFIX_OF_AUX_PROOF_2.to_owned()),
        "the private companion of {ARRAY_IS_PREFIX_OF_AUX_PROOF_2_MODULE} must retain \
         {ARRAY_IS_PREFIX_OF_AUX_PROOF_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IS_PREFIX_OF_AUX_PROOF_2)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IS_PREFIX_OF_AUX_PROOF_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_IS_PREFIX_OF_AUX_PROOF_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_is_prefix_of_aux_third_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_is_prefix_of_aux_third_proof_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_IS_PREFIX_OF_AUX_PROOF_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IS_PREFIX_OF_AUX_PROOF_3.to_owned()),
        "the private companion of {ARRAY_IS_PREFIX_OF_AUX_PROOF_3_MODULE} must retain \
         {ARRAY_IS_PREFIX_OF_AUX_PROOF_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IS_PREFIX_OF_AUX_PROOF_3)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IS_PREFIX_OF_AUX_PROOF_3}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_IS_PREFIX_OF_AUX_PROOF_3} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_is_prefix_of_aux_fourth_proof_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_is_prefix_of_aux_fourth_proof_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_IS_PREFIX_OF_AUX_PROOF_4_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IS_PREFIX_OF_AUX_PROOF_4.to_owned()),
        "the private companion of {ARRAY_IS_PREFIX_OF_AUX_PROOF_4_MODULE} must retain \
         {ARRAY_IS_PREFIX_OF_AUX_PROOF_4}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IS_PREFIX_OF_AUX_PROOF_4)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IS_PREFIX_OF_AUX_PROOF_4}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_IS_PREFIX_OF_AUX_PROOF_4} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_is_prefix_of_aux_equation_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_is_prefix_of_aux_equation_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_IS_PREFIX_OF_AUX_EQ_DEF_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_IS_PREFIX_OF_AUX_EQ_DEF.to_owned()),
        "the private companion of {ARRAY_IS_PREFIX_OF_AUX_EQ_DEF_MODULE} must retain \
         {ARRAY_IS_PREFIX_OF_AUX_EQ_DEF}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_IS_PREFIX_OF_AUX_EQ_DEF)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_IS_PREFIX_OF_AUX_EQ_DEF}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_IS_PREFIX_OF_AUX_EQ_DEF} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_all_diff_aux_aux_helper_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_all_diff_aux_aux_helper_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_AUX_F_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ALL_DIFF_AUX_AUX_F.to_owned()),
        "the private companion of {ARRAY_ALL_DIFF_AUX_AUX_F_MODULE} must retain \
         {ARRAY_ALL_DIFF_AUX_AUX_F}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ALL_DIFF_AUX_AUX_F)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ALL_DIFF_AUX_AUX_F}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ALL_DIFF_AUX_AUX_F} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_all_diff_aux_aux_proof_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_all_diff_aux_aux_proof_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_AUX_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ALL_DIFF_AUX_AUX_PROOF_1.to_owned()),
        "the private companion of {ARRAY_ALL_DIFF_AUX_AUX_PROOF_1_MODULE} must retain \
         {ARRAY_ALL_DIFF_AUX_AUX_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ALL_DIFF_AUX_AUX_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ALL_DIFF_AUX_AUX_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ALL_DIFF_AUX_AUX_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_all_diff_aux_aux_sunfold_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_all_diff_aux_aux_sunfold_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_AUX_SUNFOLD_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ALL_DIFF_AUX_AUX_SUNFOLD.to_owned()),
        "the private companion of {ARRAY_ALL_DIFF_AUX_AUX_SUNFOLD_MODULE} must retain \
         {ARRAY_ALL_DIFF_AUX_AUX_SUNFOLD}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ALL_DIFF_AUX_AUX_SUNFOLD)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ALL_DIFF_AUX_AUX_SUNFOLD}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ALL_DIFF_AUX_AUX_SUNFOLD} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_all_diff_aux_aux_unsafe_rec_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_all_diff_aux_aux_unsafe_rec_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_AUX_UNSAFE_REC_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ALL_DIFF_AUX_AUX_UNSAFE_REC.to_owned()),
        "the private companion of {ARRAY_ALL_DIFF_AUX_AUX_UNSAFE_REC_MODULE} must retain \
         {ARRAY_ALL_DIFF_AUX_AUX_UNSAFE_REC}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ALL_DIFF_AUX_AUX_UNSAFE_REC)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ALL_DIFF_AUX_AUX_UNSAFE_REC}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ALL_DIFF_AUX_AUX_UNSAFE_REC} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_all_diff_aux_aux_congr_simp_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_all_diff_aux_aux_congr_simp_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_AUX_CONGR_SIMP_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ALL_DIFF_AUX_AUX_CONGR_SIMP.to_owned()),
        "the private companion of {ARRAY_ALL_DIFF_AUX_AUX_CONGR_SIMP_MODULE} must retain \
         {ARRAY_ALL_DIFF_AUX_AUX_CONGR_SIMP}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ALL_DIFF_AUX_AUX_CONGR_SIMP)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ALL_DIFF_AUX_AUX_CONGR_SIMP}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_ALL_DIFF_AUX_AUX_CONGR_SIMP} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_all_diff_aux_aux_match_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_all_diff_aux_aux_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ALL_DIFF_AUX_AUX_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ALL_DIFF_AUX_AUX_MATCH_1.to_owned()),
        "the private companion of {ARRAY_ALL_DIFF_AUX_AUX_MATCH_1_MODULE} must retain \
         {ARRAY_ALL_DIFF_AUX_AUX_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ALL_DIFF_AUX_AUX_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ALL_DIFF_AUX_AUX_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ALL_DIFF_AUX_AUX_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_map_m_map_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_map_m_map_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MAP_M_MAP_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MAP_M_MAP.to_owned()),
        "the private companion of {ARRAY_MAP_M_MAP_MODULE} must retain {ARRAY_MAP_M_MAP}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MAP_M_MAP)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MAP_M_MAP}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_MAP_M_MAP} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_map_m_map_unary_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_map_unary_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MAP_M_MAP_UNARY_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MAP_M_MAP_UNARY.to_owned()),
        "the private companion of {ARRAY_MAP_M_MAP_UNARY_MODULE} must retain \
         {ARRAY_MAP_M_MAP_UNARY}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MAP_M_MAP_UNARY)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MAP_M_MAP_UNARY}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_MAP_M_MAP_UNARY} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_map_m_map_unsafe_rec_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_map_m_map_unsafe_rec_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_MAP_M_MAP_UNSAFE_REC_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MAP_M_MAP_UNSAFE_REC.to_owned()),
        "the private companion of {ARRAY_MAP_M_MAP_UNSAFE_REC_MODULE} must retain \
         {ARRAY_MAP_M_MAP_UNSAFE_REC}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MAP_M_MAP_UNSAFE_REC)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MAP_M_MAP_UNSAFE_REC}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_MAP_M_MAP_UNSAFE_REC} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_map_m_map_induct_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_map_m_map_induct_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MAP_M_MAP_INDUCT_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MAP_M_MAP_INDUCT.to_owned()),
        "the private companion of {ARRAY_MAP_M_MAP_INDUCT_MODULE} must retain \
         {ARRAY_MAP_M_MAP_INDUCT}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MAP_M_MAP_INDUCT)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MAP_M_MAP_INDUCT}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_MAP_M_MAP_INDUCT} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_take_while_go_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_take_while_go_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_TAKE_WHILE_GO_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_TAKE_WHILE_GO.to_owned()),
        "the private companion of {ARRAY_TAKE_WHILE_GO_MODULE} must retain {ARRAY_TAKE_WHILE_GO}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_TAKE_WHILE_GO)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_TAKE_WHILE_GO}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_TAKE_WHILE_GO} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_zip_with_all_go_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_zip_with_all_go_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_ZIP_WITH_ALL_GO_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_ZIP_WITH_ALL_GO.to_owned()),
        "the private companion of {ARRAY_ZIP_WITH_ALL_GO_MODULE} must retain \
         {ARRAY_ZIP_WITH_ALL_GO}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_ZIP_WITH_ALL_GO)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_ZIP_WITH_ALL_GO}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_ZIP_WITH_ALL_GO} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_unzip_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_unzip_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_UNZIP_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_UNZIP_MATCH_1.to_owned()),
        "the private companion of {ARRAY_UNZIP_MATCH_1_MODULE} must retain {ARRAY_UNZIP_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_UNZIP_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_UNZIP_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_UNZIP_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_unzip_second_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_unzip_second_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_UNZIP_MATCH_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_UNZIP_MATCH_3.to_owned()),
        "the private companion of {ARRAY_UNZIP_MATCH_3_MODULE} must retain {ARRAY_UNZIP_MATCH_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_UNZIP_MATCH_3)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_UNZIP_MATCH_3}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_UNZIP_MATCH_3} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_size_pop_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_size_pop_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_SIZE_POP_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_SIZE_POP_MATCH_1_1.to_owned()),
        "the private companion of {ARRAY_SIZE_POP_MATCH_1_1_MODULE} must retain \
         {ARRAY_SIZE_POP_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_SIZE_POP_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_SIZE_POP_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_SIZE_POP_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_shrink_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_shrink_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_SHRINK_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_SHRINK_MATCH_1.to_owned()),
        "the private companion of {ARRAY_SHRINK_MATCH_1_MODULE} must retain \
         {ARRAY_SHRINK_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_SHRINK_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_SHRINK_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_SHRINK_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_shrink_loop_sunfold_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_shrink_loop_sunfold_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_SHRINK_LOOP_SUNFOLD_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_SHRINK_LOOP_SUNFOLD.to_owned()),
        "the private companion of {ARRAY_SHRINK_LOOP_SUNFOLD_MODULE} must retain \
         {ARRAY_SHRINK_LOOP_SUNFOLD}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_SHRINK_LOOP_SUNFOLD)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_SHRINK_LOOP_SUNFOLD}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_SHRINK_LOOP_SUNFOLD} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_shrink_loop_unsafe_rec_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_shrink_loop_unsafe_rec_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_SHRINK_LOOP_UNSAFE_REC_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_SHRINK_LOOP_UNSAFE_REC.to_owned()),
        "the private companion of {ARRAY_SHRINK_LOOP_UNSAFE_REC_MODULE} must retain \
         {ARRAY_SHRINK_LOOP_UNSAFE_REC}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_SHRINK_LOOP_UNSAFE_REC)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_SHRINK_LOOP_UNSAFE_REC}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_SHRINK_LOOP_UNSAFE_REC} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_modify_m_unsafe_helper_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_modify_m_unsafe_helper_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MODIFY_M_UNSAFE_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MODIFY_M_UNSAFE_PROOF_1.to_owned()),
        "the private companion of {ARRAY_MODIFY_M_UNSAFE_PROOF_1_MODULE} must retain \
         {ARRAY_MODIFY_M_UNSAFE_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MODIFY_M_UNSAFE_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MODIFY_M_UNSAFE_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_MODIFY_M_UNSAFE_PROOF_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_of_fn_go_helper_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_of_fn_go_helper_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_OF_FN_GO_F_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_OF_FN_GO_F.to_owned()),
        "the private companion of {ARRAY_OF_FN_GO_F_MODULE} must retain {ARRAY_OF_FN_GO_F}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_OF_FN_GO_F)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_OF_FN_GO_F}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_OF_FN_GO_F} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_of_fn_go_sunfold_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_of_fn_go_sunfold_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_OF_FN_GO_SUNFOLD_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_OF_FN_GO_SUNFOLD.to_owned()),
        "the private companion of {ARRAY_OF_FN_GO_SUNFOLD_MODULE} must retain \
         {ARRAY_OF_FN_GO_SUNFOLD}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_OF_FN_GO_SUNFOLD)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_OF_FN_GO_SUNFOLD}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_OF_FN_GO_SUNFOLD} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_of_fn_go_unsafe_rec_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_of_fn_go_unsafe_rec_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_OF_FN_GO_UNSAFE_REC_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_OF_FN_GO_UNSAFE_REC.to_owned()),
        "the private companion of {ARRAY_OF_FN_GO_UNSAFE_REC_MODULE} must retain \
         {ARRAY_OF_FN_GO_UNSAFE_REC}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_OF_FN_GO_UNSAFE_REC)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_OF_FN_GO_UNSAFE_REC}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_OF_FN_GO_UNSAFE_REC} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_of_fn_go_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_of_fn_go_proof_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_OF_FN_GO_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_OF_FN_GO_PROOF_1.to_owned()),
        "the private companion of {ARRAY_OF_FN_GO_PROOF_1_MODULE} must retain \
         {ARRAY_OF_FN_GO_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_OF_FN_GO_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_OF_FN_GO_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_OF_FN_GO_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_of_fn_go_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_of_fn_go_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_OF_FN_GO_MATCH_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_OF_FN_GO_MATCH_1.to_owned()),
        "the private companion of {ARRAY_OF_FN_GO_MATCH_1_MODULE} must retain \
         {ARRAY_OF_FN_GO_MATCH_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_OF_FN_GO_MATCH_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_OF_FN_GO_MATCH_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_OF_FN_GO_MATCH_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn array_pop_while_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib =
        lib_or_skip!("array_pop_while_proof_theorem_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_POP_WHILE_PROOF_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_POP_WHILE_PROOF_1.to_owned()),
        "the private companion of {ARRAY_POP_WHILE_PROOF_1_MODULE} must retain \
         {ARRAY_POP_WHILE_PROOF_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_POP_WHILE_PROOF_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_POP_WHILE_PROOF_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_POP_WHILE_PROOF_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_pop_while_second_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_pop_while_second_proof_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_POP_WHILE_PROOF_2_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_POP_WHILE_PROOF_2.to_owned()),
        "the private companion of {ARRAY_POP_WHILE_PROOF_2_MODULE} must retain \
         {ARRAY_POP_WHILE_PROOF_2}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_POP_WHILE_PROOF_2)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_POP_WHILE_PROOF_2}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_POP_WHILE_PROOF_2} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_pop_while_third_proof_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_pop_while_third_proof_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_POP_WHILE_PROOF_3_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_POP_WHILE_PROOF_3.to_owned()),
        "the private companion of {ARRAY_POP_WHILE_PROOF_3_MODULE} must retain \
         {ARRAY_POP_WHILE_PROOF_3}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_POP_WHILE_PROOF_3)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_POP_WHILE_PROOF_3}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_POP_WHILE_PROOF_3} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_pop_while_equation_theorem_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "array_pop_while_equation_theorem_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, ARRAY_POP_WHILE_EQ_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_POP_WHILE_EQ_1.to_owned()),
        "the private companion of {ARRAY_POP_WHILE_EQ_1_MODULE} must retain {ARRAY_POP_WHILE_EQ_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_POP_WHILE_EQ_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_POP_WHILE_EQ_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Thm(_)),
        "private companion decoded {ARRAY_POP_WHILE_EQ_1} as {} instead of Thm",
        recovered.kind_name()
    );
}

#[test]
fn array_mem_def_match_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!("array_mem_def_match_is_decoded_from_its_private_storage_module");
    let chain = chain_bytes(&lib, ARRAY_MEM_DEF_MATCH_1_1_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&ARRAY_MEM_DEF_MATCH_1_1.to_owned()),
        "the private companion of {ARRAY_MEM_DEF_MATCH_1_1_MODULE} must retain \
         {ARRAY_MEM_DEF_MATCH_1_1}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == ARRAY_MEM_DEF_MATCH_1_1)
        .unwrap_or_else(|| panic!("private decoder lost {ARRAY_MEM_DEF_MATCH_1_1}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {ARRAY_MEM_DEF_MATCH_1_1} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn option_is_some_match_splitter_is_decoded_from_its_private_storage_module() {
    let lib = lib_or_skip!(
        "option_is_some_match_splitter_is_decoded_from_its_private_storage_module"
    );
    let chain = chain_bytes(&lib, OPTION_IS_SOME_MATCH_1_SPLITTER_MODULE);
    let (_, private_names) = exported_and_private_names(&chain);

    assert!(
        private_names.contains(&OPTION_IS_SOME_MATCH_1_SPLITTER.to_owned()),
        "the private companion of {OPTION_IS_SOME_MATCH_1_SPLITTER_MODULE} must retain \
         {OPTION_IS_SOME_MATCH_1_SPLITTER}"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == OPTION_IS_SOME_MATCH_1_SPLITTER)
        .unwrap_or_else(|| panic!("private decoder lost {OPTION_IS_SOME_MATCH_1_SPLITTER}"));
    assert!(
        matches!(recovered, ConstantInfo::Defn(_)),
        "private companion decoded {OPTION_IS_SOME_MATCH_1_SPLITTER} as {} instead of Defn",
        recovered.kind_name()
    );
}

#[test]
fn subarray_merge_sort_unary_eq_def_remains_a_concrete_exported_declaration() {
    let lib =
        lib_or_skip!("subarray_merge_sort_unary_eq_def_remains_a_concrete_exported_declaration");
    let chain = chain_bytes(&lib, "Init/Data/Array/Sort/Lemmas");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    assert!(
        exported_names.contains(&SUBARRAY_MERGE_SORT_UNARY_EQ_DEF.to_owned()),
        "the exported array-sort part must retain {SUBARRAY_MERGE_SORT_UNARY_EQ_DEF}"
    );
    assert!(
        private_names.contains(&SUBARRAY_MERGE_SORT_UNARY_EQ_DEF.to_owned()),
        "the private chain must retain {SUBARRAY_MERGE_SORT_UNARY_EQ_DEF}"
    );

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == SUBARRAY_MERGE_SORT_UNARY_EQ_DEF)
        .unwrap_or_else(|| panic!("exported decoder lost {SUBARRAY_MERGE_SORT_UNARY_EQ_DEF}"));
    assert!(
        is_concrete_recovery(&exported),
        "exported decoder decoded {SUBARRAY_MERGE_SORT_UNARY_EQ_DEF} only as {} instead of a concrete declaration",
        exported.kind_name()
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let chained = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode")
        .into_iter()
        .find(|info| info.name().to_display_string() == SUBARRAY_MERGE_SORT_UNARY_EQ_DEF)
        .unwrap_or_else(|| panic!("private chain lost {SUBARRAY_MERGE_SORT_UNARY_EQ_DEF}"));
    assert!(
        is_concrete_recovery(&chained),
        "private chain decoded {SUBARRAY_MERGE_SORT_UNARY_EQ_DEF} only as {} instead of a concrete declaration",
        chained.kind_name()
    );
}

#[test]
fn merge_sort_tr_unsafe_rec_companions_retain_concrete_kinds() {
    let lib = lib_or_skip!("merge_sort_tr_unsafe_rec_companions_retain_concrete_kinds");
    let chain = chain_bytes(&lib, "Init/Data/List/Sort/Impl");
    let (exported_names, private_names) = exported_and_private_names(&chain);

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("exported constants decode");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against its companion address spaces");
    let private_constants = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("private constants decode");

    // Direction 1: the companion-only helpers. These are what the chain must
    // restore, and they must arrive with a real declaration kind rather than as
    // a same-named axiom, which would let the kernel accept a type whose body
    // was never recovered.
    for name in MERGE_SORT_TR_COMPANION_ONLY_UNSAFE_RECS {
        assert!(
            !exported_names.contains(&name.to_owned()),
            "the exported part must omit the companion-only mergeSortTR helper {name}"
        );
        assert!(
            private_names.contains(&name.to_owned()),
            "the private companion must restore the mergeSortTR helper {name}"
        );
        assert!(
            exported_constants
                .iter()
                .all(|info| info.name().to_display_string() != name),
            "exported decoder unexpectedly recovered {name}"
        );
        let recovered = private_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("private decoder lost {name}"));
        assert!(
            is_concrete_recovery(recovered),
            "private companion decoded {name} only as {} instead of a concrete declaration",
            recovered.kind_name()
        );
    }

    // Direction 2: the `mergeSortTR₂` pair, which is `_private.`-mangled and
    // EXPORTED. Asserting these are exported is what stops direction 1 from
    // being restated as "every `_private.` name is companion-only" — the
    // premise that failed this regression, and that
    // `decl::EXPORTED_UNSAFE_REC_COLLISIONS` pins in src.
    for name in MERGE_SORT_TR_EXPORTED_UNSAFE_RECS {
        assert!(
            exported_names.contains(&name.to_owned()),
            "{name} is declared by the exported part at the pin; treating it as \
             companion-only is the prefix misclassification"
        );
        let exported_decoded = exported_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("exported decoder lost {name}"));
        assert!(
            is_concrete_recovery(exported_decoded),
            "exported decoder produced {name} as {} instead of a concrete declaration",
            exported_decoded.kind_name()
        );
        // The private part is a superset, so it carries these too, and must not
        // downgrade them on the way through.
        let private_decoded = private_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("private decoder lost {name}"));
        assert!(
            is_concrete_recovery(private_decoded),
            "private part produced {name} as {} instead of a concrete declaration",
            private_decoded.kind_name()
        );
    }
}

#[test]
fn private_part_is_a_superset_across_the_modules_the_bead_names() {
    let lib = lib_or_skip!("private_part_is_a_superset_across_the_modules_the_bead_names");

    // (module, exported constants, private constants) — all measured at the pin.
    // franken_lean-timy named these modules as sources of missing auxiliaries.
    let expected = [
        ("Init/Data/List/ToArrayImpl", 5_usize, 6_usize),
        ("Init/Prelude", 2204, 2314),
        ("Init/Data/Array/BasicAux", 8, 37),
        ("Init/Control/MonadAttach", 29, 30),
    ];

    for (relative, exported_count, private_count) in expected {
        let chain = chain_bytes(&lib, relative);
        let (exported, private) = exported_and_private_names(&chain);

        assert_eq!(
            exported.len(),
            exported_count,
            "{relative}: exported constant count changed at the pin"
        );
        assert_eq!(
            private.len(),
            private_count,
            "{relative}: private constant count changed at the pin"
        );
        assert!(
            private_count > exported_count,
            "{relative}: this module must actually gain constants from its \
             private part, else it witnesses nothing"
        );
        for name in &exported {
            assert!(
                private.contains(name),
                "{relative}: private array must be a superset of the exported \
                 array; {name} is missing"
            );
        }
        let recovered = private
            .iter()
            .filter(|name| !exported.contains(name))
            .count();
        assert_eq!(
            recovered,
            private_count - exported_count,
            "{relative}: the private part must add constants rather than \
             replace exported ones"
        );
    }
}

#[test]
fn recovered_family_covers_match_and_proof_and_loop_auxiliaries() {
    let lib = lib_or_skip!("recovered_family_covers_match_and_proof_and_loop_auxiliaries");
    let chain = chain_bytes(&lib, "Init/Data/Array/BasicAux");
    let (exported, private) = exported_and_private_names(&chain);

    // franken_lean-timy named match_N, _proof_N and the `.loop`/`.go` recursion
    // auxiliaries as the missing family. These three are measured members of
    // this module's private delta.
    let family = [
        "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_1",
        "_private.Init.Data.Array.BasicAux.0.Array.mapM'._proof_2",
        "_private.Init.Data.Array.BasicAux.0.Array.mapM'.go",
    ];
    for member in family {
        assert!(
            !exported.contains(&member.to_owned()),
            "{member} must be absent from the exported part, else it witnesses \
             nothing about chain decode"
        );
        assert!(
            private.contains(&member.to_owned()),
            "{member} must be recovered from the private part; got {private:?}"
        );
    }
}

/// The auxiliary families `franken_lean-timy` names, as predicates over a
/// display-form constant name.
///
/// Each mirrors a `\.<pattern>$`-anchored form: the leading dot is required, so
/// a bare top-level `match_1` is not counted. `.loop` and `.go` are component
/// tests rather than suffix tests because the recursion auxiliary is a segment,
/// not a terminal.
mod family {
    fn components(name: &str) -> Vec<&str> {
        name.split('.').collect()
    }

    /// A nonempty run of ASCII digits — the `\d+` of the measured patterns.
    fn digits(rest: &str) -> bool {
        !rest.is_empty() && rest.bytes().all(|byte| byte.is_ascii_digit())
    }

    /// `\d+(_\d+)*` — only `match_N` admits the underscore-joined form.
    fn digit_groups(rest: &str) -> bool {
        !rest.is_empty() && rest.split('_').all(digits)
    }

    fn last_component_suffix<'a>(name: &'a str, prefix: &str) -> Option<&'a str> {
        let parts = components(name);
        if parts.len() < 2 {
            return None;
        }
        parts.last().and_then(|last| last.strip_prefix(prefix))
    }

    /// `.match_1`, `.match_1_1`, …
    pub fn match_n(name: &str) -> bool {
        last_component_suffix(name, "match_").is_some_and(digit_groups)
    }

    /// `._proof_1`, …
    pub fn proof_n(name: &str) -> bool {
        last_component_suffix(name, "_proof_").is_some_and(digits)
    }

    /// `.eq_1`, … — equation lemmas.
    pub fn eq_n(name: &str) -> bool {
        last_component_suffix(name, "eq_").is_some_and(digits)
    }

    /// `._eq_1`, … — a shape the pinned Reference does not emit.
    ///
    /// Kept, and exercised by
    /// `the_underscore_eq_n_shape_is_absent_from_the_pin`, so the family's
    /// absence is an asserted fact rather than a silent gap in the tables
    /// above. See that test for the measurement.
    pub fn private_eq_n(name: &str) -> bool {
        last_component_suffix(name, "_eq_").is_some_and(digits)
    }

    /// `.eq_def`.
    pub fn eq_def(name: &str) -> bool {
        let parts = components(name);
        parts.len() >= 2 && parts.last() == Some(&"eq_def")
    }

    /// A `loop` component anywhere but the head.
    pub fn loop_(name: &str) -> bool {
        components(name)
            .iter()
            .skip(1)
            .any(|component| *component == "loop")
    }

    /// A `go` recursion component anywhere but the head.
    pub fn go(name: &str) -> bool {
        components(name)
            .iter()
            .skip(1)
            .any(|component| *component == "go")
    }

    /// `._unsafe_rec` — generated recursion helpers retained in private parts.
    pub fn unsafe_rec(name: &str) -> bool {
        last_component_suffix(name, "_unsafe_rec").is_some_and(str::is_empty)
    }

    /// `.loop.eq_def` — equation-compiler lemma for a generated loop helper.
    pub fn loop_eq_def(name: &str) -> bool {
        let parts = components(name);
        parts.len() >= 3
            && parts.last() == Some(&"eq_def")
            && parts[..parts.len() - 1]
                .iter()
                .any(|component| *component == "loop")
    }

    /// `.loop._proof_1` — proof helper emitted inside a generated loop.
    pub fn loop_proof_1(name: &str) -> bool {
        let parts = components(name);
        parts.len() >= 3
            && parts.last() == Some(&"_proof_1")
            && parts[..parts.len() - 1]
                .iter()
                .any(|component| *component == "loop")
    }

    /// `.loop.match_1` — match helper emitted inside a generated loop.
    pub fn loop_match_1(name: &str) -> bool {
        let parts = components(name);
        parts.len() >= 3
            && parts.last() == Some(&"match_1")
            && parts[..parts.len() - 1]
                .iter()
                .any(|component| *component == "loop")
    }

    /// `._unary` — compiler-generated unary recursor helper.
    pub fn unary(name: &str) -> bool {
        last_component_suffix(name, "_unary").is_some_and(str::is_empty)
    }

    /// `._sunfold` — compiler-generated structural-unfolding helper.
    pub fn sunfold(name: &str) -> bool {
        last_component_suffix(name, "_sunfold").is_some_and(str::is_empty)
    }

    /// `._f` — compiler-generated local helper retained in private parts.
    pub fn private_f(name: &str) -> bool {
        last_component_suffix(name, "_f").is_some_and(str::is_empty)
    }

    /// `Array.shrink.loop._f` — nested helper from the array shrink loop.
    pub fn array_shrink_loop_f(name: &str) -> bool {
        name.ends_with(".Array.shrink.loop._f")
    }
}

/// Enumerate every module under `Init` that has a complete companion chain.
fn init_chain_modules(lib: &PathBuf) -> Vec<String> {
    let mut out = Vec::new();
    let root = lib.join("Init");
    let mut pending = vec![root];
    while let Some(directory) = pending.pop() {
        let entries = std::fs::read_dir(&directory)
            .unwrap_or_else(|error| panic!("read {}: {error}", directory.display()));
        for entry in entries {
            let entry = entry.expect("directory entry");
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
                continue;
            }
            if path.extension() != Some(std::ffi::OsStr::new("olean")) {
                continue;
            }
            let server = PathBuf::from(format!("{}.server", path.display()));
            let private = PathBuf::from(format!("{}.private", path.display()));
            if !(server.is_file() && private.is_file()) {
                continue;
            }
            let relative = path
                .strip_prefix(lib)
                .expect("module path is under the stdlib root")
                .with_extension("");
            out.push(relative.to_string_lossy().into_owned());
        }
    }
    out.sort();
    out
}

#[test]
fn every_named_auxiliary_family_decodes_across_the_whole_init_corpus() {
    let lib = lib_or_skip!("every_named_auxiliary_family_decodes_across_the_whole_init_corpus");

    // An aggregate count cannot witness a per-family gap: one family could be
    // wholly absent while the total still looked healthy. franken_lean-timy
    // names match_N, _proof_N, eq_N/eq_def and the `.loop` recursion auxiliary
    // as one population, so each is bound to its own measured floor here.
    //
    // Counts are per-module-distinct names summed over every Init module with a
    // complete chain, measured at the pin.
    let modules = init_chain_modules(&lib);
    assert_eq!(
        modules.len(),
        600,
        "every Init module at the pin carries a complete companion chain"
    );

    let mut match_n = 0_usize;
    let mut proof_n = 0_usize;
    let mut eq_n = 0_usize;
    let mut eq_def = 0_usize;
    let mut loop_ = 0_usize;
    let mut exported_total = 0_usize;
    let mut private_total = 0_usize;

    for relative in &modules {
        let chain = chain_bytes(&lib, relative);
        let (exported, private) = exported_and_private_names(&chain);
        exported_total += exported.len();
        private_total += private.len();
        for name in &private {
            if family::match_n(name) {
                match_n += 1;
            }
            if family::proof_n(name) {
                proof_n += 1;
            }
            if family::eq_n(name) {
                eq_n += 1;
            }
            if family::eq_def(name) {
                eq_def += 1;
            }
            if family::loop_(name) {
                loop_ += 1;
            }
        }
    }

    assert_eq!(exported_total, 51_506, "exported corpus total moved");
    assert_eq!(private_total, 65_404, "private corpus total moved");
    assert_eq!(match_n, 2_592, "match_N decode coverage moved");
    assert_eq!(proof_n, 3_480, "_proof_N decode coverage moved");
    assert_eq!(eq_n, 3_449, "eq_N decode coverage moved");
    assert_eq!(eq_def, 507, "eq_def decode coverage moved");
    assert_eq!(loop_, 686, "`.loop` decode coverage moved");
}

#[test]
fn every_named_private_auxiliary_family_reaches_the_constant_info_decoder() {
    let lib =
        lib_or_skip!("every_named_private_auxiliary_family_reaches_the_constant_info_decoder");

    // The corpus census above proves that the private `constNames` arrays name
    // each family. That is necessary but insufficient: a future decoder could
    // retain the names while failing to construct the corresponding
    // ConstantInfo. Find one *private-only* representative per family, then
    // pass each through DeclDecoder with its real companion address spaces.
    let families: [(&str, fn(&str) -> bool); 14] = [
        ("match_N", family::match_n),
        ("_proof_N", family::proof_n),
        ("eq_N", family::eq_n),
        ("eq_def", family::eq_def),
        (".loop.eq_def", family::loop_eq_def),
        (".loop.match_1", family::loop_match_1),
        (".loop._proof_1", family::loop_proof_1),
        (".loop", family::loop_),
        (".go", family::go),
        ("_unsafe_rec", family::unsafe_rec),
        ("_unary", family::unary),
        ("_sunfold", family::sunfold),
        ("_f", family::private_f),
        ("Array.shrink.loop._f", family::array_shrink_loop_f),
    ];
    let mut representatives: [Option<(String, String)>; 14] = [
        None, None, None, None, None, None, None, None, None, None, None, None, None, None,
    ];

    for relative in init_chain_modules(&lib) {
        let chain = chain_bytes(&lib, &relative);
        let (exported, private) = exported_and_private_names(&chain);
        for (slot, (_, belongs_to_family)) in representatives.iter_mut().zip(families) {
            if slot.is_some() {
                continue;
            }
            if let Some(name) = private
                .iter()
                .find(|name| !exported.contains(*name) && belongs_to_family(name))
            {
                *slot = Some((relative.clone(), name.clone()));
            }
        }
        if representatives.iter().all(Option::is_some) {
            break;
        }
    }

    for ((family, _), representative) in families.into_iter().zip(representatives) {
        let (relative, name) = representative.unwrap_or_else(|| {
            panic!(
                "the pinned Init private companions contain no private-only {family} representative"
            )
        });
        let chain = chain_bytes(&lib, &relative);
        let private_view =
            OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
                .unwrap_or_else(|error| {
                    panic!("{family} {name}: parse private {relative}: {error}")
                });
        let constants = DeclDecoder::new(&private_view, WalkBudget::default())
            .decode_module_constants()
            .unwrap_or_else(|error| panic!("{family} {name}: decode private {relative}: {error}"));

        let recovered = constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| {
                panic!(
                    "{family} {name} in {relative} remained only a constName instead of decoding to ConstantInfo"
                )
            });
        assert!(
            is_concrete_recovery(recovered),
            "{family} {name} in {relative} decoded only as {} instead of a concrete declaration",
            recovered.kind_name()
        );
    }
}

#[test]
fn private_auxiliary_recovery_never_weakens_a_private_only_constant_to_an_axiom() {
    let lib = lib_or_skip!(
        "private_auxiliary_recovery_never_weakens_a_private_only_constant_to_an_axiom"
    );

    // This is deliberately stronger than the name census and the existence cell
    // above. A decoder that merely manufactures an axiom with the right name
    // would make the kernel accept its type without checking a recovered body,
    // recreating the body-stripping half of the same corpus defect. For every
    // family, establish the RED side on the exported decoder, then the GREEN
    // side on the private companion decoder: the concrete declaration exists
    // there and keeps its real ConstantInfo kind.
    let families: [(&str, fn(&str) -> bool); 14] = [
        ("match_N", family::match_n),
        ("_proof_N", family::proof_n),
        ("eq_N", family::eq_n),
        ("eq_def", family::eq_def),
        (".loop.eq_def", family::loop_eq_def),
        (".loop.match_1", family::loop_match_1),
        (".loop._proof_1", family::loop_proof_1),
        (".loop", family::loop_),
        (".go", family::go),
        ("_unsafe_rec", family::unsafe_rec),
        ("_unary", family::unary),
        ("_sunfold", family::sunfold),
        ("_f", family::private_f),
        ("Array.shrink.loop._f", family::array_shrink_loop_f),
    ];

    for (family, belongs_to_family) in families {
        let mut representative = None;
        for relative in init_chain_modules(&lib) {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            if let Some(name) = private
                .iter()
                .find(|name| !exported.contains(*name) && belongs_to_family(name))
            {
                representative = Some((relative, name.clone()));
                break;
            }
        }

        let (relative, name) = representative.unwrap_or_else(|| {
            panic!("the pinned Init private companions contain no private-only {family} witness")
        });
        let chain = chain_bytes(&lib, &relative);
        let exported_view = OleanView::parse(&chain.exported)
            .unwrap_or_else(|error| panic!("{family} {name}: parse exported {relative}: {error}"));
        let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
            .decode_module_constants()
            .unwrap_or_else(|error| panic!("{family} {name}: decode exported {relative}: {error}"));
        assert!(
            exported_constants
                .iter()
                .all(|info| info.name().to_display_string() != name),
            "{family} {name} unexpectedly reached the exported decoder; the private-companion regression lost its RED side"
        );

        let private_view =
            OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
                .unwrap_or_else(|error| {
                    panic!("{family} {name}: parse private {relative}: {error}")
                });
        let private_constants = DeclDecoder::new(&private_view, WalkBudget::default())
            .decode_module_constants()
            .unwrap_or_else(|error| panic!("{family} {name}: decode private {relative}: {error}"));
        let recovered = private_constants
            .iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| {
                panic!("{family} {name}: private decoder lost the representative in {relative}")
            });
        assert!(
            is_concrete_recovery(recovered),
            "{family} {name}: private companion recovery decoded only as {} instead of a concrete declaration",
            recovered.kind_name()
        );
    }
}

#[test]
fn unary_private_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib =
        lib_or_skip!("unary_private_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // Keep `_unary` as an independently named regression cell. The generic
    // family loop above proves breadth; this cell makes a failure's RED side
    // explicit: exported decode cannot see the auxiliary at all, while its
    // private companion restores a concrete declaration rather than an axiom.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::unary(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only _unary witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!("_unary {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_unary {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        "_unary {name}: exported decode unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| panic!("_unary {name}: parse private {relative}: {error}"));
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_unary {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!("_unary {name}: private decoder lost it in {relative}"));
    assert!(
        !matches!(recovered, ConstantInfo::Axiom(_)),
        "_unary {name}: companion recovery weakened the declaration to an axiom"
    );
}

#[test]
fn unsafe_rec_private_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib =
        lib_or_skip!("unsafe_rec_private_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // `_unsafe_rec` is its own compiler-emitted recursion shape. Select a real
    // private-only witness from the pin so the RED side cannot be satisfied by
    // a name that was exported in some unrelated module.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::unsafe_rec(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only _unsafe_rec witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!("_unsafe_rec {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_unsafe_rec {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        "_unsafe_rec {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| {
                panic!("_unsafe_rec {name}: parse private {relative}: {error}")
            });
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_unsafe_rec {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!("_unsafe_rec {name}: private decoder lost it in {relative}"));
    assert!(
        !matches!(recovered, ConstantInfo::Axiom(_)),
        "_unsafe_rec {name}: companion recovery weakened the declaration to an axiom"
    );
}

#[test]
fn private_f_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!("private_f_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // `_f` is a separate compiler helper family from the numbered match and
    // equation auxiliaries. Bind the failure to a genuinely private-only pin
    // member before checking omission in the exported declaration array.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::private_f(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only _f witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!("_f {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_f {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        "_f {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| panic!("_f {name}: parse private {relative}: {error}"));
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_f {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!("_f {name}: private decoder lost it in {relative}"));
    assert!(
        !matches!(recovered, ConstantInfo::Axiom(_)),
        "_f {name}: companion recovery weakened the declaration to an axiom"
    );
}

#[test]
fn loop_proof_1_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!("loop_proof_1_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // `.loop._proof_1` combines the recursion and proof-helper shapes; testing
    // it separately prevents either broad predicate from masking a missing
    // nested private declaration.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::loop_proof_1(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only .loop._proof_1 witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported).unwrap_or_else(|error| {
        panic!(".loop._proof_1 {name}: parse exported {relative}: {error}")
    });
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| {
            panic!(".loop._proof_1 {name}: decode exported {relative}: {error}")
        });
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        ".loop._proof_1 {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| {
                panic!(".loop._proof_1 {name}: parse private {relative}: {error}")
            });
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!(".loop._proof_1 {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!(".loop._proof_1 {name}: private decoder lost it in {relative}"));
    assert!(
        !matches!(recovered, ConstantInfo::Axiom(_)),
        ".loop._proof_1 {name}: companion recovery weakened the declaration to an axiom"
    );
}

#[test]
fn array_shrink_loop_f_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!("array_shrink_loop_f_requires_the_companion_and_keeps_its_real_kind");

    // The core observable names this nested `_f` specifically. A broad suffix
    // match could select some other helper, so bind the RED/green cell to the
    // Array.shrink.loop path as well as the terminal private helper name.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::array_shrink_loop_f(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain an Array.shrink.loop._f witness");
    let chain = chain_bytes(&lib, &relative);

    assert!(
        name.ends_with(".Array.shrink.loop._f"),
        "the selected _f witness must be the exact reported Array.shrink.loop._f shape"
    );

    let exported_view = OleanView::parse(&chain.exported).unwrap_or_else(|error| {
        panic!("Array.shrink.loop._f {name}: parse exported {relative}: {error}")
    });
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| {
            panic!("Array.shrink.loop._f {name}: decode exported {relative}: {error}")
        });
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        "Array.shrink.loop._f {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| {
                panic!("Array.shrink.loop._f {name}: parse private {relative}: {error}")
            });
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| {
            panic!("Array.shrink.loop._f {name}: decode private {relative}: {error}")
        })
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| {
            panic!("Array.shrink.loop._f {name}: private decoder lost it in {relative}")
        });
    assert!(
        !matches!(recovered, ConstantInfo::Axiom(_)),
        "Array.shrink.loop._f {name}: companion recovery weakened the declaration to an axiom"
    );
}

#[test]
fn loop_match_1_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!("loop_match_1_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // Syntax's generated recursion helpers have this combined `.loop.match_1`
    // shape. Requiring both components avoids treating an unrelated match_1 as
    // evidence that companion decode covers the nested recursion case.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::loop_match_1(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only .loop.match_1 witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!(".loop.match_1 {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| {
            panic!(".loop.match_1 {name}: decode exported {relative}: {error}")
        });
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        ".loop.match_1 {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| {
                panic!(".loop.match_1 {name}: parse private {relative}: {error}")
            });
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!(".loop.match_1 {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!(".loop.match_1 {name}: private decoder lost it in {relative}"));
    assert!(
        !matches!(recovered, ConstantInfo::Axiom(_)),
        ".loop.match_1 {name}: companion recovery weakened the declaration to an axiom"
    );
}

#[test]
fn loop_eq_def_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!("loop_eq_def_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // A `.loop.eq_def` is neither a broad loop helper nor an ordinary eq_def:
    // it is the equation-compiler declaration attached to the generated loop.
    // Keep its RED/green recovery proof independently named.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::loop_eq_def(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only .loop.eq_def witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!(".loop.eq_def {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!(".loop.eq_def {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        ".loop.eq_def {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| {
                panic!(".loop.eq_def {name}: parse private {relative}: {error}")
            });
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!(".loop.eq_def {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!(".loop.eq_def {name}: private decoder lost it in {relative}"));
    assert!(
        !matches!(recovered, ConstantInfo::Axiom(_)),
        ".loop.eq_def {name}: companion recovery weakened the declaration to an axiom"
    );
}

#[test]
fn go_private_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!("go_private_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // `.go` is a separately emitted recursion helper, not merely another
    // numbered equation or proof name. Select an actual private-only member
    // before proving its exported omission and concrete companion recovery.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::go(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only .go witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!(".go {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!(".go {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        ".go {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| panic!(".go {name}: parse private {relative}: {error}"));
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!(".go {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!(".go {name}: private decoder lost it in {relative}"));
    assert!(
        is_concrete_recovery(&recovered),
        ".go {name}: companion recovery decoded only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn eq_n_private_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!("eq_n_private_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // Equation lemmas are a separate compiler-emitted family. The witness must
    // be private-only by actual chain membership, not by its `_private.` name
    // prefix, before the exported omission has any diagnostic value.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::eq_n(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only eq_N witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!("eq_N {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("eq_N {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        "eq_N {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| panic!("eq_N {name}: parse private {relative}: {error}"));
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("eq_N {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!("eq_N {name}: private decoder lost it in {relative}"));
    assert!(
        is_concrete_recovery(&recovered),
        "eq_N {name}: companion recovery decoded only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn proof_n_private_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib =
        lib_or_skip!("proof_n_private_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // `_proof_N` is distinct from its surrounding match or loop declaration.
    // Select an actual private-only witness, then require the companion decoder
    // to retain a concrete declaration kind for that exact proof helper.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::proof_n(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only _proof_N witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!("_proof_N {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_proof_N {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        "_proof_N {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| panic!("_proof_N {name}: parse private {relative}: {error}"));
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_proof_N {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!("_proof_N {name}: private decoder lost it in {relative}"));
    assert!(
        is_concrete_recovery(&recovered),
        "_proof_N {name}: companion recovery decoded only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn eq_def_private_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib =
        lib_or_skip!("eq_def_private_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // The terminal `eq_def` helper is a separate equation-compiler shape from
    // numbered eq_N lemmas and the nested loop-specific `eq_def` cell above.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::eq_def(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only eq_def witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!("eq_def {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("eq_def {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        "eq_def {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| panic!("eq_def {name}: parse private {relative}: {error}"));
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("eq_def {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!("eq_def {name}: private decoder lost it in {relative}"));
    assert!(
        is_concrete_recovery(&recovered),
        "eq_def {name}: companion recovery decoded only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn sunfold_private_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib =
        lib_or_skip!("sunfold_private_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // `_sunfold` is a compiler-generated structural-unfolding helper. Its
    // recovery must be tied to real private-only chain membership and retain a
    // concrete declaration kind, not a manufactured axiom.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::sunfold(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only _sunfold witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!("_sunfold {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_sunfold {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        "_sunfold {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| panic!("_sunfold {name}: parse private {relative}: {error}"));
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_sunfold {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!("_sunfold {name}: private decoder lost it in {relative}"));
    assert!(
        is_concrete_recovery(&recovered),
        "_sunfold {name}: companion recovery decoded only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn sunfold_family_keeps_concrete_members_on_both_chain_origins() {
    let lib = lib_or_skip!("sunfold_family_keeps_concrete_members_on_both_chain_origins");
    let mut exported_member = None;
    let mut private_only_member = None;

    for relative in init_chain_modules(&lib) {
        let chain = chain_bytes(&lib, &relative);
        let (exported, private) = exported_and_private_names(&chain);
        if exported_member.is_none() {
            exported_member = exported
                .iter()
                .find(|name| family::sunfold(name))
                .map(|name| (relative.clone(), name.clone()));
        }
        if private_only_member.is_none() {
            private_only_member = private
                .iter()
                .find(|name| !exported.contains(*name) && family::sunfold(name))
                .map(|name| (relative, name.clone()));
        }
        if exported_member.is_some() && private_only_member.is_some() {
            break;
        }
    }

    let (exported_relative, exported_name) =
        exported_member.expect("the pinned Init exported parts contain an _sunfold representative");
    let exported_chain = chain_bytes(&lib, &exported_relative);
    let exported_view = OleanView::parse(&exported_chain.exported)
        .unwrap_or_else(|error| panic!("_sunfold {exported_name}: parse exported: {error}"));
    let exported = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_sunfold {exported_name}: decode exported: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == exported_name)
        .unwrap_or_else(|| panic!("exported decoder lost _sunfold {exported_name}"));
    assert!(
        is_concrete_recovery(&exported),
        "exported _sunfold {exported_name} decoded only as {} instead of a concrete declaration",
        exported.kind_name()
    );

    let (private_relative, private_name) = private_only_member.expect(
        "the pinned Init private companions contain a private-only _sunfold representative",
    );
    let private_chain = chain_bytes(&lib, &private_relative);
    let private_view = OleanView::parse_with_dependencies(
        &private_chain.private,
        &[&private_chain.exported, &private_chain.server],
    )
    .unwrap_or_else(|error| panic!("_sunfold {private_name}: parse private: {error}"));
    let private = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_sunfold {private_name}: decode private: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == private_name)
        .unwrap_or_else(|| panic!("private decoder lost _sunfold {private_name}"));
    assert!(
        is_concrete_recovery(&private),
        "private-only _sunfold {private_name} decoded only as {} instead of a concrete declaration",
        private.kind_name()
    );
}

#[test]
fn private_f_family_keeps_concrete_members_on_both_chain_origins() {
    let lib = lib_or_skip!("private_f_family_keeps_concrete_members_on_both_chain_origins");
    let mut exported_member = None;
    let mut private_only_member = None;

    for relative in init_chain_modules(&lib) {
        let chain = chain_bytes(&lib, &relative);
        let (exported, private) = exported_and_private_names(&chain);
        if exported_member.is_none() {
            exported_member = exported
                .iter()
                .find(|name| family::private_f(name))
                .map(|name| (relative.clone(), name.clone()));
        }
        if private_only_member.is_none() {
            private_only_member = private
                .iter()
                .find(|name| !exported.contains(*name) && family::private_f(name))
                .map(|name| (relative, name.clone()));
        }
        if exported_member.is_some() && private_only_member.is_some() {
            break;
        }
    }

    let (exported_relative, exported_name) =
        exported_member.expect("the pinned Init exported parts contain an _f representative");
    let exported_chain = chain_bytes(&lib, &exported_relative);
    let exported_view = OleanView::parse(&exported_chain.exported)
        .unwrap_or_else(|error| panic!("_f {exported_name}: parse exported: {error}"));
    let exported = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_f {exported_name}: decode exported: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == exported_name)
        .unwrap_or_else(|| panic!("exported decoder lost _f {exported_name}"));
    assert!(
        is_concrete_recovery(&exported),
        "exported _f {exported_name} decoded only as {} instead of a concrete declaration",
        exported.kind_name()
    );

    let (private_relative, private_name) = private_only_member
        .expect("the pinned Init private companions contain a private-only _f representative");
    let private_chain = chain_bytes(&lib, &private_relative);
    let private_view = OleanView::parse_with_dependencies(
        &private_chain.private,
        &[&private_chain.exported, &private_chain.server],
    )
    .unwrap_or_else(|error| panic!("_f {private_name}: parse private: {error}"));
    let private = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_f {private_name}: decode private: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == private_name)
        .unwrap_or_else(|| panic!("private decoder lost _f {private_name}"));
    assert!(
        is_concrete_recovery(&private),
        "private-only _f {private_name} decoded only as {} instead of a concrete declaration",
        private.kind_name()
    );
}

#[test]
fn unary_family_keeps_concrete_members_on_both_chain_origins() {
    let lib = lib_or_skip!("unary_family_keeps_concrete_members_on_both_chain_origins");
    let mut exported_member = None;
    let mut private_only_member = None;

    for relative in init_chain_modules(&lib) {
        let chain = chain_bytes(&lib, &relative);
        let (exported, private) = exported_and_private_names(&chain);
        if exported_member.is_none() {
            exported_member = exported
                .iter()
                .find(|name| family::unary(name))
                .map(|name| (relative.clone(), name.clone()));
        }
        if private_only_member.is_none() {
            private_only_member = private
                .iter()
                .find(|name| !exported.contains(*name) && family::unary(name))
                .map(|name| (relative, name.clone()));
        }
        if exported_member.is_some() && private_only_member.is_some() {
            break;
        }
    }

    let (exported_relative, exported_name) =
        exported_member.expect("the pinned Init exported parts contain an _unary representative");
    let exported_chain = chain_bytes(&lib, &exported_relative);
    // The exported part may retain only an axiom shell for this name (notably
    // `Array.zipWithMAux._unary`), while the chain's private region holds the
    // real body. Origin remains exported because the name was selected from
    // the exported array; concrete-kind checking belongs to chain decode.
    let exported_chain_view = OleanView::parse_with_dependencies(
        &exported_chain.private,
        &[&exported_chain.exported, &exported_chain.server],
    )
    .unwrap_or_else(|error| panic!("_unary {exported_name}: parse chain: {error}"));
    let exported = DeclDecoder::new(&exported_chain_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_unary {exported_name}: decode chain: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == exported_name)
        .unwrap_or_else(|| panic!("chain decoder lost exported _unary {exported_name}"));
    assert!(
        is_concrete_recovery(&exported),
        "chain decode of exported _unary {exported_name} produced only {} instead of a concrete declaration",
        exported.kind_name()
    );

    let (private_relative, private_name) = private_only_member
        .expect("the pinned Init private companions contain a private-only _unary representative");
    let private_chain = chain_bytes(&lib, &private_relative);
    let private_view = OleanView::parse_with_dependencies(
        &private_chain.private,
        &[&private_chain.exported, &private_chain.server],
    )
    .unwrap_or_else(|error| panic!("_unary {private_name}: parse private: {error}"));
    let private = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_unary {private_name}: decode private: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == private_name)
        .unwrap_or_else(|| panic!("private decoder lost _unary {private_name}"));
    assert!(
        is_concrete_recovery(&private),
        "private-only _unary {private_name} decoded only as {} instead of a concrete declaration",
        private.kind_name()
    );
}

#[test]
fn unsafe_rec_family_keeps_concrete_members_on_both_chain_origins() {
    let lib = lib_or_skip!("unsafe_rec_family_keeps_concrete_members_on_both_chain_origins");
    let mut exported_member = None;
    let mut private_only_member = None;

    for relative in init_chain_modules(&lib) {
        let chain = chain_bytes(&lib, &relative);
        let (exported, private) = exported_and_private_names(&chain);
        if exported_member.is_none() {
            exported_member = exported
                .iter()
                .find(|name| family::unsafe_rec(name))
                .map(|name| (relative.clone(), name.clone()));
        }
        if private_only_member.is_none() {
            private_only_member = private
                .iter()
                .find(|name| !exported.contains(*name) && family::unsafe_rec(name))
                .map(|name| (relative, name.clone()));
        }
        if exported_member.is_some() && private_only_member.is_some() {
            break;
        }
    }

    let (exported_relative, exported_name) = exported_member
        .expect("the pinned Init exported parts contain an _unsafe_rec representative");
    let exported_chain = chain_bytes(&lib, &exported_relative);
    let exported_view = OleanView::parse(&exported_chain.exported)
        .unwrap_or_else(|error| panic!("_unsafe_rec {exported_name}: parse exported: {error}"));
    let exported = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_unsafe_rec {exported_name}: decode exported: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == exported_name)
        .unwrap_or_else(|| panic!("exported decoder lost _unsafe_rec {exported_name}"));
    assert!(
        is_concrete_recovery(&exported),
        "exported _unsafe_rec {exported_name} decoded only as {} instead of a concrete declaration",
        exported.kind_name()
    );

    let (private_relative, private_name) = private_only_member.expect(
        "the pinned Init private companions contain a private-only _unsafe_rec representative",
    );
    let private_chain = chain_bytes(&lib, &private_relative);
    let private_view = OleanView::parse_with_dependencies(
        &private_chain.private,
        &[&private_chain.exported, &private_chain.server],
    )
    .unwrap_or_else(|error| panic!("_unsafe_rec {private_name}: parse private: {error}"));
    let private = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("_unsafe_rec {private_name}: decode private: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == private_name)
        .unwrap_or_else(|| panic!("private decoder lost _unsafe_rec {private_name}"));
    assert!(
        is_concrete_recovery(&private),
        "private-only _unsafe_rec {private_name} decoded only as {} instead of a concrete declaration",
        private.kind_name()
    );
}

#[test]
fn match_n_private_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib =
        lib_or_skip!("match_n_private_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // The original timy witness pins one exact `match_1`; this separate family
    // cell prevents another private-only match_N from being silently weakened
    // to an axiom while that one witness still happens to decode.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::match_n(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only match_N witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!("match_N {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("match_N {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        "match_N {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| panic!("match_N {name}: parse private {relative}: {error}"));
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!("match_N {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!("match_N {name}: private decoder lost it in {relative}"));
    assert!(
        is_concrete_recovery(&recovered),
        "match_N {name}: companion recovery decoded only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn loop_private_auxiliary_requires_the_companion_and_keeps_its_real_kind() {
    let lib = lib_or_skip!("loop_private_auxiliary_requires_the_companion_and_keeps_its_real_kind");

    // The nested match/proof/eq_def cells exercise particular loop products;
    // this broader family cell protects an independently selected private-only
    // loop declaration from disappearing or being weakened to an axiom.
    let (relative, name) = init_chain_modules(&lib)
        .into_iter()
        .find_map(|relative| {
            let chain = chain_bytes(&lib, &relative);
            let (exported, private) = exported_and_private_names(&chain);
            private
                .iter()
                .find(|name| !exported.contains(*name) && family::loop_(name))
                .map(|name| (relative, name.clone()))
        })
        .expect("the pinned Init private companions contain a private-only .loop witness");
    let chain = chain_bytes(&lib, &relative);

    let exported_view = OleanView::parse(&chain.exported)
        .unwrap_or_else(|error| panic!(".loop {name}: parse exported {relative}: {error}"));
    let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!(".loop {name}: decode exported {relative}: {error}"));
    assert!(
        exported_constants
            .iter()
            .all(|info| info.name().to_display_string() != name),
        ".loop {name}: exported decoder unexpectedly has the private auxiliary"
    );

    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .unwrap_or_else(|error| panic!(".loop {name}: parse private {relative}: {error}"));
    let recovered = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .unwrap_or_else(|error| panic!(".loop {name}: decode private {relative}: {error}"))
        .into_iter()
        .find(|info| info.name().to_display_string() == name)
        .unwrap_or_else(|| panic!(".loop {name}: private decoder lost it in {relative}"));
    assert!(
        is_concrete_recovery(&recovered),
        ".loop {name}: companion recovery decoded only as {} instead of a concrete declaration",
        recovered.kind_name()
    );
}

#[test]
fn verified_chain_decode_returns_the_private_superset_on_the_real_pin() {
    let lib = lib_or_skip!("verified_chain_decode_returns_the_private_superset_on_the_real_pin");
    let chain = chain_bytes(&lib, "Init/Data/List/ToArrayImpl");

    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
        .expect("server part parses against the exported region");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against the exported and server regions");

    let constants = decode_chain_constants(&exported_view, &private_view, WalkBudget::default())
        .expect("the pin's chain is a superset, so the containment proof must succeed");

    let names: Vec<String> = constants
        .iter()
        .map(|info| info.name().to_display_string())
        .collect();
    assert_eq!(
        constants.len(),
        6,
        "the private array is returned, not the exported one"
    );
    assert!(
        names.contains(&TIMY_WITNESS.to_owned()),
        "the verified decode must still carry {TIMY_WITNESS}; got {names:?}"
    );
}

/// One axiom module carrying exactly `names`, encoded as a standalone region.
///
/// The containment proof compares two decoded constant arrays, so two
/// independently encoded regions exercise it exactly. Building a genuinely
/// non-superset three-part chain is not possible from the pin — the Reference
/// never emits one, which is precisely why the assumption went unguarded.
fn module_with(names: &[&str]) -> Vec<u8> {
    let constants: Vec<ConstantInfo> = names
        .iter()
        .map(|name| {
            ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: Name::from_components(name.split('.')),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::zero()),
                },
                is_unsafe: false,
            })
        })
        .collect();
    encode_module(
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: 2,
            flags: 1,
            lean_version: "4.32.0",
            githash: "0123456789abcdef0123456789abcdef01234567",
            base_addr: 0x20_000,
        },
        WriteBudget::default(),
    )
    .expect("module encodes")
    .bytes
}

#[test]
fn verified_chain_decode_refuses_a_private_part_that_drops_an_exported_declaration() {
    // The mutant this guard exists to kill: a private array that is NOT a
    // superset. Returning it would hand the kernel fewer declarations than the
    // module declares — franken_lean-timy's failure mode reached by a different
    // cause — and every downstream reference to `Demo.dropped` would surface as
    // an UnknownConstant with no indication that decode was responsible.
    let exported = module_with(&["Demo.kept", "Demo.dropped"]);
    let private = module_with(&["Demo.kept", "Demo.aux"]);

    let exported_view = OleanView::parse(&exported).expect("exported fixture parses");
    let private_view = OleanView::parse(&private).expect("private fixture parses");

    let error = decode_chain_constants(&exported_view, &private_view, WalkBudget::default())
        .expect_err("a private part missing an exported declaration must be refused");
    match &error {
        DeclError::PrivatePartIncomplete { missing } => {
            assert_eq!(
                missing.to_display_string(),
                "Demo.dropped",
                "the refusal must name the declaration that would have been lost"
            );
        }
        other => panic!("expected PrivatePartIncomplete, got {other:?}"),
    }
    assert!(
        format!("{error}").contains("Demo.dropped"),
        "the rendered error must name the lost declaration: {error}"
    );
}

#[test]
fn verified_chain_decode_accepts_a_strict_superset() {
    // The positive control for the mutant test above: the same machinery must
    // NOT refuse a well-formed chain, or the guard would be a wall rather than
    // a check and the test above would pass for the wrong reason.
    let exported = module_with(&["Demo.kept", "Demo.other"]);
    let private = module_with(&["Demo.kept", "Demo.other", "Demo.aux"]);

    let exported_view = OleanView::parse(&exported).expect("exported fixture parses");
    let private_view = OleanView::parse(&private).expect("private fixture parses");

    let constants = decode_chain_constants(&exported_view, &private_view, WalkBudget::default())
        .expect("a strict superset must be accepted");
    assert_eq!(constants.len(), 3, "the private array is what is returned");
}

#[test]
fn extra_const_names_contents_decode_and_agree_with_the_reported_count() {
    let lib = lib_or_skip!("extra_const_names_contents_decode_and_agree_with_the_reported_count");

    // (module, exported extraConstNames, chain extraConstNames) — measured at
    // the pin. `module_data` has always reported these counts; until now the
    // names behind them were unreachable, so the count is asserted alongside
    // the decoded contents to prove the two agree rather than drift.
    let expected = [
        ("Init/Data/List/ToArrayImpl", 1_usize, 2_usize),
        ("Init/Control/MonadAttach", 2, 7),
        ("Init/Prelude", 424, 713),
    ];

    for (relative, exported_count, chain_count) in expected {
        let chain = chain_bytes(&lib, relative);

        let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
        let exported_names = exported_view
            .extra_const_names(WalkBudget::default())
            .expect("exported extraConstNames decode");
        assert_eq!(
            exported_names.len(),
            exported_count,
            "{relative}: exported extraConstNames count moved at the pin"
        );
        assert_eq!(
            u64::try_from(exported_names.len()).expect("count fits"),
            exported_view
                .module_data(WalkBudget::default())
                .expect("exported ModuleData decodes")
                .extra_const_names,
            "{relative}: decoded contents disagree with the reported count"
        );

        let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
            .expect("server part parses against the exported region");
        let private_view =
            OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
                .expect("private part parses against the exported and server regions");
        let chain_names = private_view
            .extra_const_names(WalkBudget::default())
            .expect("chain extraConstNames decode");
        assert_eq!(
            chain_names.len(),
            chain_count,
            "{relative}: chain extraConstNames count moved at the pin"
        );

        // Every name must actually render; an empty or anonymous entry would
        // mean the array was walked but the names were not really decoded.
        for name in &chain_names {
            let rendered = name.to_display_string();
            assert!(
                !rendered.is_empty() && rendered != "[anonymous]",
                "{relative}: extraConstNames entry decoded to {rendered:?}"
            );
        }
    }
}

#[test]
fn decoded_extra_const_names_are_code_generator_names_not_declarations() {
    let lib = lib_or_skip!("decoded_extra_const_names_are_code_generator_names_not_declarations");
    let chain = chain_bytes(&lib, "Init/Data/List/ToArrayImpl");

    let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
        .expect("server part parses against the exported region");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against the exported and server regions");

    let extra: Vec<String> = private_view
        .extra_const_names(WalkBudget::default())
        .expect("chain extraConstNames decode")
        .iter()
        .map(|name| name.to_display_string())
        .collect();
    assert_eq!(
        extra,
        vec![
            "List.toArrayImpl._redArg".to_owned(),
            "List.toArrayAux._redArg".to_owned(),
        ],
        "the exact extraConstNames of this module at the pin"
    );

    // The load-bearing negative, and the reason this decode does not touch
    // franken_lean-timy's UnknownConstant rows: none of these names has a
    // ConstantInfo. Decoding them yields names the kernel can never admit.
    let constants: Vec<String> = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("chain constants decode")
        .iter()
        .map(|info| info.name().to_display_string())
        .collect();
    for name in &extra {
        assert!(
            !constants.contains(name),
            "{name} is in extraConstNames AND in constants; the pin's contract is \
             that these populations are disjoint"
        );
    }
    assert!(
        constants.contains(&TIMY_WITNESS.to_owned()),
        "the admissible auxiliary still comes from `constants`, not from \
         extraConstNames — that distinction is the whole of franken_lean-timy"
    );
}

#[test]
fn chain_decode_reports_origin_as_a_fact_not_as_a_name_prefix() {
    let lib = lib_or_skip!("chain_decode_reports_origin_as_a_fact_not_as_a_name_prefix");

    // (module, exported, private, private-only) — measured at the pin.
    let expected = [
        ("Init/Data/List/ToArrayImpl", 5_usize, 6_usize, 1_usize),
        ("Init/Data/Array/BasicAux", 8, 37, 29),
        ("Init/Control/MonadAttach", 29, 30, 1),
        ("Init/Prelude", 2204, 2314, 110),
    ];

    for (relative, exported_count, private_count, private_only_count) in expected {
        let chain = chain_bytes(&lib, relative);
        let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
        let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
            .expect("server part parses against the exported region");
        let private_view =
            OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
                .expect("private part parses against the exported and server regions");

        let chained = decode_chain_constants_with_origin(
            &exported_view,
            &private_view,
            WalkBudget::default(),
        )
        .expect("the pin's chains are supersets");

        assert_eq!(
            chained.constants.len(),
            private_count,
            "{relative}: constant count"
        );
        assert_eq!(
            chained.origins.len(),
            private_count,
            "{relative}: one origin per constant"
        );
        assert_eq!(
            chained.private_only().count(),
            private_only_count,
            "{relative}: private-only count"
        );
        assert_eq!(
            chained
                .origins
                .iter()
                .filter(|origin| **origin == ConstantOrigin::Exported)
                .count(),
            exported_count,
            "{relative}: exported-origin count must equal the exported array length"
        );
    }
}

#[test]
fn the_private_name_prefix_is_not_a_provenance_signal() {
    let lib = lib_or_skip!("the_private_name_prefix_is_not_a_provenance_signal");

    // THE DEFECT THIS API EXISTS FOR. `_private.` is Lean's mangling for a
    // private-SCOPED declaration; it says nothing about which part of the chain
    // carries it. Init/Data/AC exports declarations that are BOTH `_private.`-
    // prefixed and `.loop.`-bearing, so any consumer deciding provenance by
    // prefix classifies them as companion-recovered when they are exported.
    let chain = chain_bytes(&lib, "Init/Data/AC");
    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
        .expect("server part parses against the exported region");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against the exported and server regions");

    let chained =
        decode_chain_constants_with_origin(&exported_view, &private_view, WalkBudget::default())
            .expect("the pin's chain is a superset");

    let prefix_and_loop: Vec<String> = chained
        .constants
        .iter()
        .zip(&chained.origins)
        .filter(|(info, origin)| {
            **origin == ConstantOrigin::Exported && {
                let rendered = info.name().to_display_string();
                rendered.starts_with("_private.") && rendered.contains(".loop.")
            }
        })
        .map(|(info, _)| info.name().to_display_string())
        .collect();

    assert!(
        !prefix_and_loop.is_empty(),
        "Init.Data.AC must still export `_private.*.loop.*` declarations; without \
         them this test no longer witnesses the prefix/provenance gap"
    );
    for name in &prefix_and_loop {
        assert!(
            !chained
                .private_only()
                .any(|info| info.name().to_display_string() == *name),
            "{name} is reported both exported and private-only"
        );
    }
}

#[test]
fn the_parts_door_agrees_with_the_view_door_and_classifies_the_prelude_witnesses() {
    let lib = lib_or_skip!(
        "the_parts_door_agrees_with_the_view_door_and_classifies_the_prelude_witnesses"
    );
    let chain = chain_bytes(&lib, "Init/Prelude");

    let from_parts = decode_chain_constants_from_parts(
        &chain.exported,
        &chain.server,
        &chain.private,
        ChainLimits::default(),
    )
    .expect("the parts door decodes the pin's chain");

    // Same answer as the view door, or the convenience is a second
    // implementation rather than one call site.
    let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
    let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
        .expect("server part parses against the exported region");
    let private_view =
        OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
            .expect("private part parses against the exported and server regions");
    let from_views =
        decode_chain_constants_with_origin(&exported_view, &private_view, WalkBudget::default())
            .expect("the view door decodes the pin's chain");

    assert_eq!(from_parts.constants.len(), from_views.constants.len());
    assert_eq!(from_parts.origins, from_views.origins);
    assert_eq!(from_parts.constants.len(), 2314, "Init.Prelude at the pin");
    assert_eq!(from_parts.private_only().count(), 110);

    // The two declarations WAVE 12 named. Both are `_private.`-prefixed AND
    // `.loop.`-bearing AND exported, so a prefix test calls them
    // companion-recovered. The chain says otherwise, and that is the whole
    // reason this API exists.
    let witnesses = [
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
    ];
    for witness in witnesses {
        let index = from_parts
            .constants
            .iter()
            .position(|info| info.name().to_display_string() == witness)
            .unwrap_or_else(|| panic!("{witness} must be in Init.Prelude's chain at the pin"));
        assert_eq!(
            from_parts.origins[index],
            ConstantOrigin::Exported,
            "{witness} is exported; reporting it private-only is the misclassification \
             that failed the .loop family"
        );
        assert!(
            !from_parts
                .private_only()
                .any(|info| info.name().to_display_string() == witness),
            "{witness} must not appear in private_only()"
        );
    }
}

/// `._eq_<digits>` is not a declaration shape the pinned Reference emits.
///
/// The family tables above deliberately do NOT list it. That omission is a
/// measurement, not an oversight, and this test is what makes it one: across
/// every Init module with a complete companion chain, no declaration in
/// `constants` and no name in `extraConstNames` has a final component of the
/// form `_eq_<digits>`. Corpus-wide over all 2,431 chained modules the count is
/// also zero.
///
/// A family row for a shape the pin never emits cannot be satisfied by any
/// decoder: the per-family harnesses select a private-only representative and
/// panic when none exists, so such a row fails for a reason that has nothing to
/// do with decode. Asserting the absence keeps the fact in the suite while
/// letting the tables describe only families that exist.
#[test]
fn the_underscore_eq_n_shape_is_absent_from_the_pin() {
    let lib = lib_or_skip!("the_underscore_eq_n_shape_is_absent_from_the_pin");

    // The near neighbour that DOES exist, asserted first so this test cannot
    // pass because the predicate or the corpus walk silently matched nothing.
    let mut eq_n_seen = 0_usize;
    let mut underscore_eq_n = Vec::new();

    for relative in init_chain_modules(&lib) {
        let chain = chain_bytes(&lib, &relative);
        let exported_view = OleanView::parse(&chain.exported).expect("exported part parses");
        let _server_view = OleanView::parse_with_dependencies(&chain.server, &[&chain.exported])
            .expect("server part parses against the exported region");
        let private_view =
            OleanView::parse_with_dependencies(&chain.private, &[&chain.exported, &chain.server])
                .expect("private part parses against the exported and server regions");

        let module = private_view
            .module_data(WalkBudget::default())
            .expect("private ModuleData decodes");
        let extra = private_view
            .extra_const_names(WalkBudget::default())
            .expect("extraConstNames decode");

        for name in module.const_names.iter() {
            if family::eq_n(name) {
                eq_n_seen += 1;
            }
            if family::private_eq_n(name) {
                underscore_eq_n.push(format!("{relative}: {name} (constants)"));
            }
        }
        for name in &extra {
            let rendered = name.to_display_string();
            if family::private_eq_n(&rendered) {
                underscore_eq_n.push(format!("{relative}: {rendered} (extraConstNames)"));
            }
        }
        let _ = &exported_view;
    }

    assert_eq!(
        eq_n_seen, 3_449,
        "the `.eq_<digits>` family is the live neighbour; if this moved, the \
         negative below is measuring a different corpus than it claims"
    );
    assert!(
        underscore_eq_n.is_empty(),
        "`._eq_<digits>` now exists at the pin, so the family tables above are \
         missing a real family: {underscore_eq_n:?}"
    );
}

#[test]
fn a_companion_part_read_without_its_dependencies_is_a_typed_refusal() {
    let lib = lib_or_skip!("a_companion_part_read_without_its_dependencies_is_a_typed_refusal");
    let chain = chain_bytes(&lib, "Init/Data/List/ToArrayImpl");

    // The private region's stored pointers retain the exported region's
    // compacted addresses. Read standalone, those are out-of-region pointers and
    // must become a typed RegionError — never a panic, and never a
    // silently-partial constant array that would look like a decode result.
    let view = OleanView::parse(&chain.private).expect("the private part has a valid header");
    let error = view
        .module_data(WalkBudget::default())
        .expect_err("a standalone private part must refuse its external pointers");
    let rendered = format!("{error}");
    assert!(
        rendered.contains("out of bounds"),
        "expected an out-of-region pointer refusal, got: {rendered}"
    );
}
