//! Structural regression laws for the evidence publisher's finalization order.

#![forbid(unsafe_code)]

use std::fs;
use std::path::Path;

fn check_script() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/check.sh");
    fs::read_to_string(path).expect("scripts/check.sh must be readable")
}

#[test]
fn terminal_human_log_is_sealed_before_manifest_generation() {
    let script = check_script();
    let note = script
        .split_once("note() {\n")
        .expect("check.sh must define note")
        .1
        .split_once("\n}\n\nset_final()")
        .expect("check.sh note must end before set_final")
        .0;
    let finalizer = script
        .split_once("on_exit() {\n")
        .expect("check.sh must define on_exit")
        .1
        .split_once("\n}\n\ntrap 'on_signal HUP 129' HUP")
        .expect("check.sh on_exit must end before the signal traps")
        .0;

    let terminal_append = finalizer
        .find(
            r#"note "terminal verdict=$FINAL_VERDICT reason=$FINAL_REASON process_exit=$FINAL_EXIT""#,
        )
        .expect("the finalizer must append its terminal human record");
    let human_seal = finalizer[terminal_append..]
        .find("HUMAN_LOG_SEALED=1")
        .map(|offset| terminal_append + offset)
        .expect("the finalizer must seal human.log after its terminal record");
    let manifest_generation = finalizer
        .find(r#"run_finalizer_command python3 "$EVIDENCE" manifest"#)
        .expect("the finalizer must generate an evidence manifest");

    let sealed_note_branch = note
        .find(r#"if [ "$HUMAN_LOG_SEALED" -eq 1 ]; then"#)
        .expect("note must recognize a sealed human log");
    let sealed_note_return = note[sealed_note_branch..]
        .find("return 0")
        .map(|offset| sealed_note_branch + offset)
        .expect("sealed note handling must return without appending");
    let human_append = note
        .find(r#"tee -a "$HUMAN""#)
        .expect("unsealed notes must append to human.log");

    assert!(
        terminal_append < human_seal && human_seal < manifest_generation,
        "human.log must receive its terminal record and be sealed before the manifest inventories it"
    );
    assert!(
        sealed_note_branch < sealed_note_return && sealed_note_return < human_append,
        "post-seal notes must return after stderr output and before the human.log append path"
    );
}
