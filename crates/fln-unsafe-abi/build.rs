fn main() {
    // The G0-3 plugin e2e (tests.rs `door_loads_a_reference_built_plugin_end_to_end`)
    // dlopens a Reference-built shared library under RTLD_NOW, so every lean_*
    // symbol the plugin imports must resolve against THIS test binary's exports —
    // which requires the exported symbols in the dynamic symbol table. The plain
    // link-arg form is used because the unit tests live in the lib (no tests/
    // target for the -tests form); this crate is rlib-only, so the only linked
    // artifacts are its test binaries and the flag reaches nothing else;
    // release artifacts get their link story from the product door (franken_lean-sno).
    println!("cargo:rustc-link-arg=-rdynamic");
}
