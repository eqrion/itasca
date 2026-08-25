# Helpers for the Rust -> Charon -> Aeneas -> Coq pipeline.
#
# Coq builds go through Makefile.coq so dependencies are tracked. Register new
# theory files in _CoqProject, not here.

opam_prefix := `opam var prefix --switch=wasmcert 2>/dev/null`
coqbin := opam_prefix / "bin"
coqflags := "-R theories Itasca -R vendor/aeneas/backends/coq Itasca -R vendor/WasmCert-Coq/_build/default/theories Wasm"
njobs := `nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4`

# List available recipes.
default:
    @just --list

# Compile one theory file and whatever it depends on.
check file:
    @make -f Makefile.coq COQBIN={{ coqbin }}/ -j{{ njobs }} {{ without_extension(file) }}.vo

# Compile every theory file.
prove:
    @make prove

# Iterate on one lemma in theories/Scratch.v (gitignored).
scratch:
    # Direct coqc rather than `just check`: Scratch.v is gitignored so it
    # cannot be registered in _CoqProject, and Makefile.coq only knows about
    # registered files. Its dependencies are already-built .vo files.
    @{{ coqbin }}/coqc {{ coqflags }} theories/Scratch.v

# Run the Rust tests.
test:
    @cargo test

# Print the axioms a theorem transitively depends on.
assumptions module theorem:
    #!/bin/sh
    # Kernel bypasses show up as "assumed to be guarded" and "assumed to be
    # positive" lines. Example: just assumptions OpIter_Validate validate_body_sound
    set -eu
    tmp=$(mktemp -d "${TMPDIR:-/tmp}/itasca.XXXXXX")
    trap 'rm -rf "$tmp"' EXIT
    printf 'Require Import Itasca.%s.\nPrint Assumptions %s.\n' \
        '{{ module }}' '{{ theorem }}' > "$tmp/PrintAx.v"
    {{ coqbin }}/coqc {{ coqflags }} "$tmp/PrintAx.v"

# Show the slowest sentences in a theory file.
profile file:
    #!/bin/sh
    # How a quadratic tactic chain that cost 116 of 119 seconds in one file
    # was found.
    set -eu
    out=$(mktemp "${TMPDIR:-/tmp}/itasca.XXXXXX")
    trap 'rm -f "$out"' EXIT
    {{ coqbin }}/coqc -time {{ coqflags }} '{{ file }}' > "$out" 2>&1 || true
    echo "--- slowest sentences (secs, tactic) ---"
    rg -o '^Chars [0-9]+ - [0-9]+ \[(\S+)\] ([0-9.]+) secs' -r '$2  $1' "$out" \
        | sort -rn | head -20
    printf 'total sentence time: '
    rg -o '\] ([0-9.]+) secs' -r '$1' "$out" | awk '{s+=$1} END {print s" s"}'

# Rust -> LLBC -> extracted Coq.
extract:
    @make coq

# The extraction must be free of kernel bypasses.
extract-check: extract
    #!/bin/sh
    # Held since the AST checker was deleted: nothing left in the Rust is
    # recursive over a Vec.
    set -eu
    files="theories/Itasca_Types.v theories/Itasca_Funs.v"
    if rg -q 'Unset (Guard|Positivity) Checking' $files; then
        echo "FAIL: extraction contains kernel bypasses:"
        rg -n 'Unset (Guard|Positivity) Checking' $files
        exit 1
    fi
    echo "OK: no Unset Guard/Positivity Checking in the extraction"

# Compare the hand-written externals against what Aeneas asks for.
externals-check:
    #!/bin/sh
    # Itasca_FunsExternal.v is hand-written; Aeneas only emits a template
    # naming the axioms it needs. A missing one already fails the Coq build with
    # an unknown identifier, but a stale one just sits in the trust base
    # unnoticed, so compare both directions. A handful of extras are ours by
    # design (the loop combinator and friends); the point is to notice new ones.
    set -eu
    template=theories/Itasca_FunsExternal_Template.v
    if [ ! -f "$template" ]; then
        echo "$template is missing; run 'just extract' first" >&2
        exit 1
    fi
    tmp=$(mktemp -d "${TMPDIR:-/tmp}/itasca.XXXXXX")
    trap 'rm -rf "$tmp"' EXIT
    rg -U -o '^Axiom\s+([A-Za-z_0-9]+)' -r '$1' "$template" | sort > "$tmp/want"
    rg -U -o '^Axiom\s+([A-Za-z_0-9]+)' -r '$1' \
        theories/Itasca_FunsExternal.v | sort > "$tmp/have"
    missing=$(comm -23 "$tmp/want" "$tmp/have")
    extra=$(comm -13 "$tmp/want" "$tmp/have")
    if [ -n "$extra" ]; then
        echo "not requested by Aeneas (ours, or stale):"
        echo "$extra" | sed 's/^/  /'
    fi
    if [ -n "$missing" ]; then
        echo "FAIL: requested by Aeneas but not defined:"
        echo "$missing" | sed 's/^/  /'
        exit 1
    fi
    echo "OK: every axiom Aeneas asks for is defined"

# Print the trust base of each key theorem, for TRUST.md.
trust:
    #!/bin/sh
    set -eu
    printf '%-46s %8s %10s\n' THEOREM AXIOMS BYPASSES
    for pair in \
        Spec_Binary:repr_ops_det \
        Spec_Binary:repr_op_prefix \
        OpIter_Decode:read_u32_leb_sound \
        OpIter_Decode:read_s32_leb_sound \
        OpIter_Decode:read_u32_leb_complete \
        OpIter_Decode:read_s32_leb_complete \
        OpIter_Decode:read_s64_leb_sound \
        OpIter_Decode:read_s64_leb_complete \
        OpIter_Decode:read_f32_bits_sound \
        OpIter_Decode:read_f64_bits_complete \
        OpIter_Decode:read_op_sound \
        OpIter_Decode:read_memarg_sound \
        OpIter_Decode:read_u32_leb_span \
        OpIter_State:push_types_pos \
        OpIter_Sim:ctx_at_label_lookup \
        OpIter_Sim:step_end_block \
        OpIter_Sim:step_switch_else \
        OpIter_Sim:step_end_then \
        OpIter_Sim:step_br \
        OpIter_Sim:step_br_table \
        Spec_Expr:repr_expr_det \
        Spec_Expr:repr_expr_det_rest \
        Spec_Expr:repr_expr_prefix \
        Spec_Module:repr_module_det \
        Spec_Module:repr_code_prefix \
        OpIter_Table:convert_types_spec \
        OpIter_Table:binary_types_spec \
        OpIter_Table:op_spec_handled \
        OpIter_Table:visit_numeric_names_convert \
        OpIter_Table:visit_numeric_names_binary \
        OpIter_Table:visit_memory_names_load \
        OpIter_Table:visit_memory_names_store \
        OpIter_Visit:nop_hooks_total \
        OpIter_Visit:nop_hooks_accept \
        OpIter_Table:trace_records \
        OpIter_NoPanic:validate_body_no_panic \
        OpIter_NoPanic:validate_body_with_no_panic \
        OpIter_Validate:step_op_step \
        OpIter_Validate:validate_body_sound \
        OpIter_Validate:validate_body_checker \
        OpIter_Validate:validate_body_typed \
        OpIter_Validate:validate_body_with_typed \
        OpIter_Validate:validate_body_with_trace \
        OpIter_Validate:validate_body_trace \
        OpIter_Checker:pop_with_type_complete \
        OpIter_Readers:read_end_complete \
        OpIter_Complete:step_complete \
        OpIter_Complete:validate_body_complete \
        OpIter_Complete:validate_body_with_complete \
        OpIter_Driven:validate_body_with_transfer \
        OpIter_Driven:validate_body_driven \
        OpIter_Driven:validate_body_accepts \
        Module_NoPanic:validate_module_no_panic \
        Module_NoPanic:validate_env_ok \
        Module_NoPanic:validate_tail_ok \
        Module_NoPanic:read_section_header_span \
        Module_NoPanic:code_entry_extent_span \
        Module_NoPanic:code_section_span \
        Module_Sound:validate_module_repr \
        Module_Sound:validate_code_entry_with_sound \
        Module_Sound:code_section_sound \
        Module_Sound:code_entry_extent_frames \
        Module_Sound:validate_code_driven \
        Module_Sound:validate_module_driven \
        Module_Sound:validate_code_with_sound \
        Module_NoPanic:validate_code_with_ok \
        Module_Complete:validate_code_with_complete \
        Module_NoPanic:validate_code_entry_with_ok \
        Module_Externs:import_types_externs \
        Module_Externs:export_types_externs \
        Module_Typing:validate_module_checked \
        Module_Typing:validate_module_typed \
        Module_Complete:decode_bytevec_complete \
        Module_Complete:decode_func_type_complete \
        Module_Complete:validate_limits_complete \
        Module_Complete:utf8_sequence_len_complete \
        Module_Complete:decode_name_complete \
        Module_Complete:read_header_complete \
        Module_Complete:read_section_header_complete \
        Module_Complete:decode_custom_section_complete \
        OpIter_Table:op_spec_invert \
        Module_Complete:decode_const_expr_complete \
        Module_Complete:decode_type_section_complete \
        Module_Complete:decode_import_section_complete \
        Module_Complete:decode_function_section_complete \
        Module_Complete:decode_table_section_complete \
        Module_Complete:decode_memory_section_complete \
        Module_Complete:decode_global_section_complete \
        Module_Complete:decode_export_section_complete \
        Module_Complete:decode_start_section_complete \
        Module_Complete:decode_element_section_complete \
        Module_Complete:decode_data_section_complete \
        Module_Complete:validate_tail_complete \
        Module_Complete:decode_and_build_locals_complete \
        Module_Complete:validate_code_entry_complete \
        Module_Complete:validate_code_complete \
        Module_Complete:validate_env_with_loop_complete \
        Module_Complete:validate_env_complete \
        Module_Complete:validate_code_entry_with_complete \
        Module_Complete:validate_module_complete \
        Module_Wasm10:const_exprs_one \
        Module_Wasm10:module_wasm10_of_checker \
        Module_Wasm10:validate_module_typechecked \
        Module_Driven:validate_code_entry_driven \
        Module_Driven:validate_code_entry_accepts \
        Module_Driven:validate_env_with_accepts \
        Module_Driven:validate_tail_with_accepts \
        Module_Driven:validate_code_with_accepts \
        Module_Driven:entry_recorder_records \
        Module_Driven:validate_code_with_deferred \
        Module_Driven:validate_code_recorded \
        Module_Driven:validate_module_of_parts \
        Module_Driven:validate_module_with_accepts \
        Module_Driven:validate_module_with_no_panic \
        Module_Driven:validate_module_with_complete \
        Module_Driven:validate_module_parts_typed \
        Module_Driven:validate_module_deferred_typed \
        Module_Sound:validate_env_lines \
        Module_Sound:tail_chain_no_code \
        Module_Typing:validate_module_regions_typed \
        Module_Driven:validate_module_regions_deferred_typed
    do
        m="${pair%%:*}"; t="${pair##*:}"
        out=$(just assumptions "$m" "$t" 2>/dev/null)
        n=$(printf '%s\n' "$out" | grep -c '^[A-Za-z]' || echo 1)
        k=$(printf '%s\n' "$out" | grep -c 'guarded\|positive' || true)
        printf '%-46s %8s %10s\n' "$m.$t" "$((n-1))" "${k:-0}"
    done
