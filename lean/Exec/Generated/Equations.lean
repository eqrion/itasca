import Exec.Generated.Funs

/-! Shared equation lemmas for the generated runtime. Import this module instead
of `Exec.Generated.Funs`.

The functions below match on every `runtime.bytecode.Instr` constructor and share
one 432-alternative matcher. Lean generates the matcher's equation lemmas on
demand, privately to the requesting module, and their size is quadratic in the
number of alternatives (about 45 MiB). Generating the public equation lemmas of
these functions here lets every importer rewrite with them without regenerating
the matcher equations. -/

open Lean Meta in
set_option maxHeartbeats 0 in
run_meta do
  let functions := [``Exec.runtime.interp.dispatch, ``Exec.runtime.interp.scalar_operands,
    ``Exec.runtime.interp.load_operands, ``Exec.runtime.interp.store_operands,
    ``Exec.runtime.interp.simd_operands, ``Exec.runtime.interp.bulk.execute,
    ``Exec.runtime.bytecode.Instr.scalar, ``Exec.runtime.bytecode.Instr.load,
    ``Exec.runtime.bytecode.Instr.store, ``Exec.runtime.bytecode.Instr.simd,
    ``Exec.runtime.bytecode.Instr.retarget, ``Exec.runtime.bytecode.is_return,
    ``Exec.runtime.bytecode.CompiledFunction.other_valid]
  for function in functions do
    discard <| getEqnsFor? function
