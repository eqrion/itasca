import Itasca.Generated.Funs

/-! Shared equation lemmas for the generated runtime. Import this module instead
of `Itasca.Generated.Funs`.

The functions below match on every `runtime.bytecode.Instr` constructor and share
one 432-alternative matcher. Lean generates the matcher's equation lemmas on
demand, privately to the requesting module, and their size is quadratic in the
number of alternatives (about 45 MiB). Generating the public equation lemmas of
these functions here lets every importer rewrite with them without regenerating
the matcher equations. -/

open Lean Meta in
set_option maxHeartbeats 0 in
run_meta do
  let functions := [``Itasca.runtime.interp.dispatch, ``Itasca.runtime.interp.scalar_operands,
    ``Itasca.runtime.interp.load_operands, ``Itasca.runtime.interp.store_operands,
    ``Itasca.runtime.interp.simd_operands, ``Itasca.runtime.interp.bulk.execute,
    ``Itasca.runtime.bytecode.Instr.scalar, ``Itasca.runtime.bytecode.Instr.load,
    ``Itasca.runtime.bytecode.Instr.store, ``Itasca.runtime.bytecode.Instr.simd,
    ``Itasca.runtime.bytecode.Instr.retarget, ``Itasca.runtime.bytecode.is_return,
    ``Itasca.runtime.bytecode.CompiledFunction.other_valid]
  for function in functions do
    discard <| getEqnsFor? function
