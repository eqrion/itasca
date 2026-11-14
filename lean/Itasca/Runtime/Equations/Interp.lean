import Itasca.Generated.FunsInterp
import Itasca.Runtime.Equations.Bytecode

/-! Equation lemmas for interpreter dispatch. Runtime execution proofs use these
without regenerating the large instruction matcher in each consumer. -/

open Lean Meta in
run_meta do
  let functions := [``Itasca.runtime.interp.dispatch,
    ``Itasca.runtime.interp.scalar_operands,
    ``Itasca.runtime.interp.load_operands,
    ``Itasca.runtime.interp.store_operands,
    ``Itasca.runtime.interp.simd_operands,
    ``Itasca.runtime.interp.bulk.execute]
  for function in functions do
    discard <| getEqnsFor? function
