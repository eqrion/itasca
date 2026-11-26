import Itasca.Generated.Funs
import Itasca.Runtime.Equations.Bytecode

/-! Equation lemmas for interpreter dispatch. Runtime execution proofs use these
without regenerating the large instruction matcher in each consumer. -/

run_meta Itasca.Automation.emitInstructionEquations ``Itasca.runtime.interp.dispatch
run_meta Itasca.Automation.emitInstructionEquations ``Itasca.runtime.interp.scalar_operands
run_meta Itasca.Automation.emitInstructionEquations ``Itasca.runtime.interp.load_operands
run_meta Itasca.Automation.emitInstructionEquations ``Itasca.runtime.interp.store_operands
run_meta Itasca.Automation.emitInstructionEquations ``Itasca.runtime.interp.simd_operands
run_meta Itasca.Automation.emitInstructionEquations ``Itasca.runtime.interp.bulk.execute
