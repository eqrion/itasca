import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Sim.Structured

/-!
Sections, each formerly its own module: FrameStack, CompiledFunctions, ControlPoint, StackRelation, FrameStoreMetadata.
-/

/-! ## FrameStack -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Code safety and exact retained store lookups for a concrete frame. -/
structure FrameProgram {M : Type} (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (locals results : List valtype) (functions : List functype) : Prop where
  lookup : ∃ inst, store.instances.val[raw.instance.val]? = some inst ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    FunctionTable store inst functions
  checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true
  fetchBound : compiled.code.val.length ≤ U32.max
  localSlots : compiled.local_slots.val = Compiler.slots locals
  epilogue : ∃ pc count : U32, compiled.code.val.length = pc.val + 1 ∧
    compiled.code.val[pc.val]? = some (.Return compiled.local_slots count)

end Itasca.Runtime.Interp

end

/-! ## CompiledFunctions -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A frame's retained signature list belongs to its actual instance. -/
theorem FrameProgram.function_table {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions}
    (program : FrameProgram store raw compiled locals results functions)
    (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst) :
    FunctionTable store inst functions := by
  obtain ⟨actual, found, _, table⟩ := program.lookup
  have same : actual = inst := Option.some.inj (found.symm.trans lookup)
  exact same ▸ table

/-- Resolving a compiler CALL signature exposes the exact issued raw address,
function entry, and canonical signature consumed by interpreter dispatch. -/
theorem FrameProgram.resolve_call {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions}
    (program : FrameProgram store raw compiled locals results functions)
    (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst)
    (index : Nat) (ty : functype) (signature : functions[index]? = some ty) :
    ∃ address function rawType, inst.funcs.val[index]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some rawType ∧ Store.decodeFuncType rawType = ty :=
  (program.function_table inst lookup).resolve index ty signature

end Itasca.Runtime.Interp

end

/-! ## ControlPoint -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Simulation counts positive SpecTec reductions and explicitly measures all
concrete administrative dispatches. -/
def ConcreteSim (codeLength : Nat) (beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (before after : SourceMachine.AState) : Prop :=
  (SourceMachine.decode before = SourceMachine.decode after ∧
    dispatchMeasure afterPending codeLength afterPC after < dispatchMeasure beforePending codeLength beforePC before) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (SourceMachine.decode before) [] (SourceMachine.decode after)

theorem dispatch_measure_source_any {before after : SourceMachine.AState}
    (beforePending afterPending : Bool) (codeLength pc target : Nat)
    (decrease : SourceMachine.administrativeMeasure after < SourceMachine.administrativeMeasure before) :
    dispatchMeasure afterPending codeLength target after < dispatchMeasure beforePending codeLength pc before := by
  have adjacent : SourceMachine.administrativeMeasure after + 1 ≤ SourceMachine.administrativeMeasure before := decrease
  have multiplied := Nat.mul_le_mul_right (2 * (codeLength + 1)) adjacent
  simp only [Nat.add_mul, Nat.one_mul] at multiplied
  cases beforePending <;> cases afterPending <;>
    simp only [dispatchMeasure, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem ConcreteSim.of_source {before after : SourceMachine.AState}
    (codeLength beforePC afterPC : Nat) (beforePending afterPending : Bool)
    (simulation : SourceMachine.NextSim before after) :
    ConcreteSim codeLength beforePC afterPC beforePending afterPending before after := by
  rcases simulation with ⟨same, decrease⟩ | ⟨n, positive, steps⟩
  · exact Or.inl ⟨same, dispatch_measure_source_any beforePending afterPending codeLength beforePC afterPC decrease⟩
  · exact Or.inr ⟨n, positive, steps⟩

end Itasca.Runtime.Interp

end

/-! ## StackRelation -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The compiler's code-length certificate rules out PC increment overflow
whenever the interpreter fetches an actual instruction. -/
theorem FrameProgram.fetched_bound {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions} (program : FrameProgram store raw compiled locals results functions)
    (instruction : runtime.bytecode.Instr)
    (fetched : compiled.code.val[raw.pc.val]? = some instruction) : raw.pc.val < U32.max := by
  have bound := (List.getElem?_eq_some_iff.mp fetched).1
  exact lt_of_lt_of_le bound program.fetchBound

end Itasca.Runtime.Interp

end

/-! ## FrameStoreMetadata -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Runtime content mutations preserve the metadata used by every active or
suspended compiled frame. Object payloads and resource counters may change. -/
structure FrameStoreMetadata {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  functions : after.funcs = before.funcs
  types : after.types = before.types
  instances : after.instances = before.instances

theorem FrameStoreMetadata.refl {M : Type} (store : runtime.store.Store M) :
    FrameStoreMetadata store store := ⟨rfl,rfl,rfl,rfl⟩

theorem FrameStoreMetadata.decode_instance {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) (inst : runtime.store.ModuleInst) :
    Store.decodeInstance after inst = Store.decodeInstance before inst := by
  simp only [Store.decodeInstance, metadata.types]

theorem FunctionTable.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {inst functions}
    (table : FunctionTable before inst functions) : FunctionTable after inst functions := by
  simpa only [FunctionTable, metadata.identity, metadata.functions, metadata.types] using table

theorem FrameBinding.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {exec raw source}
    (binding : FrameBinding before exec raw source) : FrameBinding after exec raw source := by
  simpa only [FrameBinding, metadata.identity, metadata.functions, metadata.types,
    metadata.instances, metadata.decode_instance] using binding

theorem FrameProgram.store_metadata {M : Type} {before after : runtime.store.Store M}
    (metadata : FrameStoreMetadata before after) {raw compiled locals results functions}
    (program : FrameProgram before raw compiled locals results functions) :
    FrameProgram after raw compiled locals results functions := by
  refine ⟨?_,program.checked,program.fetchBound,program.localSlots,program.epilogue⟩
  obtain ⟨inst,found,code,table⟩ := program.lookup
  exact ⟨inst,by simpa only [metadata.instances] using found,code,table.store_metadata metadata⟩

end Itasca.Runtime.Interp

end
