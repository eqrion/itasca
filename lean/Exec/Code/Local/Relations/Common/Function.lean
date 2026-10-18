import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Code.Local.Relations.Common.LayoutProofs
import Itasca.Support.TypeTranslation
namespace Exec.Code
open Aeneas.Std

/-- The function's implicit body label branches to its epilogue. -/
def rootLabel (results : List valtype) (epilogue : U32) : LabelTarget :=
  ⟨[], results, results, epilogue, epilogue.val, [], [], true, true⟩

/-- The actual epilogue determines whether the implicit root exit carries
its declared results. Dead nonvoid bodies may retain a zero-width epilogue. -/
def functionRootLabel (results : List valtype) (compiled : runtime.bytecode.CompiledFunction)
    (epilogue : U32) : LabelTarget :=
  let live := match compiled.code.val[epilogue.val]? with
    | some (.Return _ count) => decide (count.val = slots results)
    | _ => false
  ⟨[], results, results, epilogue, epilogue.val, [], [], live, live⟩

theorem functionRootLabel_live {results compiled epilogue src count}
    (found : compiled.code.val[epilogue.val]? = some (.Return src count))
    (live : (functionRootLabel results compiled epilogue).branchLive = true) :
    count.val = slots results := by
  simpa only [functionRootLabel, found, decide_eq_true_eq] using live

/-- Complete retained syntax/layout evidence for one defined function. The
well-formedness field is the actual bytecode check, not execution correctness. -/
structure FunctionCode (typeTable functions : List functype)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop where
  signature : typeTable[compiled.type_index.val]? = some ⟨.mk_list params, .mk_list results⟩
  locals : compiled.locals.val.map Itasca.Translate.valueType = params ++ declared
  parameterSlots : compiled.param_slots.val = slots params
  localSlots : compiled.local_slots.val = slots (params ++ declared)
  capacity : compiled.local_slots.val ≤ compiled.slot_count.val
  fetchBound : compiled.code.val.length ≤ U32.max
  checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true
  bodyCode : CodeRel typeTable functions results (params ++ declared) compiled.code.val
    [functionRootLabel results compiled epilogue] [] body 0 epilogue.val results
  returnCode : ∃ count, compiled.code.val[epilogue.val]? = some (.Return compiled.local_slots count)
  endPosition : compiled.code.val.length = epilogue.val + 1

/-- Initial execution receives the body's structured point and the implicit
label's source continuation at the checked epilogue. -/
theorem FunctionCode.entry {typeTable functions params declared results body compiled epilogue}
    (certificate : FunctionCode typeTable functions params declared results body compiled epilogue) :
    StructuredPoint typeTable functions results (params ++ declared) compiled.code.val
      [functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  have bound : epilogue.val ≤ compiled.code.val.length := by have := certificate.endPosition; omega
  have root (live : (functionRootLabel results compiled epilogue).branchLive = true) :
      RootAligned compiled.code.val results [] epilogue.val results := by
    intro _
    obtain ⟨count, found⟩ := certificate.returnCode
    exact ⟨certificate.endPosition.symm, rfl, compiled.local_slots, count,
      functionRootLabel_live found live, found⟩
  refine ⟨certificate.bodyCode, ?_, ?_, ExitAligned.cons _ _, RootAligned.cons _ _ _ _ _ _⟩
  · apply LabelContinuations.cons
    · intro depth label lookup; simp at lookup
    · intro _
      exact CodeRel.nil [] _ _ bound NormalLive.nil
    · intro _ label lookup; simp at lookup
    · exact root
  · apply NormalContinuations.cons
    · intro depth label lookup; simp at lookup
    · intro _
      exact CodeRel.nil [] _ _ bound NormalLive.nil
    · intro _ label lookup; simp at lookup
    · exact root

theorem FunctionCode.epilogue_bound {typeTable functions params declared results body compiled epilogue}
    (certificate : FunctionCode typeTable functions params declared results body compiled epilogue) :
    epilogue.val < U32.max := by
  have := certificate.fetchBound
  have := certificate.endPosition
  omega
end Exec.Code
