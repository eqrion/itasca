import Exec.Code.Local.Control.Table.StructuredCodeWithTablesLabels
import Exec.Code.Local.Control.Table.StructuredCodeTableEmbedding
import Exec.Code.Local.Control.Common.StructuredFunction
import Exec.Code.Local.Relations.Common.LayoutProofs
import Itasca.Support.TypeTranslation
import Exec.Code.Local.Relations.Common.Function
namespace Exec.Code
open Aeneas.Std
/-- Complete retained syntax/layout evidence for one defined function. The
well-formedness field is the actual bytecode check, not execution correctness. -/
structure StructuredFunctionCodeWithTables (emit : List valtype → instr → List Bytecode → List valtype → Prop) (typeTable functions : List functype)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop where
  signature : typeTable[compiled.type_index.val]? = some ⟨.mk_list params, .mk_list results⟩
  locals : compiled.locals.val.map Itasca.Translate.valueType = params ++ declared
  parameterSlots : compiled.param_slots.val = slots params
  localSlots : compiled.local_slots.val = slots (params ++ declared)
  capacity : compiled.local_slots.val ≤ compiled.slot_count.val
  fetchBound : compiled.code.val.length ≤ U32.max
  checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true
  bodyCode : StructuredCodeWithTables emit typeTable functions results (params ++ declared) compiled.code.val compiled.jump_tables.val
    [functionRootLabel results compiled epilogue] [] body 0 epilogue.val results
  returnCode : ∃ count, compiled.code.val[epilogue.val]? = some (.Return compiled.local_slots count)
  endPosition : compiled.code.val.length = epilogue.val + 1

/-- Initial execution receives the body's structured point and the implicit
label's source continuation at the checked epilogue. -/
theorem StructuredFunctionCodeWithTables.entry {emit typeTable functions params declared results body compiled epilogue}
    (certificate : StructuredFunctionCodeWithTables emit typeTable functions params declared results body compiled epilogue) :
    StructuredCodeWithTables.Point emit typeTable functions results (params ++ declared) compiled.code.val compiled.jump_tables.val
      [functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  have bound : epilogue.val ≤ compiled.code.val.length := by have := certificate.endPosition; omega
  have root (live : (functionRootLabel results compiled epilogue).branchLive = true) :
      RootAligned compiled.code.val results [] epilogue.val results := by
    intro _
    obtain ⟨count, found⟩ := certificate.returnCode
    exact ⟨certificate.endPosition.symm, rfl, compiled.local_slots, count,
      functionRootLabel_live found live, found⟩
  refine ⟨certificate.bodyCode, ?_, ?_, ExitAligned.cons _ _, RootAligned.cons _ _ _ _ _ _⟩
  · apply StructuredCodeWithTables.Targets.cons
    · intro depth label lookup; simp at lookup
    · intro _
      exact StructuredCodeWithTables.nil [] _ _ bound NormalLive.nil
    · intro _ label lookup; simp at lookup
    · exact root
  · apply StructuredCodeWithTables.Normals.cons
    · intro depth label lookup; simp at lookup
    · intro _
      exact StructuredCodeWithTables.nil [] _ _ bound NormalLive.nil
    · intro _ label lookup; simp at lookup
    · exact root

theorem StructuredFunctionCodeWithTables.epilogue_bound {emit typeTable functions params declared results body compiled epilogue}
    (certificate : StructuredFunctionCodeWithTables emit typeTable functions params declared results body compiled epilogue) :
    epilogue.val < U32.max := by
  have := certificate.fetchBound
  have := certificate.endPosition
  omega
theorem StructuredFunctionCode.with_tables {emit typeTable functions params declared results body compiled epilogue}
    (certificate : StructuredFunctionCode emit typeTable functions params declared results body compiled epilogue)
    (ordinary : ∀ before instruction emitted after, emit before instruction emitted after →
      ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredFunctionCodeWithTables emit typeTable functions params declared results body compiled epilogue := by
  rcases certificate with ⟨signature,locals,parameterSlots,localSlots,capacity,fetchBound,checked,bodyCode,returnCode,endPosition⟩
  exact ⟨signature,locals,parameterSlots,localSlots,capacity,fetchBound,checked,
    bodyCode.with_tables compiled.jump_tables.val ordinary,returnCode,endPosition⟩
end Exec.Code
