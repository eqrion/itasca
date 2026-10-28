import Itasca.Runtime.Interp.StructuredMachine.SimdPoint
import Itasca.Runtime.Interp.StructuredMachine.SimdContinue
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdSignature
import Itasca.Runtime.Abs.Simd.Transition

namespace Itasca.Runtime.Interp.StructuredMachine.Simd
open Aeneas.Std SpecExt Itasca.Runtime.Spec

theorem instruction_operands {s : store} {f : Abs.AFrame} {after : List instr}
    {C opcode immediate input source output frontTypes}
    (meaning : Code.SimdImmediateMeaning C opcode immediate input source output)
    (typed : Abs.FrameTyped s {f with code := source :: after} [])
    (stack : f.vals.map Code.valueType = frontTypes ++ input) :
    ∃ front operands, f.vals = front ++ operands ∧ front.map Code.valueType = frontTypes ∧
      operands.map Code.valueType = input ∧ Forall wf_val operands ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨front,operands,values,frontTypesEq,operandTypes⟩ := List.map_eq_append_iff.mp stack
  obtain ⟨D,actualFront,actualOperands,ins,outs,_,_,operation,split,actualTypes,_,heights⟩ :=
    Abs.frame_typed_operands_bounds typed
  obtain ⟨rfl,rfl⟩ := meaning.principal operation
  have actualLength := resultsTyped_length actualTypes
  have operandLength := congrArg List.length operandTypes
  have frontLength := congrArg List.length (values.symm.trans split)
  simp only [List.length_append,List.length_map] at operandLength frontLength
  have equal : actualFront.length = front.length := by omega
  have valid := (Abs.frameTyped_wf typed).2.2.1
  change Forall wf_val f.vals at valid
  refine ⟨front,operands,values,frontTypesEq,operandTypes,?_,?_⟩
  · intro value member
    apply valid value
    rw [values]
    exact List.mem_append_right _ member
  · simpa only [equal] using heights

theorem framePoint_head
    {s : store} {raw : runtime.interp.Frame} {f : Abs.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {C : context} {targets : List Code.LabelTarget}
    {next : Nat} {output : List valtype} (source : instr) (after : List instr)
    (allowed : Abs.SimdInstr source)
    (project : ∀ before emitted result, emission compiled C before source emitted result →
      Code.SimdEmission compiled.simd.val compiled.v128_pool.val C before source emitted result)
    (point : FramePoint s raw {f with code := source :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint s {raw with pc := target} {f with code := source :: after} compiled C targets next output) ∨
    (∃ instruction result,
      Code.SimdEmission compiled.simd.val compiled.v128_pool.val C (f.vals.map Code.valueType) source [instruction] result ∧
      compiled.code.val[raw.pc.val]? = some instruction ∧
      Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
        compiled.code.val compiled.jump_tables.val targets result after (raw.pc.val+1) next output) := by
  rcases simd_point_head source after allowed project point.code with jump | head
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · exact Or.inr head

end Itasca.Runtime.Interp.StructuredMachine.Simd
