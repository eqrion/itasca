import Itasca.Runtime.Interp.Machine.Simd.Point
import Itasca.Runtime.Interp.Machine.Simd.Continue
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdSignature
import Itasca.Runtime.SourceMachine.Simd.Transition

/-!
Source operands and head preparation for a SIMD frame instruction.

Main declarations: `instruction_operands` and `frame_point_head`. A direct consumer is `Interp.Machine.Simd.LaneFrame`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas.Std SpecExt Itasca.Runtime.Spec

theorem instruction_operands {s : store} {f : SourceMachine.AFrame} {after : List instr}
    {C opcode immediate input source output frontTypes}
    (meaning : Compiler.SimdImmediateMeaning C opcode immediate input source output)
    (typed : SourceMachine.FrameTyped s {f with code := source :: after} [])
    (stack : f.vals.map Compiler.valueType = frontTypes ++ input) :
    ∃ front operands, f.vals = front ++ operands ∧ front.map Compiler.valueType = frontTypes ∧
      operands.map Compiler.valueType = input ∧ Forall wf_val operands ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨front,operands,values,frontTypesEq,operandTypes⟩ := List.map_eq_append_iff.mp stack
  obtain ⟨D,actualFront,actualOperands,ins,outs,_,_,operation,split,actualTypes,_,heights⟩ :=
    SourceMachine.frame_typed_operands_bounds typed
  obtain ⟨rfl,rfl⟩ := meaning.principal operation
  have actualLength := results_typed_length actualTypes
  have operandLength := congrArg List.length operandTypes
  have frontLength := congrArg List.length (values.symm.trans split)
  simp only [List.length_append,List.length_map] at operandLength frontLength
  have equal : actualFront.length = front.length := by omega
  have valid := (SourceMachine.frame_typed_wf typed).2.2.1
  change Forall wf_val f.vals at valid
  refine ⟨front,operands,values,frontTypesEq,operandTypes,?_,?_⟩
  · intro value member
    apply valid value
    rw [values]
    exact List.mem_append_right _ member
  · simpa only [equal] using heights

theorem frame_point_head
    {s : store} {raw : runtime.interp.Frame} {f : SourceMachine.AFrame}
    {compiled : runtime.bytecode.CompiledFunction} {C : context} {targets : List Compiler.LabelTarget}
    {next : Nat} {output : List valtype} (source : instr) (after : List instr)
    (allowed : SourceMachine.SimdInstr source)
    (project : ∀ before emitted result, emission compiled C before source emitted result →
      Compiler.SimdEmission compiled.simd.val compiled.v128_pool.val C before source emitted result)
    (point : FramePoint s raw {f with code := source :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint s {raw with pc := target} {f with code := source :: after} compiled C targets next output) ∨
    (∃ instruction result,
      Compiler.SimdEmission compiled.simd.val compiled.v128_pool.val C (f.vals.map Compiler.valueType) source [instruction] result ∧
      compiled.code.val[raw.pc.val]? = some instruction ∧
      Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
        compiled.code.val compiled.jump_tables.val targets result after (raw.pc.val+1) next output) := by
  rcases simd_point_head source after allowed project point.code with jump | head
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · exact Or.inr head

end Itasca.Runtime.Interp.Machine.Simd
