import Exec.Abs.Simd.ChosenStep
import Exec.Interp.Simd.Common.SimdMachineHelpers
import Exec.Interp.Simd.Common.SimdPureChosenValues
import Exec.Abs.Simd.ChosenSimulation
import Exec.Interp.Simd.Common.SimdBytecodeDispatch
import Exec.Interp.StructuredMachine.SimdPrepare
import Exec.Interp.StructuredMachine.SimdExecutionJoin
import Exec.Code.Local.Lowering.Simd.SimdPureSignature
import Exec.Code.Local.Capacity.SimdMeaningBound

namespace Exec.Interp.StructuredMachine.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem step_pure_chosen_frame {emission : FunctionEmission} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (frontTypes : List valtype) (op : Operation)
    (opcode operand entry : U32) (imm : runtime.bytecode.SimdImmediate) (instruction : Code.Bytecode)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=op.instruction::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission (Store.decodeStore view interpretation store) raw
      {f with code:=op.instruction::after} compiled C targets next output)
    (stack : f.vals.map Code.valueType=frontTypes++op.signature.inputs)
    (meaning : pureMeaning opcode.val=some op)
    (immediate : compiled.simd.val[entry.val]?=some imm)
    (made : runtime.bytecode.Instr.make_simd opcode operand operand entry=.ok (some instruction))
    (position : operand.val=Code.slots C.LOCALS+Code.slots frontTypes)
    (fetch : compiled.code.val[raw.pc.val]?=some instruction)
    (tail : Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (frontTypes++op.signature.outputs) after (raw.pc.val+1) next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧
      FrameStoreMetadata store out.2.2.1 ∧ ∃ pc : U32, ∃ updated : Abs.AFrame,
      pc.val=raw.pc.val+1 ∧
      {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
      SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
      FrameSlots out.2.1 {raw with pc:=pc} updated ∧
      FrameMetadata {f with code:=op.instruction::after} updated ∧
      FramePoint emission (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc}
        updated compiled C targets next output ∧
      Abs.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=op.instruction::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ∧
      Spec.ChoiceStep choices occurrence
        (Abs.decode ⟨Store.decodeStore view interpretation store,ambient,{f with code:=op.instruction::after}::rest,[]⟩) []
        (Abs.decode ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ∧
      Abs.Simd.ChosenStep choices occurrence ⟨Store.decodeStore view interpretation store,ambient,{f with code:=op.instruction::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ⦄ := by
  have sig := Code.pure_source_signature meaning
  have immediateMeaning := Code.SimdImmediateMeaning.pure (C:=C) opcode imm op meaning
  have frameTyped : Abs.FrameTyped (Store.decodeStore view interpretation store) {f with code:=op.instruction::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨front,values,split,frontEq,types,wf,heights⟩ := instruction_operands immediateMeaning frameTyped stack
  have simdView := Code.make_simd_roundtrip_bounded opcode operand operand entry instruction
    (Itasca.Wasm2.Simd.pure_bound meaning) made
  obtain ⟨space,lastSpace,capacity⟩ := program.simd_capacity exec.slots.slice allocated instruction opcode operand entry
    _ _ _ _ fetch simdView immediateMeaning.shape
  have memories := module_memories_issued view interpretation store inst C (moduleEq ▸ point.bindings)
  have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++values) := by
    simpa only [FrameSlots,split,List.append_assoc] using slots
  have position' : operand.val=Code.slots ((f.locals++front).map Code.valueType) := by
    simpa only [List.map_append,Code.slots_append,point.locals,frontEq] using position
  apply step_simd_of_view memory hooks floats allocator exec store platform index raw inst compiled instruction
    opcode operand operand entry last hf hi hc fetch (program.fetched_bound _ fetch) simdView
  intro pc pcNext
  apply WP.spec_mono (execute_simd_pure_chosen_values_mutation_bounded memory floats interpretation view memoryLaws floatLaws admissible vector occurrence
    {exec with frames:=exec.frames.set index {raw with pc:=pc}} store raw.instance raw.function raw.base
    opcode operand entry inst compiled imm op (f.locals++front) values hi hc immediate meaning memories
    position' represented wf types space lastSpace capacity)
  rintro out ⟨mutation,value,source,ok,decoded,metadata,effect,resultSlots⟩
  let updated : Abs.AFrame := {f with code:=after,vals:=front++[Interp.Simd.pureResult op.signature value.bv]}
  have resultType : Abs.valueType (Interp.Simd.pureResult op.signature value.bv)=Code.simdPureOutput op.signature := by
    cases op.signature <;> rfl
  have step : Abs.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=op.instruction::after}::rest,[]⟩
      (.next ⟨Store.decodeStore view interpretation out.2.2,ambient,updated::rest,[]⟩) := by
    rw [decoded]
    apply Abs.Simd.Step.pure sig
    exact .next front values _ split
      (by simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using types) ⟨source.erases admissible,resultType⟩
  refine ⟨ok,rfl,mutation,metadata,pc,updated,pcNext,effect.2,?_,?_,?_,?_,step,?_,?_⟩
  · rw [effect.1]
    exact .simd_result raw.base.val exec.slots.val (raw.base.val+operand.val) _ value (by omega)
  · simpa only [FrameSlots,updated,List.append_assoc] using resultSlots
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · apply framePoint_continue point (step.next_extension typed) front values [_] after split heights _ pc pcNext
    have outputEq : [Code.valueType (Interp.Simd.pureResult op.signature value.bv)]=op.signature.outputs := by
      cases op.signature <;> rfl
    simpa only [List.map_cons,List.map_nil,outputEq,frontEq] using tail

  · rw [decoded]
    apply sig.chosen_simulation admissible typed.typed split
    · simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using types
    · exact source
  · rw [decoded]
    exact Abs.Simd.ChosenStep.pure sig split
      (by simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using types)
      ⟨source.erases admissible,resultType⟩ source

end Exec.Interp.StructuredMachine.Simd
