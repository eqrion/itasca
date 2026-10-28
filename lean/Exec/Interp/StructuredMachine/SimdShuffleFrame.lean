import Exec.Interp.Simd.Common.SimdMachineHelpers
import Exec.Interp.Simd.Common.SimdShuffleValuesExecute
import Exec.Interp.Simd.Common.SimdBytecodeDispatch
import Exec.Interp.StructuredMachine.SimdPrepare
import Exec.Interp.StructuredMachine.SimdExecutionJoin
import Exec.Code.Local.Lowering.Simd.SimdSourceSignature
import Exec.Interp.Simd.Common.SimdValuesTransition
import Exec.Code.Local.Capacity.SimdMeaningBound

namespace Itasca.Runtime.Interp.StructuredMachine.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem step_shuffle_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (frontTypes : List valtype) (low high : U64)
    (operand entry : U32) (imm : runtime.bytecode.SimdImmediate) (instruction : Code.Bytecode)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=(shuffle low high)::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=(shuffle low high)::after} compiled C targets next output)
    (stack : f.vals.map Code.valueType=frontTypes++[valtype.V128,valtype.V128])
    (combined : imm.bits.val=low.val+high.val*2^64)
    (immediate : compiled.simd.val[entry.val]?=some imm)
    (made : runtime.bytecode.Instr.make_simd 13#u32 operand operand entry=.ok (some instruction))
    (position : operand.val=Code.slots C.LOCALS+Code.slots frontTypes)
    (fetch : compiled.code.val[raw.pc.val]?=some instruction)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (frontTypes++[valtype.V128]) after (raw.pc.val+1) next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧
      FrameStoreMetadata store out.2.2.1 ∧ ∃ pc : U32, ∃ updated : Abs.AFrame,
      pc.val=raw.pc.val+1 ∧
      {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
      SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
      FrameSlots out.2.1 {raw with pc:=pc} updated ∧
      FrameMetadata {f with code:=(shuffle low high)::after} updated ∧
      FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc}
        updated compiled C targets next output ∧
      Abs.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=(shuffle low high)::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ⦄ := by
  have sig : Abs.Simd.PureSignature (shuffle low high) [.V128,.V128] .V128 := by
    with_unfolding_all exact .shuffle _ _
  have immediateMeaning := Code.SimdImmediateMeaning.shuffle (C:=C) imm low high combined
  have frameTyped : Abs.FrameTyped (Store.decodeStore view interpretation store) {f with code:=(shuffle low high)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨front,values,split,frontEq,types,wf,heights⟩ := instruction_operands immediateMeaning frameTyped stack
  have simdView := Code.make_simd_roundtrip_bounded 13#u32 operand operand entry instruction
    (by decide) made
  obtain ⟨space,lastSpace,capacity⟩ := program.simd_capacity exec.slots.slice allocated instruction 13#u32 operand entry
    _ _ _ _ fetch simdView immediateMeaning.shape
  obtain ⟨D,actualFront,actualValues,ins,outs,_,_,operation,_⟩ := Abs.frame_typed_operands_bounds frameTyped
  have valid : ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32 := by
    cases operation
    cases_type fun_dim
    assumption
  have memories := module_memories_issued view interpretation store inst C (moduleEq ▸ point.bindings)
  have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++values) := by
    simpa only [FrameSlots,split,List.append_assoc] using slots
  have position' : operand.val=Code.slots ((f.locals++front).map Code.valueType) := by
    simpa only [List.map_append,Code.slots_append,point.locals,frontEq] using position
  apply step_simd_of_view memory hooks floats allocator exec store platform index raw inst compiled instruction
    13#u32 operand operand entry last hf hi hc fetch (program.fetched_bound _ fetch) simdView
  intro pc pcNext
  apply WP.spec_mono (execute_simd_shuffle_values memory floats interpretation view memoryLaws
    {exec with frames:=exec.frames.set index {raw with pc:=pc}} store raw.instance raw.function raw.base
    operand entry inst compiled imm low high (f.locals++front) values hi hc immediate combined valid memories
    position' represented wf types (by change raw.base.val+operand.val+2+2≤Usize.max at space; omega) capacity)
  rintro out ⟨mutation,value,source,ok,decoded,metadata,effect,resultSlots⟩
  let updated : Abs.AFrame := {f with code:=after,vals:=front++[Spec.Simd.valueOfBits .V128 value.bv]}
  have resultType : Abs.valueType (Spec.Simd.valueOfBits .V128 value.bv)=valtype.V128 := by
    rfl
  have step : Abs.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=(shuffle low high)::after}::rest,[]⟩
      (.next ⟨Store.decodeStore view interpretation out.2.2,ambient,updated::rest,[]⟩) := by
    rw [decoded]
    apply Abs.Simd.Step.pure sig
    exact .next front values _ split
      (by simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using types) ⟨source,resultType⟩
  refine ⟨ok,rfl,mutation,metadata,pc,updated,pcNext,effect.2,?_,?_,?_,?_,step⟩
  · rw [effect.1]
    exact .simd_result raw.base.val exec.slots.val (raw.base.val+operand.val) _ value (by omega)
  · simpa only [FrameSlots,updated,List.append_assoc] using resultSlots
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · apply framePoint_continue point (step.next_extension typed) front values [_] after split heights _ pc pcNext
    have outputEq : [Code.valueType (Spec.Simd.valueOfBits .V128 value.bv)]=[valtype.V128] := by
      rfl
    simpa only [List.map_cons,List.map_nil,outputEq,frontEq] using tail

end Itasca.Runtime.Interp.StructuredMachine.Simd
