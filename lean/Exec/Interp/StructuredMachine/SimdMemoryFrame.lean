import Exec.Interp.Simd.Common.SimdMachineHelpers
import Exec.Interp.Simd.Memory.SimdMemoryValuesExecute
import Exec.Interp.Simd.Common.SimdMutation
import Exec.Interp.Simd.Common.SimdValuesTransition
import Exec.Code.Local.Lowering.Simd.SimdMemoryValid
import Exec.Interp.Simd.Common.SimdBytecodeDispatch
import Exec.Interp.StructuredMachine.SimdPrepare
import Exec.Interp.StructuredMachine.SimdExecutionJoin
import Exec.Code.Local.Lowering.Simd.SimdSourceSignature
import Exec.Code.Local.Capacity.SimdMeaningBound

namespace Exec.Interp.StructuredMachine.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem step_memory_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (frontTypes : List valtype) (op : MemoryOperation) (argument : memarg) (lane : U8)
    (opcode operand entry : U32) (imm : runtime.bytecode.SimdImmediate) (instruction : Code.Bytecode)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=(op.instruction argument (.mk_uN lane.val))::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=(op.instruction argument (.mk_uN lane.val))::after} compiled C targets next output)
    (stack : f.vals.map Code.valueType=frontTypes++op.inputs)
    (meaning : memoryMeaning opcode.val=some op)
    (memoryType : memtype) (available : C.MEMS[0]?=some memoryType)
    (offset : argument.OFFSET=.mk_uN imm.offset.val)
    (lanePosition : op.laneCount ≠ 0 → imm.lane.val=lane.val)
    (immediate : compiled.simd.val[entry.val]?=some imm)
    (made : runtime.bytecode.Instr.make_simd opcode operand operand entry=.ok (some instruction))
    (position : operand.val=Code.slots C.LOCALS+Code.slots frontTypes)
    (fetch : compiled.code.val[raw.pc.val]?=some instruction)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (frontTypes++op.outputs) after (raw.pc.val+1) next output) :
    let initial : Abs.AState := ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=op.instruction argument (.mk_uN lane.val)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧
      FrameStoreMetadata store out.2.2.1 ∧ ∃ pc : U32, pc.val=raw.pc.val+1 ∧
      ((out.1=.Ok () ∧ ∃ updated : Abs.AFrame,
        {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
        FrameSlots out.2.1 {raw with pc:=pc} updated ∧
        FrameMetadata {f with code:=op.instruction argument (.mk_uN lane.val)::after} updated ∧
        FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc}
          updated compiled C targets next output ∧
        Abs.Simd.Step initial (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .MemoryOutOfBounds) ∧
        out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        Store.decodeStore view interpretation out.2.2.1=Store.decodeStore view interpretation store ∧
        Abs.Simd.Step initial .trap)) ⦄ := by
  dsimp only
  have sig := Code.memory_source_signature op argument (.mk_uN lane.val)
  have immediateMeaning := Code.SimdImmediateMeaning.memory (C:=C) opcode imm op meaning argument lane
    memoryType available offset lanePosition
  have frameTyped : Abs.FrameTyped (Store.decodeStore view interpretation store)
      {f with code:=op.instruction argument (.mk_uN lane.val)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨front,values,split,frontEq,types,wf,heights⟩ := instruction_operands immediateMeaning frameTyped stack
  have simdView := Code.make_simd_roundtrip_bounded opcode operand operand entry instruction
    immediateMeaning.opcode_bound made
  obtain ⟨space,lastSpace,capacity⟩ := program.simd_capacity exec.slots.slice allocated instruction opcode operand entry
    _ _ _ _ fetch simdView immediateMeaning.shape
  obtain ⟨D,actualFront,actualValues,ins,outs,_,_,operation,_⟩ := Abs.frame_typed_operands_bounds frameTyped
  have laneValid : op.laneCount ≠ 0 → imm.lane.val < op.laneCount := by
    intro nonzero
    rw [lanePosition nonzero]
    exact Code.simd_memory_lane_valid op (Abs.labelContext D f.labels) argument (.mk_uN lane.val) ins outs operation nonzero
  have sourceEq : op.instruction argument (.mk_uN imm.lane.val)=op.instruction argument (.mk_uN lane.val) := by
    by_cases nonzero : op.laneCount ≠ 0
    · rw [lanePosition nonzero]
    · cases op <;> first | rfl | simp [MemoryOperation.laneCount] at nonzero
  obtain ⟨ma,object,mapped,issued⟩ := Stateful.memory_binding_raw view interpretation store inst C memoryType
    (moduleEq ▸ point.bindings) available
  have represented : ValuesAt exec.slots.val raw.base.val ((f.locals++front)++values) := by
    simpa only [FrameSlots,split,List.append_assoc] using slots
  have position' : operand.val=Code.slots ((f.locals++front).map Code.valueType) := by
    simpa only [List.map_append,Code.slots_append,point.locals,frontEq] using position
  have frameWf := (Abs.frameTyped_wf frameTyped).1
  have operationWf : wf_admininstr (admininstr_instr (op.instruction argument (.mk_uN imm.lane.val))) := by
    rw [sourceEq]
    exact Spec.wf_admininstr_instr ((Abs.frameTyped_wf frameTyped).2.2.2 _ (by simp))
  apply step_simd_of_view memory hooks floats allocator exec store platform index raw inst compiled instruction
    opcode operand operand entry last hf hi hc fetch (program.fetched_bound _ fetch) simdView
  intro pc pcNext
  apply WP.spec_mono (execute_simd_memory_values memory floats interpretation view memoryLaws
    {exec with frames:=exec.frames.set index {raw with pc:=pc}} store raw.instance raw.function raw.base
    opcode operand entry inst compiled imm op (f.locals++front) values hi hc immediate meaning ma object mapped issued
    position' represented wf types space lastSpace capacity f.toFrame argument moduleEq typed.typed.store frameWf
    operationWf (by rw [offset]; rfl) laneValid)
  rintro out ⟨mutation,effect⟩
  refine ⟨rfl,Or.inr ⟨ma,object,issued,mutation⟩,mutation.frame_metadata,pc,pcNext,?_⟩
  cases status : out.1 with
  | Ok unit =>
    cases unit
    rw [status] at effect
    obtain ⟨value,slotsEffect,resultSlots,source,change⟩ := effect
    rw [sourceEq] at source
    let results := Spec.Simd.operandValues op.outputs value.bv 0 0
    let updated : Abs.AFrame := {f with code:=after,vals:=front++results}
    have step : Abs.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,
        {f with code:=op.instruction argument (.mk_uN lane.val)::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2,ambient,updated::rest,[]⟩) := by
      apply Abs.Simd.Step.memory sig
      exact Interp.Simd.memory_values_transition _ _ _ after op argument lane.val front values value _ split types change source
    refine Or.inl ⟨rfl,updated,slotsEffect.2,?_,?_,⟨rfl,rfl,rfl,rfl⟩,?_,step⟩
    · rw [slotsEffect.1]
      exact .simd_result raw.base.val exec.slots.val (raw.base.val+operand.val) _ value (by omega)
    · simpa only [FrameSlots,updated,List.append_assoc] using resultSlots
    · apply framePoint_continue point (step.next_extension typed) front values results after split heights _ pc pcNext
      have resultTypes : results.map Code.valueType=op.outputs := by
        simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using Interp.Simd.memory_result_types op value.bv
      simpa only [resultTypes,frontEq] using tail
  | Err error =>
    rw [status] at effect
    obtain ⟨rfl,same,decoded,source⟩ := effect
    rw [sourceEq] at source
    refine Or.inr ⟨rfl,same,decoded,?_⟩
    apply Abs.Simd.Step.memory sig
    exact Interp.Simd.memory_values_trap _ _ _ after op argument lane.val front values split types source

end Exec.Interp.StructuredMachine.Simd
