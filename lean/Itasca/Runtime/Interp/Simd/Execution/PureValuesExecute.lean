import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Simd.Relations.InputValues
import Itasca.Runtime.Compiler.Local.Capacity.SimdCapacity
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.State.StatefulSegmentLookup
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormed
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdConstructor
import Itasca.Runtime.Interp.Simd.Relations.PureResultSlots
import Itasca.Runtime.Interp.Simd.Execution.PureSound

/-!
Sections, each formerly its own module: ConstValues, FrameCapacity, FrameRetention, BytecodeDispatch, PureValuesExecute.
-/

/-! ## ConstValues -/

section

/-!
Typed source values produced by vector-constant dispatch.

Main declarations: `dispatch_const_v128_values`. A direct consumer is `Interp.Machine.Simd.ConstantFrame`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem dispatch_const_v128_values {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index instIndex function base : Usize) (dst pool : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction) (value : U128)
    (front : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (metadata : code.v128_pool.val[pool.val]? = some value)
    (position : dst.val = Compiler.slots (front.map Compiler.valueType))
    (represented : ValuesAt exec.slots.val base.val front)
    (capacity : base.val + dst.val + 2 ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index instIndex function base (.ConstV128 dst pool)
      ⦃ out => out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
        SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+dst.val) 2#u32 value) ∧
        ValuesAt out.2.1.slots.val base.val (front ++ [.VCONST .V128 (.mk_uN value.val)]) ⦄ := by
  simp only [runtime.interp.dispatch]
  step with const_v128_effect memory exec store instIndex function base dst pool inst code value
    found compiled metadata (by omega) as ⟨result,execution,storeNext,ok,unchanged,slots⟩
  have exactSlots : SlotsEffect exec execution (simdResultSlots exec.slots.val (base.val+dst.val) 2#u32 value) := by
    with_unfolding_all exact slots
  refine ⟨ok,unchanged,exactSlots,?_⟩
  rw [exactSlots.1,position]
  exact represented.simd_vector_result value (by simpa only [position] using capacity)
end Itasca.Runtime.Interp

end

/-! ## FrameCapacity -/

section

/-!
Frame-capacity bounds for SIMD operands and results.

Main declarations: `simd_frame_capacity`. A direct consumer is `Interp.Simd.Execution.FrameRetention`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem simd_frame_capacity (slots : Slice U64) (base : Usize) (count a dst wa wb wc wr : U32)
    (frame : base.val + count.val ≤ slots.length)
    (input : a.val + wa.val + wb.val + wc.val ≤ count.val)
    (output : dst.val + wr.val ≤ count.val) :
    base.val + a.val + wa.val + wb.val ≤ Usize.max ∧
    (wc = 2#u32 → base.val + a.val + wa.val + wb.val < Usize.max) ∧
    base.val + dst.val + wr.val ≤ slots.length := by
  refine ⟨?_,?_,?_⟩
  · scalar_tac
  · intro two; scalar_tac
  · omega
end Itasca.Runtime.Interp

end

/-! ## FrameRetention -/

section

/-!
Slot-prefix retention and issued-memory/capacity facts for SIMD frames.

Main declarations: `SlotPrefix.simd_result` and `FrameProgram.simd_capacity`. A direct consumer is `Interp.Machine.Simd.ConstantFrame`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem SlotPrefix.simd_result (base : Nat) (words : List U64) (position : Nat)
    (width : U32) (value : U128) (above : base ≤ position) :
    SlotPrefix base words (simdResultSlots words position width value) := by
  unfold simdResultSlots
  split <;> split
  all_goals first
    | exact .refl _ _
    | exact .set _ _ _ _ above
    | exact .set _ _ _ _ (by omega)
    | exact (SlotPrefix.set _ _ _ _ above).trans (.set _ _ _ _ (by omega))

theorem module_memories_issued {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (C : context)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) (Store.decodeInstance store inst) C) :
    ∀ address, inst.memories.val[0]? = some address →
      ∃ object, store.memories.val[address.index.val]? = some object := by
  intro address mapped
  have bound := (List.getElem?_eq_some_iff.mp mapped).1
  have sourceBound : 0 < (Store.decodeInstance store inst).MEMS.length := by
    simpa only [Store.decodeInstance,List.length_map] using bound
  have contextBound : 0 < C.MEMS.length := by rw [←bindings.mems.length_eq]; exact sourceBound
  obtain ⟨other,object,otherMapped,found⟩ := Stateful.memory_binding_raw view code store inst C C.MEMS[0]
    bindings (List.getElem?_eq_getElem contextBound)
  have same : other = address := Option.some.inj (otherMapped.symm.trans mapped)
  exact ⟨object,same ▸ found⟩

theorem FrameProgram.simd_capacity {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions} (program : FrameProgram store raw compiled locals results functions)
    (slots : Slice U64) (allocated : raw.base.val + compiled.slot_count.val ≤ slots.length)
    (instruction : runtime.bytecode.Instr) (opcode operand entry wa wb wc wr : U32)
    (fetch : compiled.code.val[raw.pc.val]? = some instruction)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (opcode,operand,operand,entry)))
    (shape : runtime.bytecode.simd_shape opcode = .ok (some (wa,wb,wc,wr))) :
    raw.base.val + operand.val + wa.val + wb.val ≤ Usize.max ∧
    (wc = 2#u32 → raw.base.val + operand.val + wa.val + wb.val < Usize.max) ∧
    raw.base.val + operand.val + wr.val ≤ slots.length := by
  obtain ⟨input,output,_⟩ := Compiler.simd_valid_bounds compiled instruction opcode operand operand entry wa wb wc wr
    view shape (Compiler.well_formed_fetched compiled program.checked raw.pc.val instruction fetch)
  exact simd_frame_capacity slots raw.base compiled.slot_count operand operand wa wb wc wr allocated input output

end Itasca.Runtime.Interp

end

/-! ## BytecodeDispatch -/

section

/-!
Lifting SIMD operation views into interpreter dispatch and steps.

Main declarations: `dispatch_simd_of_view` and `step_simd_of_view`. A direct consumer is `Interp.Machine.Simd.LaneFrame`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem dispatch_simd_of_view {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (instruction : runtime.bytecode.Instr) (op dst a entry : U32)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (op,dst,a,entry))) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base instruction = (do
      let (result,next,storeNext) ← runtime.interp.execute_simd memory floats exec store inst function base op dst a entry
      Result.ok (result,next,storeNext,platform)) := by
  cases instruction
  all_goals simp only [runtime.bytecode.Instr.simd,Result.ok.injEq,Option.some.injEq,reduceCtorEq,Prod.mk.injEq] at view
  all_goals first | contradiction | obtain ⟨rfl,rfl,rfl,rfl⟩ := view
  all_goals simp only [runtime.interp.dispatch,runtime.interp.dispatch_simd,runtime.interp.simd_operands,bind_ok,uncurry_apply_pair]

theorem step_simd_of_view {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (frame : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (code : runtime.bytecode.CompiledFunction) (instruction : runtime.bytecode.Instr)
    (op dst a entry : U32)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some frame)
    (hi : store.instances.val[frame.instance.val]? = some inst)
    (hc : inst.module.functions.val[frame.function.val]? = some code)
    (hop : code.code.val[frame.pc.val]? = some instruction)
    (pcBound : frame.pc.val < U32.max)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (op,dst,a,entry)))
    (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P → Prop)
    (handler : ∀ next : U32, next.val = frame.pc.val + 1 →
      runtime.interp.execute_simd memory floats
        {exec with frames := exec.frames.set index {frame with pc := next}}
        store frame.instance frame.function frame.base op dst a entry
        ⦃ out => post (out.1,out.2.1,out.2.2,platform) ⦄) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ post ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index frame inst code instruction
    last hf hi hc hop pcBound post
  intro next nextValue
  rw [dispatch_simd_of_view memory hooks floats allocator _ store platform index frame.instance frame.function frame.base
    instruction op dst a entry view]
  obtain ⟨⟨result,execution,storeNext⟩,returned,property⟩ := WP.spec_imp_exists (handler next nextValue)
  simpa only [returned,bind_ok,uncurry_apply_pair,WP.spec_ok] using property
end Itasca.Runtime.Interp

end

/-! ## PureValuesExecute -/

section

/-!
Bounded pure SIMD execution with typed result values.

Main declarations: `execute_simd_pure_values_mutation_bounded`. A direct consumer is `Interp.Machine.Simd.PureFrame`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Itasca.Wasm2.Simd

private theorem signature_inputs_numeric (signature : Signature) (ty : valtype)
    (member : ty ∈ signature.inputs) : ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF := by
  cases ty <;> cases signature <;> simp_all [Signature.inputs]

theorem execute_simd_pure_values_mutation_bounded {M F : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (interpretation : Store.CodeInterpretation) (view : M → Slice U8)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instIndex function base : Usize) (opcode operand entry : U32)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (imm : runtime.bytecode.SimdImmediate) (op : Operation) (front values : List val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : inst.module.functions.val[function.val]? = some code)
    (immediate : code.simd.val[entry.val]? = some imm)
    (meaning : pureMeaning opcode.val = some op)
    (memories : ∀ ma, inst.memories.val[0]? = some ma →
      ∃ object, store.memories.val[ma.index.val]? = some object)
    (position : operand.val = Compiler.slots (front.map Compiler.valueType))
    (represented : ValuesAt exec.slots.val base.val (front ++ values))
    (wellFormed : Forall wf_val values)
    (typed : values.map Compiler.valueType = op.signature.inputs)
    (space : base.val + operand.val + (Compiler.simdSourceWidth op.signature.inputs[0]?).val +
      (Compiler.simdSourceWidth op.signature.inputs[1]?).val ≤ Usize.max)
    (lastSpace : Compiler.simdSourceWidth op.signature.inputs[2]? = 2#u32 →
      base.val + operand.val + (Compiler.simdSourceWidth op.signature.inputs[0]?).val +
      (Compiler.simdSourceWidth op.signature.inputs[1]?).val < Usize.max)
    (capacity : base.val + operand.val + (Compiler.simdSourceWidth op.signature.outputs[0]?).val ≤ exec.slots.length) :
    runtime.interp.execute_simd memory floats exec store instIndex function base opcode operand operand entry
      ⦃ out => SimdStoreMutation view store out.2.2 ∧ ∃ value,
        Step_pure (values.map admininstr_val ++ [admininstr_instr op.instruction])
          [admininstr_val (Simd.pureResult op.signature value.bv)] ∧
        out.1 = .Ok () ∧ Store.decodeStore view interpretation out.2.2 = Store.decodeStore view interpretation store ∧
        FrameStoreMetadata store out.2.2 ∧
        SlotsEffect exec out.2.1 (simdResultSlots exec.slots.val (base.val+operand.val)
          (Compiler.simdSourceWidth op.signature.outputs[0]?) value) ∧
        ValuesAt out.2.1.slots.val base.val (front ++ [Simd.pureResult op.signature value.bv]) ⦄ := by
  have numeric : ∀ value ∈ values, Compiler.valueType value ≠ .FUNCREF ∧ Compiler.valueType value ≠ .EXTERNREF := by
    intro value member
    have m : Compiler.valueType value ∈ op.signature.inputs := by rw [←typed]; exact List.mem_map_of_mem member
    exact signature_inputs_numeric op.signature _ m
  have arity : values.length ≤ 3 := by
    have length := congrArg List.length typed
    simp only [List.length_map] at length
    have bound : op.signature.inputs.length ≤ 3 := by cases op.signature <;> decide
    omega
  have inputs := represented.operands.simd_operands wellFormed numeric arity
  dsimp only at inputs
  rw [typed,←position] at inputs
  have shape := (Compiler.SimdImmediateMeaning.pure (C := default) opcode imm op meaning).shape
  apply WP.spec_mono (execute_simd_source_mutation_bounded memory floats interpretation view memoryLaws exec store instIndex function base
    opcode operand operand entry inst code imm
    (Compiler.simdSourceWidth op.signature.inputs[0]?) (Compiler.simdSourceWidth op.signature.inputs[1]?)
    (Compiler.simdSourceWidth op.signature.inputs[2]?) (Compiler.simdSourceWidth op.signature.outputs[0]?)
    (fun value => Step_pure (values.map admininstr_val ++ [admininstr_instr op.instruction])
      [admininstr_val (Simd.pureResult op.signature value.bv)])
    found compiled immediate shape memories space lastSpace capacity ?_)
  · rintro out ⟨mutation,value,source,ok,decoded,metadata,slots⟩
    refine ⟨mutation,value,source,ok,decoded,metadata,slots,?_⟩
    rw [slots.1,position]
    exact represented.locals.simd_pure_result op.signature value _ source (by simpa only [position] using capacity)
  · intro bytes
    apply WP.spec_mono (Simd.pure_dispatch_source floats floatLaws opcode op meaning imm.offset imm.lane imm.bits
      (simdInput exec.slots.val (base.val+operand.val) (Compiler.simdSourceWidth op.signature.inputs[0]?))
      (simdInput exec.slots.val (base.val+operand.val+(Compiler.simdSourceWidth op.signature.inputs[0]?).val)
        (Compiler.simdSourceWidth op.signature.inputs[1]?))
      (simdInput exec.slots.val (base.val+operand.val+(Compiler.simdSourceWidth op.signature.inputs[0]?).val+
        (Compiler.simdSourceWidth op.signature.inputs[1]?).val) (Compiler.simdSourceWidth op.signature.inputs[2]?)) bytes)
    rintro result ⟨value,eq,source⟩
    refine ⟨value,eq,?_⟩
    unfold Simd.PureSourceEffect at source
    rw [inputs] at source
    exact source

end Itasca.Runtime.Interp

end
