import Exec.Interp.StructuredMachine.SimdPureFrame
import Exec.Interp.StructuredMachine.SimdLaneFrame
import Exec.Interp.StructuredMachine.SimdShuffleFrame
import Exec.Interp.StructuredMachine.SimdMemoryFrame
import Exec.Interp.StructuredMachine.SimdConstantFrame
import Exec.Interp.StructuredMachine.SimdFrameOutcome

namespace Exec.Interp.StructuredMachine.Simd
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem frame_point_step {emission : FunctionEmission} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (source : instr) (after : List instr)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission (Store.decodeStore view interpretation store) raw
      {f with code:=source::after} compiled C targets next output)
    (allowed : Abs.SimdInstr source)
    (project : ∀ before emitted result, emission compiled C before source emitted result →
      Code.SimdEmission compiled.simd.val compiled.v128_pool.val C before source emitted result) :
    (∃ target : U32, raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      FramePoint emission (Store.decodeStore view interpretation store) {raw with pc:=target}
        {f with code:=source::after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ FrameOutcome emission view interpretation
      store exec platform raw index compiled C targets next output ambient {f with code:=source::after} rest ⦄) := by
  rcases framePoint_head source after allowed project point with jump | ⟨instruction,result,head,fetch,tail⟩
  · exact Or.inl jump
  · apply Or.inr
    generalize stackEq : f.vals.map Code.valueType=stack at head
    cases head with
    | instruction front inputs outputs source opcode operand entry imm instruction meaning immediate made position =>
      cases meaning with
      | pure opcode imm op meaning =>
        apply WP.spec_mono (step_pure_frame memory hooks floats allocator view interpretation memoryLaws floatLaws
          exec store platform raw index inst compiled C targets next output ambient f rest after front op
          opcode operand entry imm instruction last hf hi hc moduleEq program allocated typed slots point stackEq
          meaning immediate made position fetch tail)
        rintro out ⟨ok,platformEq,mutation,metadata,pc,g,pcNext,effect⟩
        exact ⟨platformEq,mutation,metadata,pc,pcNext,Or.inl ⟨ok,g,effect⟩⟩
      | lane opcode imm op meaning lane lanePosition =>
        apply WP.spec_mono (step_lane_frame memory hooks floats allocator view interpretation memoryLaws
          exec store platform raw index inst compiled C targets next output ambient f rest after front op lane
          opcode operand entry imm instruction last hf hi hc moduleEq program allocated typed slots point stackEq
          meaning lanePosition immediate made position fetch tail)
        rintro out ⟨ok,platformEq,mutation,metadata,pc,g,pcNext,effect⟩
        exact ⟨platformEq,mutation,metadata,pc,pcNext,Or.inl ⟨ok,g,effect⟩⟩
      | memory opcode imm op meaning argument lane memoryType available offset lanePosition =>
        exact step_memory_frame memory hooks floats allocator view interpretation memoryLaws
          exec store platform raw index inst compiled C targets next output ambient f rest after front op argument lane
          opcode operand entry imm instruction last hf hi hc moduleEq program allocated typed slots point stackEq
          meaning memoryType available offset lanePosition immediate made position fetch tail
      | shuffle imm low high combined =>
        apply WP.spec_mono (step_shuffle_frame memory hooks floats allocator view interpretation memoryLaws
          exec store platform raw index inst compiled C targets next output ambient f rest after front low high
          operand entry imm instruction last hf hi hc moduleEq program allocated typed slots point stackEq
          combined immediate made position fetch tail)
        rintro out ⟨ok,platformEq,mutation,metadata,pc,g,pcNext,effect⟩
        exact ⟨platformEq,mutation,metadata,pc,pcNext,Or.inl ⟨ok,g,effect⟩⟩
    | constant front bits dst entry immediate position =>
      rw [←stackEq] at position tail
      apply WP.spec_mono (step_constant_frame memory hooks floats allocator view interpretation
        exec store platform raw index inst compiled C targets next output ambient f rest after bits dst entry
        last hf hi hc program allocated typed slots point immediate position fetch tail)
      rintro out ⟨ok,platformEq,mutation,metadata,pc,g,pcNext,effect⟩
      exact ⟨platformEq,mutation,metadata,pc,pcNext,Or.inl ⟨ok,g,effect⟩⟩

end Exec.Interp.StructuredMachine.Simd
