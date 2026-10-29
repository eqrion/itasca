import Itasca.Runtime.Interp.Simd.Execution.ConstValues
import Itasca.Runtime.Interp.Simd.Execution.FrameRetention
import Itasca.Runtime.Interp.Simd.Relations.Mutation
import Itasca.Runtime.Interp.Machine.Simd.ExecutionJoin
import Itasca.Runtime.Interp.Machine.Simd.Continue

/-!
SIMD constant execution at a structured frame point.

Main declarations: `step_constant_frame`. A direct consumer is `Interp.Machine.Simd.FrameStep`.
-/

namespace Itasca.Runtime.Interp.Machine.Simd
open Aeneas Aeneas.Std Itasca.ResultFacts

private theorem constant_bounds (compiled : runtime.bytecode.CompiledFunction) (dst entry : U32)
    (valid : runtime.bytecode.CompiledFunction.instruction_valid compiled (.ConstV128 dst entry)=.ok true) :
    dst.val+2≤compiled.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
    runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at valid
  obtain ⟨fits,run,valid⟩ := bind_ok_inv _ _ _ valid
  cases fits with
  | false => simp at valid
  | true => exact Compiler.slots_fit_true compiled dst 2#u32 run

theorem step_constant_frame {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Compiler.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (bits : U128) (dst entry : U32)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (typed : SourceMachine.CoreTyped ⟨Store.decodeStore view interpretation store,ambient,
      {f with code:=.VCONST .V128 (.mk_uN bits.val)::after}::rest,[]⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view interpretation store) raw
      {f with code:=.VCONST .V128 (.mk_uN bits.val)::after} compiled C targets next output)
    (immediate : compiled.v128_pool.val[entry.val]?=some bits)
    (position : dst.val=Compiler.slots C.LOCALS+Compiler.slots (f.vals.map Compiler.valueType))
    (fetch : compiled.code.val[raw.pc.val]?=some (.ConstV128 dst entry))
    (tail : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (f.vals.map Compiler.valueType++[.V128]) after (raw.pc.val+1) next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ SimdStoreMutation view store out.2.2.1 ∧
      FrameStoreMetadata store out.2.2.1 ∧ ∃ pc : U32, ∃ updated : SourceMachine.AFrame,
      pc.val=raw.pc.val+1 ∧
      {out.2.1 with slots:=exec.slots}={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
      SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ∧
      FrameSlots out.2.1 {raw with pc:=pc} updated ∧
      FrameMetadata {f with code:=.VCONST .V128 (.mk_uN bits.val)::after} updated ∧
      FramePoint (Store.decodeStore view interpretation out.2.2.1) {raw with pc:=pc}
        updated compiled C targets next output ∧
      SourceMachine.Simd.Step ⟨Store.decodeStore view interpretation store,ambient,{f with code:=.VCONST .V128 (.mk_uN bits.val)::after}::rest,[]⟩
        (.next ⟨Store.decodeStore view interpretation out.2.2.1,ambient,updated::rest,[]⟩) ⦄ := by
  have bounds := constant_bounds compiled dst entry (Compiler.well_formed_fetched compiled program.checked _ _ fetch)
  have capacity : raw.base.val+dst.val+2≤exec.slots.length := by omega
  have frameTyped : SourceMachine.FrameTyped (Store.decodeStore view interpretation store)
      {f with code:=.VCONST .V128 (.mk_uN bits.val)::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  have position' : dst.val=Compiler.slots ((f.locals++f.vals).map Compiler.valueType) := by
    simpa only [List.map_append,Compiler.slots_append,point.locals] using position
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled (.ConstV128 dst entry)
    last hf hi hc fetch (program.fetched_bound _ fetch)
  intro pc pcNext
  apply WP.spec_mono (dispatch_const_v128_values memory hooks floats allocator
    {exec with frames:=exec.frames.set index {raw with pc:=pc}} store platform index raw.instance raw.function raw.base
    dst entry inst compiled bits (f.locals++f.vals) hi hc immediate position' slots capacity)
  rintro out ⟨ok,same,platformEq,effect,resultSlots⟩
  rw [same]
  let updated : SourceMachine.AFrame := {f with code:=after,vals:=f.vals++[.VCONST .V128 (.mk_uN bits.val)]}
  refine ⟨ok,platformEq,Or.inl rfl,.refl store,pc,updated,pcNext,effect.2,?_,?_,⟨rfl,rfl,rfl,rfl⟩,?_,.constant⟩
  · rw [effect.1]
    exact .simd_result raw.base.val exec.slots.val (raw.base.val+dst.val) 2#u32 bits (by omega)
  · simpa only [FrameSlots,updated,List.append_assoc] using resultSlots
  · dsimp only [updated]
    refine ⟨point.bindings,point.locals,?_,?_⟩
    · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
      exact labels.replace_suffix (show ∀ label ∈ f.labels, label.height ≤ f.vals.length from SourceMachine.frame_typed_heights (f := {f with code:=.VCONST .V128 (.mk_uN bits.val)::after}) frameTyped)
    · simpa only [List.map_append,List.map_cons,List.map_nil,Compiler.valueType,pcNext] using tail

end Itasca.Runtime.Interp.Machine.Simd
