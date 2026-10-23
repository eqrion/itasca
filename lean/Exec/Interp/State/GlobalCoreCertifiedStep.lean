import Exec.Interp.State.GlobalCoreStep
import Exec.Interp.State.GlobalCoreContinue
import Exec.Interp.Relations.Capacity
import Exec.Code.Local.Capacity.GlobalCapacity
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem coreFramePoint_globalGet_step (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (binding : FrameBinding store exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true)
    (pcBound : raw.pc.val < U32.max)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : CoreFramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      CoreFramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ nextFrame pc, pc.val = raw.pc.val+1 ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧
        Abs.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        CoreFramePoint (Store.decodeStore view code store) {raw with pc := pc} nextFrame compiled C targets next output ∧ (∃ values, nextFrame = {f with code := after,vals := values}) ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄) := by
  dsimp only
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_GET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases coreFramePoint_globalGet_prepare view code store inst raw f compiled C targets next output after index moduleEq point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨idx,dst,address,object,indexEq,mapped,issued,position,fetch,tail⟩ := operation
    subst index
    have valid := Code.well_formed_fetched compiled checked raw.pc.val _ fetch
    have bound := Code.global_get_valid_bounds compiled (sourceType object.ty.valtype) dst idx valid
    have allocated := binding.capacity inst compiled found codeFound
    have capacity : raw.base.val + dst.val + Code.width (sourceType object.ty.valtype) ≤ exec.slots.length := by omega
    apply WP.spec_mono (step_global_get_simulation memory hooks floats allocator view code exec store raw dst idx inst address object ambient f rest after platform frameIndex found mapped issued moduleEq slots position capacity
      (small object (List.mem_of_getElem? issued)) compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨success,platformSame,storeSame,nextFrame,actual,fresh,source,represented,pc,pcNext,unchanged,prefixEffect⟩ := effect
    have exactStep := core_global_get_value view code store inst address object ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN idx.val) :: after} :: rest,[]⟩ f rest after idx rfl moduleEq mapped issued
    rw [exactStep] at actual
    have frameEq := (List.cons.inj (congrArg Abs.AState.frames (Abs.AResult.next.inj actual))).1
    refine ⟨success,storeSame,platformSame,nextFrame,pc,pcNext,unchanged,fresh,source,represented,?_,?_,prefixEffect⟩
    · rw [←frameEq]
      exact corePoint_globalGet_continue point _ _ after (Abs.frameTyped_heights frameTyped)
        (decode_words_valueType _ _ _) tail pc pcNext
    · exact ⟨_,frameEq.symm⟩

theorem coreFramePoint_globalSet_step (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : CoreFramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      CoreFramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ nextFrame pc, pc.val = raw.pc.val+1 ∧
        out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧
        Abs.CoreTyped {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Extend_store initial.store (Store.decodeStore view code out.2.2.1) ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        CoreFramePoint (Store.decodeStore view code out.2.2.1) {raw with pc := pc} nextFrame compiled C targets next output ∧ ∃ values, nextFrame = {f with code := after,vals := values} ⦄) := by
  dsimp only
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases coreFramePoint_globalSet_prepare view code store inst raw f compiled C targets next output after index moduleEq frameTyped point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,valueType,position,fetch,tail⟩ := operation
    subst index
    apply WP.spec_mono (step_global_set_simulation memory hooks floats allocator view code exec store raw src idx inst address object ambient f rest after front value platform frameIndex found mapped issued moduleEq slots values position mutable valueWf valueType compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨platformSame,success,⟨pc,pcNext,unchanged⟩,metadata,nextFrame,actual,fresh,extension,source,represented⟩ := effect
    have typeEq : Abs.valueType value = sourceType object.ty.valtype := by rw [←valueType_eq_abs]; exact valueType.symm
    have exactStep := core_global_set_value view code store inst address object ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN idx.val) :: after} :: rest,[]⟩ f rest after idx front value rfl moduleEq mapped issued values mutable typeEq
    rw [exactStep] at actual
    have frameEq := (List.cons.inj (congrArg Abs.AState.frames (Abs.AResult.next.inj actual))).1
    refine ⟨success,platformSame,metadata,nextFrame,pc,pcNext,unchanged,fresh,extension,source,represented,?_,?_⟩
    · rw [←frameEq]
      exact corePoint_globalSet_continue point extension front value after values heights tail pc pcNext
    · exact ⟨_,frameEq.symm⟩

end Exec.Interp
