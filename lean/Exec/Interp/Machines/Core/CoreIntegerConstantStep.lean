import Exec.Interp.Machines.Core.CoreIntegerConstantPoint
import Exec.Interp.Machines.Core.CoreIntegerConstantSlots
import Exec.Interp.Machines.Core.CoreJump
import Exec.Abs.Core.Pure
namespace Exec.Interp.IntegerConstant
open Aeneas Aeneas.Std SpecExt

theorem step_integer32_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : U32) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Code.slots ((f.locals++f.vals).map Code.valueType) < exec.slots.length)
    (point : CoreFramePoint sourceStore raw {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        CoreFramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  rcases corePoint_integer32_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
  · have targetPoint : CoreFramePoint sourceStore {raw with pc := target} {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_core_forward_jump memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} rest C targets next output target last frameFound instanceFound codeFound pcBound forward fetched slots targetPoint typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · subst value
    have destination : dst.val = Code.slots ((f.locals++f.vals).map Code.valueType) := by
      simpa only [point.locals,List.map_append,Code.slots_append] using position
    have frameTyped : Abs.FrameTyped sourceStore {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val)) :: after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨nextState,actual,fresh,simulation⟩ := Abs.Core.constant_progress sourceStore ambient f rest after .I32 (.mk_num__0 .I32 (.mk_uN bits.val)) typed
    have nextEq : (⟨sourceStore,ambient,{f with code := after,vals := f.vals ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))]}::rest,[]⟩ : Abs.AState) = nextState := Abs.AResult.next.inj actual
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const32 dst bits) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have nextPoint : CoreFramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := f.vals ++ [.CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
        have heights := Abs.frameTyped_heights frameTyped
        exact labels.replace_suffix heights
      · simpa only [List.map_append,List.map_cons,List.map_nil,Code.valueType,valtype_numtype,pcNext] using tail
    apply WP.spec_mono (dispatch_integer32_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw dst bits f after slots destination
      (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,written,unchanged⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,unchanged,represented,nextPoint,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr rfl,?_,?_⟩
    · exact ConcreteSim.of_source _ _ _ _ _ simulation
    · exact Or.inr ⟨raw.base.val+dst.val,_,Nat.le_add_right _ _,by simpa only [destination] using capacity,written⟩

theorem step_integer64_core {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : U64) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Code.slots ((f.locals++f.vals).map Code.valueType) < exec.slots.length)
    (point : CoreFramePoint sourceStore raw {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        CoreFramePoint sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))]}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  rcases corePoint_integer64_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
  · have targetPoint : CoreFramePoint sourceStore {raw with pc := target} {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_core_forward_jump memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} rest C targets next output target last frameFound instanceFound codeFound pcBound forward fetched slots targetPoint typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · subst value
    have destination : dst.val = Code.slots ((f.locals++f.vals).map Code.valueType) := by
      simpa only [point.locals,List.map_append,Code.slots_append] using position
    have frameTyped : Abs.FrameTyped sourceStore {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val)) :: after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨nextState,actual,fresh,simulation⟩ := Abs.Core.constant_progress sourceStore ambient f rest after .I64 (.mk_num__0 .I64 (.mk_uN bits.val)) typed
    have nextEq : (⟨sourceStore,ambient,{f with code := after,vals := f.vals ++ [.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val))]}::rest,[]⟩ : Abs.AState) = nextState := Abs.AResult.next.inj actual
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const64 dst bits) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have nextPoint : CoreFramePoint sourceStore {raw with pc := pc}
        {f with code := after,vals := f.vals ++ [.CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val))]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
        have heights := Abs.frameTyped_heights frameTyped
        exact labels.replace_suffix heights
      · simpa only [List.map_append,List.map_cons,List.map_nil,Code.valueType,valtype_numtype,pcNext] using tail
    apply WP.spec_mono (dispatch_integer64_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw dst bits f after slots destination
      (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,written,unchanged⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,unchanged,represented,nextPoint,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr rfl,?_,?_⟩
    · exact ConcreteSim.of_source _ _ _ _ _ simulation
    · exact Or.inr ⟨raw.base.val+dst.val,_,Nat.le_add_right _ _,by simpa only [destination] using capacity,written⟩

end Exec.Interp.IntegerConstant
