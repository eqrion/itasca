import Exec.Abs.Core.ChosenConstant
import Exec.Interp.Relations.ChosenControlSource
import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Machines.Core.CoreFloatConstantStep
import Exec.Interp.StructuredMachine.FloatConstantPoint
import Exec.Interp.Machines.Core.CoreFloatConstantSlots
import Exec.Interp.StructuredMachine.ForwardJump
import Exec.Abs.Core.Pure
namespace Exec.Interp.StructuredMachine.FloatConstant
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
open Exec.Interp.FloatConstant
open Aeneas Aeneas.Std SpecExt

theorem step_float32_core_forward_chosen {choices : Spec.SourceChoices} (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Code.slots ((f.locals++f.vals).map Code.valueType) < exec.slots.length)
    (point : FramePoint emission sourceStore raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 value)]}) ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  rcases corePoint_float32_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
  · have targetPoint : FramePoint emission sourceStore {raw with pc := target} {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} rest C targets next output target last frameFound instanceFound codeFound pcBound forward fetched slots targetPoint typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,forward,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward tail.current.entry_bound⟩,?_⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · subst value
    have destination : dst.val = Code.slots ((f.locals++f.vals).map Code.valueType) := by
      simpa only [point.locals,List.map_append,Code.slots_append] using position
    have frameTyped : Abs.FrameTyped sourceStore {f with code := .CONST .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val)) :: after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨nextState,actual,fresh,simulation⟩ := Abs.Core.constant_chosen_progress occurrence sourceStore ambient f rest after .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val)) typed
    have nextEq : (⟨sourceStore,ambient,{f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val))]}::rest,[]⟩ : Abs.AState) = nextState := Abs.AResult.next.inj actual
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const32 dst bits) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have nextPoint : FramePoint emission sourceStore {raw with pc := pc}
        {f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 (Builtins.floatOfBits 32 bits.val))]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
        have heights := Abs.frameTyped_heights frameTyped
        exact labels.replace_suffix heights
      · simpa only [List.map_append,List.map_cons,List.map_nil,Code.valueType,valtype_numtype,pcNext] using tail
    apply WP.spec_mono (dispatch_float32_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw dst bits f after slots destination
      (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,written,unchanged⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,by omega,unchanged,represented,nextPoint,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr rfl,?_,?_⟩
    · exact ChosenConcreteSim.of_source _ _ _ _ _ simulation
    · exact Or.inr ⟨raw.base.val+dst.val,_,Nat.le_add_right _ _,by simpa only [destination] using capacity,written⟩


theorem step_float32_core_chosen {choices : Spec.SourceChoices} (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Code.slots ((f.locals++f.vals).map Code.valueType) < exec.slots.length)
    (point : FramePoint emission sourceStore raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F32 (.mk_num__1 .F32 value)]}) ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  apply WP.spec_mono (step_float32_core_forward_chosen occurrence memory hooks floats allocator exec store platform index raw inst compiled C targets next output sourceStore ambient f rest value after last frameFound instanceFound codeFound pcBound slots capacity point typed)
  rintro out ⟨success,sameStore,samePlatform,pc,g,forward,rest⟩
  exact ⟨success,sameStore,samePlatform,pc,g,rest⟩

theorem step_float64_core_forward_chosen {choices : Spec.SourceChoices} (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Code.slots ((f.locals++f.vals).map Code.valueType) < exec.slots.length)
    (point : FramePoint emission sourceStore raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame), raw.pc.val < pc.val ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 value)]}) ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  rcases corePoint_float64_head value after point.code with ⟨target,forward,fetched,tail⟩ | ⟨dst,bits,valueEq,position,fetched,tail⟩
  · have targetPoint : FramePoint emission sourceStore {raw with pc := target} {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      sourceStore ambient {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} rest C targets next output target last frameFound instanceFound codeFound pcBound forward fetched slots targetPoint typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨success,sameStore,samePlatform,target,_,forward,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward tail.current.entry_bound⟩,?_⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · subst value
    have destination : dst.val = Code.slots ((f.locals++f.vals).map Code.valueType) := by
      simpa only [point.locals,List.map_append,Code.slots_append] using position
    have frameTyped : Abs.FrameTyped sourceStore {f with code := .CONST .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val)) :: after} [] := by
      cases typed.typed.frames with | cons head _ => exact head
    obtain ⟨nextState,actual,fresh,simulation⟩ := Abs.Core.constant_chosen_progress occurrence sourceStore ambient f rest after .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val)) typed
    have nextEq : (⟨sourceStore,ambient,{f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val))]}::rest,[]⟩ : Abs.AState) = nextState := Abs.AResult.next.inj actual
    subst nextState
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
      (.Const64 dst bits) last frameFound instanceFound codeFound fetched pcBound
    intro pc pcNext
    have nextPoint : FramePoint emission sourceStore {raw with pc := pc}
        {f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 (Builtins.floatOfBits 64 bits.val))]} compiled C targets next output := by
      refine ⟨point.bindings,point.locals,?_,?_⟩
      · have labels : LabelsMatch (f.vals++[]) f.labels targets := by simpa only [List.append_nil] using point.labels
        have heights := Abs.frameTyped_heights frameTyped
        exact labels.replace_suffix heights
      · simpa only [List.map_append,List.map_cons,List.map_nil,Code.valueType,valtype_numtype,pcNext] using tail
    apply WP.spec_mono (dispatch_float64_slots memory hooks floats allocator
      {exec with frames := exec.frames.set index {raw with pc := pc}} store platform index raw dst bits f after slots destination
      (by simpa only [destination] using capacity))
    intro out effect
    obtain ⟨success,sameStore,samePlatform,represented,written,unchanged⟩ := effect
    refine ⟨success,sameStore,samePlatform,pc,_,by omega,unchanged,represented,nextPoint,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inr rfl,?_,?_⟩
    · exact ChosenConcreteSim.of_source _ _ _ _ _ simulation
    · exact Or.inr ⟨raw.base.val+dst.val,_,Nat.le_add_right _ _,by simpa only [destination] using capacity,written⟩


theorem step_float64_core_chosen {choices : Spec.SourceChoices} (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (sourceStore : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (slots : FrameSlots exec raw f)
    (capacity : raw.base.val+Code.slots ((f.locals++f.vals).map Code.valueType) < exec.slots.length)
    (point : FramePoint emission sourceStore raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission sourceStore {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped ⟨sourceStore,ambient,g::rest,[]⟩ ∧ FrameMetadata f g ∧
        (g = {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} ∨
          g = {f with code := after,vals := f.vals ++ [.CONST .F64 (.mk_num__1 .F64 value)]}) ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false false
          ⟨sourceStore,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after}::rest,[]⟩
          ⟨sourceStore,ambient,g::rest,[]⟩ ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word) ⦄ := by
  apply WP.spec_mono (step_float64_core_forward_chosen occurrence memory hooks floats allocator exec store platform index raw inst compiled C targets next output sourceStore ambient f rest value after last frameFound instanceFound codeFound pcBound slots capacity point typed)
  rintro out ⟨success,sameStore,samePlatform,pc,g,forward,rest⟩
  exact ⟨success,sameStore,samePlatform,pc,g,rest⟩

end Exec.Interp.StructuredMachine.FloatConstant
