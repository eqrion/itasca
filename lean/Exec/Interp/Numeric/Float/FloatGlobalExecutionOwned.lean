import Exec.Interp.Machines.FloatCore.FloatCoreTransitions
import Exec.Interp.Machines.Core.CoreBound
import Exec.Interp.Machines.Core.CoreOwnership
import Exec.Interp.Numeric.Float.FloatGlobalCertifiedStepOwned
import Exec.Interp.FloatCore.OrdinaryExecution
import Exec.Interp.Core.StoreTransport
import Exec.Interp.Numeric.Float.FloatJump
import Exec.Spec.Extend
namespace Exec.Interp.FloatGlobal
open Aeneas Aeneas.Std SpecExt Exec.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_globalGet_core_execution_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : FloatFramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_GET (.mk_uN index) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : FloatCoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, ∃ g : Abs.AFrame,
        FloatCoreExecution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, Abs.Ownership.CoreOwned bounds initial → Abs.Ownership.CoreOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = frameIndex.val := by change exec.frames.length-1 = frameIndex.val; omega
    rw [position]
    exact frameFound
  have binding := (machine.stack.top raw top).binding
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_globalGet_head index after point.code with ⟨target,forward,fetch,tail⟩ | ⟨mutability,ty,idx,dst,indexEq,lookup,position,fetch,tail⟩
    · exact program.fetched_bound _ fetch
    · exact program.fetched_bound _ fetch
  rcases coreFramePoint_globalGet_step_owned memory hooks floats allocator platform frameIndex view code exec store raw inst compiled ambient f rest after index C targets next output found moduleEq slots binding last frameFound codeFound program.checked pcBound small point machine.typed with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    apply WP.spec_mono (step_float_forward_jump memory hooks floats allocator exec store platform frameIndex raw inst compiled
      (Store.decodeStore view code store) ambient {f with code := .GLOBAL_GET (.mk_uN index) :: after} rest C targets next output target last frameFound found codeFound pcBound forward fetch slots tail machine.typed)
    intro out effect
    obtain ⟨success,storeSame,platformSame,exactState,represented,retained,typed,simulation⟩ := effect
    refine ⟨success,storeSame,platformSame,target,_,?_,simulation,fun _ owned => owned,fun _ h => h⟩
    exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw frameIndex target last frameFound program (.ready retained)
      represented ⟨rfl,rfl,rfl,rfl⟩ (by rw [exactState]) (by rw [exactState]; exact .refl _ _) typed machine.core
  · apply WP.spec_mono operation
    intro out effect
    obtain ⟨success,storeSame,platformSame,g,pc,pcNext,unchanged,typed,source,represented,retained,⟨values,shape⟩,prefixEffect,sourceStep⟩ := effect
    have metadata : FrameMetadata {f with code := .GLOBAL_GET (.mk_uN index) :: after} g := by rw [shape]; exact ⟨rfl,rfl,rfl,rfl⟩
    have covered : Abs.FloatCoreState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      exact Abs.FloatCore.step_covered _ _ machine.typed.typed machine.core sourceStep
    refine ⟨success,storeSame,platformSame,pc,g,?_,?_,float_core_owned_transition machine.typed machine.core (Or.inr sourceStep),float_core_bound_transition machine.typed machine.core (Or.inr sourceStep)⟩
    · exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
        (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program (.ready retained)
        represented metadata unchanged prefixEffect typed covered
    · exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (stepH_wf source).2)⟩

theorem step_globalSet_core_execution_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FloatFramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : FloatCoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      Extend_store initial.store (Store.decodeStore view code out.2.2.1) ∧
      ∃ pc : U32, ∃ g : Abs.AFrame,
        FloatCoreExecution view code out.2.2.1 out.2.1 ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ ∧
        (∀ bounds, Abs.Ownership.CoreOwned bounds initial → Abs.Ownership.CoreOwned bounds ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_globalSet_head index after point.code with ⟨target,forward,fetch,tail⟩ | operation
    · exact program.fetched_bound _ fetch
    · obtain ⟨ty,idx,src,front,indexEq,lookup,values,position,fetch,tail⟩ := operation
      exact program.fetched_bound _ fetch
  rcases coreFramePoint_globalSet_step_owned memory hooks floats allocator platform frameIndex view code exec store raw inst compiled ambient f rest after index C targets next output found moduleEq slots last frameFound codeFound pcBound point machine.typed with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    apply WP.spec_mono (step_float_forward_jump memory hooks floats allocator exec store platform frameIndex raw inst compiled
      (Store.decodeStore view code store) ambient {f with code := .GLOBAL_SET (.mk_uN index) :: after} rest C targets next output target last frameFound found codeFound pcBound forward fetch slots tail machine.typed)
    intro out effect
    obtain ⟨success,storeSame,platformSame,exactState,represented,retained,typed,simulation⟩ := effect
    simp only [storeSame]
    refine ⟨success,platformSame,.refl store,extend_store_refl _ machine.typed.typed.store,target,_,?_,simulation,fun _ owned => owned,fun _ h => h⟩
    exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw frameIndex target last frameFound program (.ready retained)
      represented ⟨rfl,rfl,rfl,rfl⟩ (by rw [exactState]) (by rw [exactState]; exact .refl _ _) typed machine.core
  · apply WP.spec_mono operation
    intro out effect
    obtain ⟨success,platformSame,stores,g,pc,pcNext,unchanged,typed,extension,source,represented,retained,⟨values,shape⟩,sourceStep⟩ := effect
    have metadata : FrameMetadata {f with code := .GLOBAL_SET (.mk_uN index) :: after} g := by rw [shape]; exact ⟨rfl,rfl,rfl,rfl⟩
    have covered : Abs.FloatCoreState ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ := by
      exact Abs.FloatCore.step_covered _ _ machine.typed.typed machine.core sourceStep
    refine ⟨success,platformSame,stores,extension,pc,g,?_,?_,float_core_owned_transition machine.typed machine.core (Or.inr sourceStep),float_core_bound_transition machine.typed machine.core (Or.inr sourceStep)⟩
    · exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false stores extension
        raw frameIndex pc last frameFound program (.ready retained)
        represented metadata (by rw [unchanged]) (by rw [unchanged]; exact .refl _ _) typed covered
    · exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (stepH_wf source).2)⟩
end Exec.Interp.FloatGlobal
