import Itasca.Runtime.Interp.State.GlobalCoreWrite
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalLowering
import Itasca.Runtime.Interp.Relations.Fetch

/-!
Global instruction dispatch through decoded values to a concrete step. Scalar and two-word global representations retain their separate width obligations.
-/

/-! ## Global Core Dispatch -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_globalGet {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex inst function base : Usize) (wide : Bool) (dst index : U32)
    (handler : (if wide then runtime.interp.execute_global_get2 memory exec store inst base dst index
        else runtime.interp.execute_global_get memory exec store inst base dst index) ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Code.globalGetInstruction wide dst index) ⦃ out => Q (out.1,out.2.1,out.2.2.1) ∧ out.2.2.2 = platform ⦄ := by
  have equation : runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Code.globalGetInstruction wide dst index) = (do
        let (result,next,nextStore) ← if wide then runtime.interp.execute_global_get2 memory exec store inst base dst index
          else runtime.interp.execute_global_get memory exec store inst base dst index
        Result.ok (result,next,nextStore,platform)) := by cases wide <;> rfl
  rw [equation]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next,nextStore⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl⟩

theorem dispatch_globalSet {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex inst function base : Usize) (wide : Bool) (src index : U32)
    (handler : (if wide then runtime.interp.execute_global_set2 memory exec store inst base src index
        else runtime.interp.execute_global_set memory exec store inst base src index) ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Code.globalSetInstruction wide src index) ⦃ out => Q (out.1,out.2.1,out.2.2.1) ∧ out.2.2.2 = platform ⦄ := by
  have equation : runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Code.globalSetInstruction wide src index) = (do
        let (result,next,nextStore) ← if wide then runtime.interp.execute_global_set2 memory exec store inst base src index
          else runtime.interp.execute_global_set memory exec store inst base src index
        Result.ok (result,next,nextStore,platform)) := by cases wide <;> rfl
  rw [equation]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next,nextStore⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl⟩
end Itasca.Runtime.Interp

end

/-! ## Global Core Dispatch Values -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem sourceType_width_two (ty : Itasca.types.ValueType) :
    Code.width (sourceType ty) = 2 ↔ ty = .V128 := by
  cases ty <;> simp [sourceType,Code.width]

theorem sourceType_width_scalar (ty : Itasca.types.ValueType) (scalar : ty ≠ .V128) :
    Code.width (sourceType ty) = 1 := by
  cases ty <;> simp_all [sourceType,Code.width]

theorem dispatch_global_get_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType))
    (capacity : raw.base.val + dst.val + Code.width (sourceType object.ty.valtype) ≤ exec.slots.length)
    (small : object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.globalGetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) dst index) ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ out.2.2.1 = store ∧
      ∃ nextFrame, Abs.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  classical
  have handler : (if decide (Code.width (sourceType object.ty.valtype) = 2) then
      runtime.interp.execute_global_get2 memory exec store raw.instance raw.base dst index
      else runtime.interp.execute_global_get memory exec store raw.instance raw.base dst index) ⦃ out => out.1 = .Ok () ∧ out.2.2 = store ∧ ∃ nextFrame, Abs.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧ FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
    simp only [sourceType_width_two]
    by_cases vector : object.ty.valtype = .V128
    · simp only [vector,decide_true,ite_true]
      exact global_get2_core memory view code exec store raw dst index inst address object s f rest after
        found mapped issued storeEq moduleEq slots position (by simpa only [vector,sourceType,Code.width] using capacity) vector
    · simp only [vector,decide_false,ite_false]
      exact global_get_core memory view code exec store raw dst index inst address object s f rest after
        found mapped issued storeEq moduleEq slots position (by rw [sourceType_width_scalar _ vector] at capacity; omega) vector small
  apply WP.spec_mono (dispatch_globalGet memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
    (decide (Code.width (sourceType object.ty.valtype) = 2)) dst index handler)
  intro out effect
  exact ⟨effect.1.1,effect.2,effect.1.2⟩

theorem dispatch_global_set_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (mutable : object.ty.mutability = .Var)
    (valueWf : wf_val value) (typed : sourceType object.ty.valtype = Code.valueType value) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index) ⦃ out =>
      out.2.2.2 = platform ∧ out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ nextFrame, Abs.Core.globalSet s f rest index.val after =
          .next {s with store := Store.decodeStore view code out.2.2.1, frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ⦄ := by
  classical
  have handler : (if decide (Code.width (sourceType object.ty.valtype) = 2) then
      runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index
      else runtime.interp.execute_global_set memory exec store raw.instance raw.base src index) ⦃ out => out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧ ∃ nextFrame, Abs.Core.globalSet s f rest index.val after = .next {s with store := Store.decodeStore view code out.2.2, frames := nextFrame :: rest} ∧ FrameSlots out.2.1 raw nextFrame ⦄ := by
    simp only [sourceType_width_two]
    by_cases vector : object.ty.valtype = .V128
    · simp only [vector,decide_true,ite_true]
      exact global_set2_core memory view code exec store raw src index inst address object s f rest after front value
        found mapped issued storeEq moduleEq slots values position vector mutable valueWf typed
    · simp only [vector,decide_false,ite_false]
      exact global_set_core memory view code exec store raw src index inst address object s f rest after front value
        found mapped issued storeEq moduleEq slots values position vector mutable valueWf typed
  apply WP.spec_mono (dispatch_globalSet memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
    (decide (Code.width (sourceType object.ty.valtype) = 2)) src index handler)
  intro out effect
  exact ⟨effect.2,effect.1⟩

end Itasca.Runtime.Interp

end

/-! ## Global Core Step -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_global_get_simulation (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Code.slots ((f.locals ++ f.vals).map Code.valueType))
    (capacity : raw.base.val + dst.val + Code.width (sourceType object.ty.valtype) ≤ exec.slots.length)
    (small : object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.globalGetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) dst index))
    (pcBound : raw.pc.val < U32.max)
    (sourceTyped : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index.val) :: after} :: rest,[]⟩) :
    let s : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index.val) :: after} :: rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ out.2.2.1 = store ∧
      ∃ nextFrame, Abs.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧
        Abs.CoreTyped {s with frames := nextFrame :: rest} ∧
        StepH (Abs.decode s) [] (Abs.decode {s with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 raw nextFrame ∧ ∃ pc : U32, pc.val = raw.pc.val+1 ∧ {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  dsimp only
  obtain ⟨next,abstract,fresh,source⟩ := Abs.Core.globalGet_progress (Store.decodeStore view code store) ambient f rest index.val after sourceTyped
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst compiled
    (Code.globalGetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) dst index) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  apply WP.spec_mono (dispatch_global_get_core memory hooks floats allocator view code
    {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store raw dst index inst address object
    ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index.val) :: after} :: rest,[]⟩ f rest after platform frameIndex
    found mapped issued rfl moduleEq slots position capacity small)
  intro out effect
  obtain ⟨success,platformSame,storeSame,nextFrame,actual,represented,unchanged,prefixEffect⟩ := effect
  rw [actual] at abstract
  cases abstract
  exact ⟨success,platformSame,storeSame,nextFrame,actual,fresh,source,represented,pc,pcNext,unchanged,prefixEffect⟩

theorem step_global_set_simulation (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (mutable : object.ty.mutability = .Var)
    (valueWf : wf_val value) (typed : sourceType object.ty.valtype = Code.valueType value)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index))
    (pcBound : raw.pc.val < U32.max)
    (sourceTyped : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index.val) :: after} :: rest,[]⟩) :
    let s : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index.val) :: after} :: rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧ out.1 = .Ok () ∧ (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}}) ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ nextFrame, Abs.Core.globalSet s f rest index.val after =
          .next {s with store := Store.decodeStore view code out.2.2.1, frames := nextFrame :: rest} ∧
        Abs.CoreTyped {s with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Extend_store s.store (Store.decodeStore view code out.2.2.1) ∧
        StepH (Abs.decode s) [] (Abs.decode {s with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 raw nextFrame ⦄ := by
  dsimp only
  obtain ⟨next,abstract,fresh,extension,source⟩ := Abs.Core.globalSet_progress (Store.decodeStore view code store) ambient f rest index.val after sourceTyped
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst compiled
    (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  apply WP.spec_mono (dispatch_global_set_core memory hooks floats allocator view code
    {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store raw src index inst address object
    ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index.val) :: after} :: rest,[]⟩ f rest after front value platform frameIndex
    found mapped issued rfl moduleEq slots values position mutable valueWf typed)
  intro out effect
  obtain ⟨platformSame,success,unchanged,metadata,nextFrame,actual,represented⟩ := effect
  rw [actual] at abstract
  cases abstract
  exact ⟨platformSame,success,⟨pc,pcNext,unchanged⟩,metadata,nextFrame,actual,fresh,extension,source,represented⟩

end Itasca.Runtime.Interp

end
