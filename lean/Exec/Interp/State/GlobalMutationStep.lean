import Exec.Interp.State.GlobalMutation
import Exec.Interp.State.GlobalCoreCertifiedStep
namespace Exec.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_global_set_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : Abs.AFrame) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Code.valueType value) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index)
      ⦃ out => GlobalMutation store out.2.2.1 value ⦄ := by
  classical
  have handler : (if decide (Code.width (sourceType object.ty.valtype) = 2) then
      runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index
      else runtime.interp.execute_global_set memory exec store raw.instance raw.base src index)
      ⦃ out => GlobalMutation store out.2.2 value ⦄ := by
    simp only [sourceType_width_two]
    by_cases vector : object.ty.valtype = .V128
    · simp only [vector,decide_true,ite_true]
      exact global_set2_mutation memory exec store raw src index inst address object f front value
        found mapped issued slots values position vector mutable typed
    · simp only [vector,decide_false,ite_false]
      exact global_set_mutation memory exec store raw src index inst address object f front value
        found mapped issued slots values position vector mutable typed
  apply WP.spec_mono (dispatch_globalSet memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
    (decide (Code.width (sourceType object.ty.valtype) = 2)) src index handler)
  exact fun _ effect => effect.1

theorem step_global_set_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : Abs.AFrame) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Code.valueType value)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index))
    (pcBound : raw.pc.val < U32.max) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => GlobalMutation store out.2.2.1 value ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst compiled
    (Code.globalSetInstruction (decide (Code.width (sourceType object.ty.valtype) = 2)) src index) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  exact dispatch_global_set_mutation memory hooks floats allocator
    {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store raw src index inst address object f front value
    platform frameIndex found mapped issued slots values position mutable typed

/-- The exact instruction certificate exposes either a forward administrative
jump or a write of the original source stack's top value. -/
theorem coreFramePoint_globalSet_mutation (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (point : CoreFramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target)) ∨
    (∃ front value, f.vals = front ++ [value] ∧ wf_val value ∧
      runtime.interp.step memory hooks floats allocator exec store platform ⦃ out => GlobalMutation store out.2.2.1 value ⦄) := by
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code := .GLOBAL_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases coreFramePoint_globalSet_prepare view code store inst raw f compiled C targets next output after index moduleEq frameTyped point with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch⟩
  · obtain ⟨front,value,idx,src,address,object,indexEq,values,valueWf,heights,mapped,issued,mutable,valueType,position,fetch,tail⟩ := operation
    subst index
    refine Or.inr ⟨front,value,values,valueWf,?_⟩
    exact step_global_set_mutation memory hooks floats allocator exec store raw src idx inst address object f front value
      platform frameIndex found mapped issued slots values position mutable valueType compiled last frameFound codeFound fetch pcBound
end Exec.Interp
