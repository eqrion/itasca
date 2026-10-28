import Itasca.Runtime.Interp.Core.Mutation
import Itasca.Runtime.Interp.StructuredMachine.GlobalMutationStep
import Itasca.Runtime.Interp.Control.PendingJump
namespace Itasca.Runtime.Interp.StructuredMachine.Global
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
theorem coreFramePoint_globalSet_store_mutation (platform : P) (frameIndex : Usize)
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
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CoreStoreMutation view ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩ store out.2.2.1 ⦄ := by
  rcases coreFramePoint_globalSet_mutation memory hooks floats allocator platform frameIndex view code exec store raw inst compiled
    ambient f rest after index C targets next output found moduleEq slots last frameFound codeFound pcBound point typed with jump | mutation
  · obtain ⟨target,forward,fetch⟩ := jump
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform frameIndex raw inst compiled target
      last frameFound found codeFound pcBound fetch)
    intro out effect
    rw [effect.2.2.1]
    exact .unchanged
  · obtain ⟨front,value,values,wellFormed,mutation⟩ := mutation
    apply WP.spec_mono mutation
    intro out effect
    apply CoreStoreMutation.global ?_ wellFormed effect
    exact Or.inr ⟨{f with code := .GLOBAL_SET (.mk_uN index) :: after},by simp,Or.inr (by simpa only [values] using List.mem_append_right front (List.mem_singleton_self value))⟩
end Itasca.Runtime.Interp.StructuredMachine.Global
