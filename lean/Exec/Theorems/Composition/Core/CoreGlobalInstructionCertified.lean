import Exec.Interp.Core.GlobalExecution
import Exec.Interp.State.GlobalMutationStep
import Exec.Theorems.Composition.GlobalMutationShape
import Exec.Theorems.Composition.Certified.CertifiedCoreContent
import Exec.Theorems.Composition.Core.CoreOwnership
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
theorem step_globalSet_core_certified (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (index : Nat)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : CoreFramePoint (Store.decodeStore view code store) raw {f with code := .GLOBAL_SET (.mk_uN index) :: after} compiled C targets next output)
    (certified : CertifiedCoreStore view code store)
    (owned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩)
    (expected : List valtype)
    (machine : CoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      CertifiedCoreStore view code out.2.2.1 ∧
      Store.ownershipBounds out.2.2.1 = Store.ownershipBounds store ∧
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      Extend_store initial.store (Store.decodeStore view code out.2.2.1) ∧
      ∃ pc : U32, ∃ g : Abs.AFrame,
        CoreExecution view code out.2.2.1 out.2.1 ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_globalSet_head index after point.code with ⟨target,forward,fetch,tail⟩ | operation
    · exact program.fetched_bound _ fetch
    · obtain ⟨ty,idx,src,front,indexEq,lookup,values,position,fetch,tail⟩ := operation
      exact program.fetched_bound _ fetch
  have execute := step_globalSet_core_execution memory hooks floats allocator platform frameIndex view code exec store raw inst compiled
    ambient f rest after index C targets next output found moduleEq slots last frameFound codeFound program point expected machine
  obtain ⟨out,run,effect⟩ := WP.spec_imp_exists execute
  rw [run,WP.spec_ok]
  have extension := effect.2.2.2.1
  rcases coreFramePoint_globalSet_mutation memory hooks floats allocator platform frameIndex view code exec store raw inst compiled
    ambient f rest after index C targets next output found moduleEq slots last frameFound codeFound pcBound point machine.typed with jump | mutation
  · obtain ⟨target,forward,fetch⟩ := jump
    have unchanged := step_jump_exact memory hooks floats allocator exec store platform frameIndex raw inst compiled target
      last frameFound found codeFound pcBound fetch
    rw [run,WP.spec_ok] at unchanged
    exact ⟨by simpa only [unchanged.2.2.1] using certified,by rw [unchanged.2.2.1],effect⟩
  · obtain ⟨front,value,values,wellFormed,mutation⟩ := mutation
    rw [run,WP.spec_ok] at mutation
    have valueOwned : Abs.Ownership.ValueOwned (Store.ownershipBounds store) value := by
      have frameOwned := owned.2 {f with code := .GLOBAL_SET (.mk_uN index) :: after} (by simp)
      exact frameOwned.2 value (by simp [values])
    have shape := Store.global_mutation_shape certified.shape mutation wellFormed valueOwned
    obtain ⟨idx,old,lo,hi,issued,mutable,typed,represented,high,same⟩ := mutation
    have fresh : CertifiedCoreStore view code out.2.2.1 := certified.content_update
      (by rw [same]) (by rw [same]) (by rw [same]) (by rw [same]) (by rw [same]) (by rw [same]) shape extension
    exact ⟨fresh,by rw [same]; rfl,effect⟩
end Exec.Theorems
