import Exec.Interp.Machines.Uniform.UniformSourceControl
import Exec.Interp.StructuredMachine.ControlSemantics
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.StructuredMachine.LocalGetOwned
import Exec.Interp.StructuredMachine.LocalWriteOwned
import Exec.Interp.StructuredMachine.LocalCapacity
import Exec.Interp.StructuredMachine.LocalPrefix
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.Core.StoreTransport
import Exec.Spec.Extend
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std SpecExt Exec.Spec
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
variable {allowed supported owned} (semantics : ControlSemantics allowed supported owned)
include semantics
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_localGet_execution_owned_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (localIndex : U32)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,allowed⟩ := localGet_fetch localIndex.val after point
  have pcBound := program.fetched_bound instruction fetched
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = frameIndex.val := by change exec.frames.length-1 = frameIndex.val; omega
    rw [position]
    exact frameFound
  have binding := (machine.stack.top raw top).binding
  have capacity := structured_local_get_storage_capacity binding inst compiled found codeFound program.checked localIndex.val after point
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_localGet_owned_forward memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest localIndex after last frameFound found codeFound pcBound machine.typed slots capacity point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched allowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,forward,pendingEq,unchanged,represented,retained,typed,metadata,closure,simulation,shape,ownership⟩ := effect
  subst pending
  have uniform := simulation.uniform_forward forward (by scalar_tac)
  have covered : supported ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | ⟨locals,values,same⟩
    · rw [same]; exact machine.core
    · rw [same]; exact semantics.syntax_preserved (SyntaxClosure.tail _ _ _ _ _) machine.core
  refine ⟨success,storeSame,platformSame,pc,g,false,?_,simulation,uniform,fun _ h => semantics.ownership ownership h,fun _ bounded => closure.codeBound bounded⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered


theorem step_localGet_execution_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (localIndex : U32)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .LOCAL_GET (.mk_uN localIndex.val) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  apply WP.spec_mono (step_localGet_execution_owned_uniform semantics memory hooks floats allocator platform frameIndex view code exec store raw inst compiled ambient f rest after localIndex C targets next output found slots last frameFound codeFound program point expected machine)
  rintro out ⟨success,same,platform,pc,g,pending,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,same,platform,pc,g,pending,machine,simulation,ownership,bounded⟩

theorem step_localWrite_execution_owned_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (localIndex : U32) (keep : Bool)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,allowed⟩ := localWrite_fetch localIndex.val keep after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_localWrite_owned_forward memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest localIndex keep after last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched allowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,forward,pendingEq,unchanged,represented,retained,typed,metadata,closure,simulation,shape,ownership⟩ := effect
  subst pending
  have uniform := simulation.uniform_forward forward (by scalar_tac)
  have covered : supported ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases shape with same | ⟨locals,values,same⟩
    · rw [same]; exact machine.core
    · rw [same]; exact semantics.syntax_preserved (SyntaxClosure.tail _ _ _ _ _) machine.core
  refine ⟨success,storeSame,platformSame,pc,g,false,?_,simulation,uniform,fun _ h => semantics.ownership ownership h,fun _ bounded => closure.codeBound bounded⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered
theorem step_localWrite_execution_owned (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (localIndex : U32) (keep : Bool)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := (if keep then .LOCAL_TEE (.mk_uN localIndex.val) else .LOCAL_SET (.mk_uN localIndex.val)) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  apply WP.spec_mono (step_localWrite_execution_owned_uniform semantics memory hooks floats allocator platform frameIndex view code exec store raw inst compiled ambient f rest after localIndex keep C targets next output found slots last frameFound codeFound program point expected machine)
  rintro out ⟨success,same,platform,pc,g,pending,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,same,platform,pc,g,pending,machine,simulation,ownership,bounded⟩


end Exec.Interp.StructuredMachine
