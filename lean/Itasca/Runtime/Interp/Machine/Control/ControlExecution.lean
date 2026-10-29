import Itasca.Runtime.Interp.Machine.Control.BranchInversion
import Itasca.Runtime.Interp.Machine.Control.BranchPoint
import Itasca.Runtime.Interp.Machine.Control.ControlInversion
import Itasca.Runtime.Interp.Relations.PrefixDispatch
import Itasca.Runtime.Interp.Machine.Control.UniformSource
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.SourceMachine.Core.Bound
import Itasca.Runtime.Interp.Machine.Retention.Ownership
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.Control.BranchOwned
import Itasca.Runtime.Interp.Machine.Control.BranchIfOwned
import Itasca.Runtime.Interp.Machine.Control.If
import Itasca.Runtime.Interp.Machine.Control.Loop
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Spec.Extend

/-!
Structured control fetch and whole-execution preservation. Fetch inversion for if, loop and branches supplies the execution lemmas with their explicit uniform or concrete emission premises.
-/

/-! ## Control Fetch -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

theorem loop_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame} [OrdinaryHeads (emission compiled)]
    (bt : blocktype) (body after : List instr)
    (point : FramePoint s raw {f with code := .LOOP bt body::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases code_rel_loop_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨front,params,results,entry,exit,live,shape,atEntry,signature,fetch,bodyCode,continuation,bounds⟩ := branch
    exact ⟨.LoopHead,by simpa only [atEntry] using fetch,.loopHead⟩

theorem if_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame} [OrdinaryHeads (emission compiled)]
    (bt : blocktype) (yes no after : List instr)
    (point : FramePoint s raw {f with code := .IFELSE bt yes no::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases code_rel_if_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨front,params,results,cond,noEntry,yesExit,exit,yn,yb,nn,nb,shape,signature,condition,fetch,yesCode,skip,noCode,continuation,bounds⟩ := branch
    exact ⟨_,fetch,.jumpZero cond noEntry⟩

theorem transfer_prefix (dst src count : U32) : PrefixInstruction (Compiler.transferInstruction dst src count) := by
  unfold Compiler.transferInstruction
  split
  · exact .copy ..
  · split
    · exact .copy2 ..
    · exact .copyN ..

theorem branch_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame} [OrdinaryHeads (emission compiled)]
    (depth : Nat) (after : List instr)
    (point : FramePoint s raw {f with code := .BR (.mk_uN depth)::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases code_rel_branch_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨target,dst,src,count,finish,lookup,live,layout,fragment,remaining⟩ := branch
    by_cases noCopy : count = 0#u32 ∨ src = dst
    · refine ⟨.Jump target.target,?_,.jump _⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Compiler.branchInstructions,if_pos noCopy,List.getElem?_cons_zero])
    · refine ⟨Compiler.transferInstruction dst src count,?_,transfer_prefix ..⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Compiler.branchInstructions,if_neg noCopy,List.getElem?_cons_zero])

theorem branch_if_fetch {s raw compiled C targets next output} {f : SourceMachine.AFrame} [OrdinaryHeads (emission compiled)]
    (depth : Nat) (after : List instr)
    (point : FramePoint s raw {f with code := .BR_IF (.mk_uN depth)::after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction ∧ PrefixInstruction instruction := by
  rcases code_rel_branch_if_inv point.code.current with ⟨target,forward,fetch,tail⟩ | branch
  · exact ⟨_,fetch,.jump target⟩
  · obtain ⟨before,target,dst,src,count,cond,resume,shape,lookup,live,layout,condition,fragment,continuation⟩ := branch
    by_cases noCopy : count = 0#u32 ∨ src = dst
    · refine ⟨.JumpIfNonZero cond target.target,?_,.jumpNonzero ..⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Compiler.branchIfInstructions,if_pos noCopy,List.getElem?_cons_zero])
    · refine ⟨.JumpIfZero cond resume,?_,.jumpZero ..⟩
      simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [Compiler.branchIfInstructions,if_neg noCopy,List.getElem?_cons_zero])
end Itasca.Runtime.Interp.Machine

end

/-! ## Control Execution -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_if_execution_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (bt : blocktype) (yes no : List instr) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .IFELSE bt yes no :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := if_fetch bt yes no after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_if memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest bt yes no after last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,sourceStep⟩ := effect
  have uniform : UniformConcreteSim raw.pc.val pc.val false pending
      ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩
      ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
    rcases sourceStep with same | step
    · subst g
      exact simulation.uniform_same (by scalar_tac)
    · apply UniformConcreteSim.single
      apply SourceMachine.typed_if_positive _ _ _ _ _ _ _ _ _ machine.typed.typed
      simpa only [SourceMachine.Core.step, SourceMachine.Core.instruction] using step
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases sourceStep with same | step
    · rw [same]; exact machine.core
    · exact Machine.core_step_supported machine.typed machine.core step
  have ownership := Machine.owned_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
  have bounded := Machine.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
  refine ⟨success,storeSame,platformSame,pc,g,pending,?_,simulation,uniform,ownership,bounded⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

theorem step_loop_execution_uniform     (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
(platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (bt : blocktype) (body : List instr) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .LOOP bt body :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate,out.2.2.2))) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := loop_fetch bt body after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_loop memory hooks floats allocator law exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest bt body after last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨storeSame,success | stopped⟩ := effect
  · obtain ⟨success,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,sourceStep⟩ := success
    have uniform : UniformConcreteSim raw.pc.val pc.val false pending
        ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩
        ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases sourceStep with same | step
      · subst g
        exact simulation.uniform_same (by scalar_tac)
      · apply UniformConcreteSim.single
        apply SourceMachine.typed_loop_positive _ _ _ _ _ _ _ _ machine.typed.typed
        simpa only [SourceMachine.Core.step, SourceMachine.Core.instruction] using step
    have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases sourceStep with same | step
      · rw [same]; exact machine.core
      · exact Machine.core_step_supported machine.typed machine.core step
    have ownership := Machine.owned_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
    have bounded := Machine.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
    refine ⟨storeSame,Or.inl ⟨success,pc,g,pending,?_,simulation,uniform,ownership,bounded⟩⟩
    exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
      represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered
  · exact ⟨storeSame,Or.inr stopped⟩

theorem step_loop_execution     (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
(platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (bt : blocktype) (body : List instr) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .LOOP bt body :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate,out.2.2.2))) ⦄ := by
  apply WP.spec_mono (step_loop_execution_uniform memory hooks floats allocator law platform frameIndex view code exec store raw inst compiled ambient f rest bt body after C targets next output found slots last frameFound codeFound program point expected machine)
  rintro out ⟨storeSame,success | stopped⟩
  · rcases success with ⟨success,pc,g,pending,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨storeSame,Or.inl ⟨success,pc,g,pending,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨storeSame,Or.inr stopped⟩

theorem step_branch_execution_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (depth : Nat) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .BR (.mk_uN depth) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .BR (.mk_uN depth) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .BR (.mk_uN depth) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := branch_fetch depth after point
  have pcBound := program.fetched_bound instruction fetched
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = frameIndex.val := by change exec.frames.length-1 = frameIndex.val; omega
    rw [position]
    exact frameFound
  have binding := (machine.stack.top raw top).binding
  have capacity := slots.capacity binding
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_branch_owned_uniform memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest depth after last frameFound found codeFound pcBound machine.typed slots capacity point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,uniform,ownership,bounded⟩ := effect
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    exact Machine.SyntaxClosure.supported closure machine.core
  refine ⟨success,storeSame,platformSame,pc,g,pending,?_,simulation,uniform,fun _ h => FrameOwnershipClosure.stateful ownership h,fun _ h => bounded.state h⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

theorem step_branch_if_execution_uniform (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (depth : Nat) (after : List instr)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .BR_IF (.mk_uN depth) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : SourceMachine.AFrame) (pending : Bool),
        Execution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := branch_if_fetch depth after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_branch_if_owned_uniform memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest depth after (.br _) last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,uniform,ownership,bounded⟩ := effect
  have covered : SourceMachine.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    exact Machine.SyntaxClosure.supported closure machine.core
  refine ⟨success,storeSame,platformSame,pc,g,pending,?_,simulation,uniform,fun _ h => FrameOwnershipClosure.stateful ownership h,fun _ h => bounded.state h⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered

end Itasca.Runtime.Interp.Machine

end
