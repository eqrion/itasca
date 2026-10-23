import Exec.Interp.StructuredMachine.IfChosen
import Exec.Interp.StructuredMachine.LoopChosen
import Exec.Interp.StructuredMachine.BranchChosenOwned
import Exec.Interp.StructuredMachine.BranchIfChosenOwned
import Exec.Interp.Machines.Uniform.UniformSourceControl
import Exec.Interp.StructuredMachine.ControlSemantics
import Exec.Interp.Machines.Core.CoreBound
import Exec.Interp.Core.OwnershipClosure
import Exec.Interp.Machines.Core.CoreOwnership
import Exec.Interp.StructuredMachine.BranchOwned
import Exec.Interp.StructuredMachine.BranchIfOwned
import Exec.Interp.StructuredMachine.If
import Exec.Interp.StructuredMachine.Loop
import Exec.Interp.StructuredMachine.ControlFetch
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.Relations.Capacity
import Exec.Spec.Extend
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std SpecExt Exec.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)
  {emission : FunctionEmission} {allowed : instr → Prop} {supported : Abs.AState → Prop}
  {owned : Abs.Ownership.Bounds → Abs.AState → Prop}
  (semantics : ControlSemantics allowed supported owned)
variable {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat)
include semantics admissible vector occurrence

theorem step_if_execution_uniform_chosen (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (bt : blocktype) (yes no : List instr) (after : List instr)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .IFELSE bt yes no :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := if_fetch bt yes no after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_if_chosen admissible vector occurrence memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest bt yes no after last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,sourceStep⟩ := effect
  have uniform : UniformConcreteSim raw.pc.val pc.val false pending
      ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩
      ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
    rcases sourceStep with same | step
    · subst g
      exact (simulation.erases admissible).uniform_same (by scalar_tac)
    · apply UniformConcreteSim.single
      apply Abs.typed_if_positive _ _ _ _ _ _ _ _ _ machine.typed.typed
      simpa only [Abs.Core.step, Abs.Core.instruction] using step
  have covered : supported ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases sourceStep with same | step
    · rw [same]; exact machine.core
    · exact semantics.next_covered machine.typed machine.core step
  have ownership := semantics.owned_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
  have bounded := semantics.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
  refine ⟨success,storeSame,platformSame,pc,g,pending,?_,simulation,uniform,ownership,bounded⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered


theorem step_if_execution_chosen (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (bt : blocktype) (yes no : List instr) (after : List instr)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .IFELSE bt yes no :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .IFELSE bt yes no :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  apply WP.spec_mono (step_if_execution_uniform_chosen memory hooks floats allocator semantics admissible vector occurrence platform frameIndex view code exec store raw inst compiled ambient f rest bt yes no after C targets next output found slots last frameFound codeFound program point expected machine)
  rintro out ⟨success,storeSame,platformSame,pc,g,pending,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,storeSame,platformSame,pc,g,pending,machine,simulation,ownership,bounded⟩

theorem step_loop_execution_uniform_chosen     (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
(platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (bt : blocktype) (body : List instr) (after : List instr)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .LOOP bt body :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate,out.2.2.2))) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := loop_fetch bt body after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_loop_chosen admissible vector occurrence memory hooks floats allocator law exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest bt body after last frameFound found codeFound pcBound machine.typed slots point)
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
        exact (simulation.erases admissible).uniform_same (by scalar_tac)
      · apply UniformConcreteSim.single
        apply Abs.typed_loop_positive _ _ _ _ _ _ _ _ machine.typed.typed
        simpa only [Abs.Core.step, Abs.Core.instruction] using step
    have covered : supported ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases sourceStep with same | step
      · rw [same]; exact machine.core
      · exact semantics.next_covered machine.typed machine.core step
    have ownership := semantics.owned_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
    have bounded := semantics.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))
    refine ⟨storeSame,Or.inl ⟨success,pc,g,pending,?_,simulation,uniform,ownership,bounded⟩⟩
    exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
      (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
      represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered
  · exact ⟨storeSame,Or.inr stopped⟩


theorem step_loop_execution_chosen     (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
(platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (bt : blocktype) (body : List instr) (after : List instr)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .LOOP bt body :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .LOOP bt body :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate,out.2.2.2))) ⦄ := by
  apply WP.spec_mono (step_loop_execution_uniform_chosen memory hooks floats allocator semantics admissible vector occurrence law platform frameIndex view code exec store raw inst compiled ambient f rest bt body after C targets next output found slots last frameFound codeFound program point expected machine)
  rintro out ⟨storeSame,success | stopped⟩
  · rcases success with ⟨success,pc,g,pending,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨storeSame,Or.inl ⟨success,pc,g,pending,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨storeSame,Or.inr stopped⟩

theorem step_branch_execution_uniform_chosen (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (depth : Nat) (after : List instr)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .BR (.mk_uN depth) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .BR (.mk_uN depth) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .BR (.mk_uN depth) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
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
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_branch_owned_uniform_chosen (allowed := allowed) admissible vector occurrence memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest depth after last frameFound found codeFound pcBound machine.typed slots capacity point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,uniform,ownership,bounded⟩ := effect
  have covered : supported ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    exact semantics.syntax_preserved closure machine.core
  refine ⟨success,storeSame,platformSame,pc,g,pending,?_,simulation,uniform,fun _ h => semantics.ownership ownership h,fun _ h => bounded.state h⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered


theorem step_branch_execution_chosen (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (depth : Nat) (after : List instr)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .BR (.mk_uN depth) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .BR (.mk_uN depth) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .BR (.mk_uN depth) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  apply WP.spec_mono (step_branch_execution_uniform_chosen memory hooks floats allocator semantics admissible vector occurrence platform frameIndex view code exec store raw inst compiled ambient f rest depth after C targets next output found slots last frameFound codeFound program point expected machine)
  rintro out ⟨success,storeSame,platformSame,pc,g,pending,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,storeSame,platformSame,pc,g,pending,machine,simulation,ownership,bounded⟩

theorem step_branchIf_execution_uniform_chosen (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (depth : Nat) (after : List instr)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .BR_IF (.mk_uN depth) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched,prefixAllowed⟩ := branchIf_fetch depth after point
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_branchIf_owned_uniform_chosen admissible vector occurrence memory hooks floats allocator exec store platform frameIndex raw inst compiled C targets next output (Store.decodeStore view code store) ambient f rest depth after (semantics.branch depth) last frameFound found codeFound pcBound machine.typed slots point)
  rw [returned]
  simp only [WP.spec_ok]
  have preserved := step_prefix memory hooks floats allocator exec store platform frameIndex raw inst compiled instruction last frameFound found codeFound fetched prefixAllowed out returned
  obtain ⟨success,storeSame,platformSame,pc,g,targets',next',output',pending,unchanged,represented,retained,typed,metadata,closure,simulation,uniform,ownership,bounded⟩ := effect
  have covered : supported ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    exact semantics.syntax_preserved closure machine.core
  refine ⟨success,storeSame,platformSame,pc,g,pending,?_,simulation,uniform,fun _ h => semantics.ownership ownership h,fun _ h => bounded.state h⟩
  exact machine.ordinary view code ambient _ _ rest expected raw.pc.val false (.refl store)
    (extend_store_refl _ machine.typed.typed.store) raw frameIndex pc last frameFound program retained
    represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged preserved typed covered
theorem step_branchIf_execution_chosen (platform : P) (frameIndex : Usize)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)]
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (depth : Nat) (after : List instr)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst) (slots : FrameSlots exec raw f)
    (last : frameIndex.val+1 = exec.frames.length) (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .BR_IF (.mk_uN depth) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .BR_IF (.mk_uN depth) :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val pending ∧
        ChosenConcreteSim choices occurrence compiled.code.length raw.pc.val pc.val false pending initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩) ⦄ := by
  apply WP.spec_mono (step_branchIf_execution_uniform_chosen memory hooks floats allocator semantics admissible vector occurrence platform frameIndex view code exec store raw inst compiled ambient f rest depth after C targets next output found slots last frameFound codeFound program point expected machine)
  rintro out ⟨success,storeSame,platformSame,pc,g,pending,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,storeSame,platformSame,pc,g,pending,machine,simulation,ownership,bounded⟩


end Exec.Interp.StructuredMachine
