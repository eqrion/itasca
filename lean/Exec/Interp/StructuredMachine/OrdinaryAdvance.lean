import Exec.Interp.StructuredMachine.UniformAdvance
import Exec.Interp.StructuredMachine.NumericNoTrap
import Exec.Interp.StructuredMachine.NumericExecutionOwned
import Exec.Interp.StructuredMachine.LocalExecutionOwned
import Exec.Interp.StructuredMachine.ControlExecution
import Exec.Interp.StructuredMachine.IntegerConstantExecutionOwned
import Exec.Interp.StructuredMachine.Advance
import Exec.Interp.Machines.Slice.SliceOpcode
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Numeric
theorem step_numeric_total_advance_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : Instruction) (after : List instr)
    (total : ∀ a b, op.apply a b ≠ none)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      UniformAdvance view code store out.2.1 expected compiled.code.length raw.pc.val false initial ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched⟩ := numeric_fetched op after point
  have normal := step_numeric_no_trap memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest op after total last hf hi hc (program.fetched_bound instruction fetched) machine.typed slots point
  obtain ⟨out,returned,effect⟩ := WP.spec_imp_exists (step_numeric_execution_owned_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output
    ambient f rest op after last hf hi hc program slots point expected machine)
  rw [returned] at normal ⊢
  simp only [WP.spec_ok] at normal ⊢
  obtain ⟨sameStore,samePlatform,operation⟩ := effect
  rcases operation with success | ⟨trap,rejected,_⟩
  · obtain ⟨status,pc,g,fresh,simulation,uniform,ownership,bounded⟩ := success
    exact ⟨status,sameStore,samePlatform,⟨pc.val,false,_,fresh,simulation,uniform,ownership,rfl,bounded⟩⟩
  · rw [normal] at rejected
    cases rejected

theorem step_ordinary_advance_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : OrdinaryOpcode) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      UniformAdvance view code store out.2.1 expected compiled.code.length raw.pc.val false initial ⦄ := by
  dsimp only
  cases op with
  | const32 value =>
    apply WP.spec_mono (IntegerConstant.step_integer32_execution_owned_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
      view code ambient f rest value after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,pc,g,forward,fresh,simulation,ownership,bounded⟩ := effect
    exact ⟨success,sameStore,samePlatform,UniformAdvance.of_frame_forward fresh simulation forward ownership rfl bounded⟩
  | const64 value =>
    apply WP.spec_mono (IntegerConstant.step_integer64_execution_owned_forward memory hooks floats allocator exec store platform index raw inst compiled C targets next output
      view code ambient f rest value after last hf hi hc slots point expected machine program)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,pc,g,forward,fresh,simulation,ownership,bounded⟩ := effect
    exact ⟨success,sameStore,samePlatform,UniformAdvance.of_frame_forward fresh simulation forward ownership rfl bounded⟩
  | binary ty operation =>
    cases operation with
    | add =>
      exact step_numeric_total_advance_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output
        ambient f rest (.binary ty .ADD) after (by intro a b; simp [Instruction.apply,Abs.Numeric.binary]) last hf hi hc program slots point expected machine
    | sub =>
      exact step_numeric_total_advance_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output
        ambient f rest (.binary ty .SUB) after (by intro a b; simp [Instruction.apply,Abs.Numeric.binary]) last hf hi hc program slots point expected machine
    | eq =>
      exact step_numeric_total_advance_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output
        ambient f rest (.compare ty .EQ) after (by intro a b; simp [Instruction.apply,Abs.Numeric.binary]) last hf hi hc program slots point expected machine
    | ltU =>
      exact step_numeric_total_advance_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output
        ambient f rest (.compare ty (.LT .U)) after (by intro a b; simp [Instruction.apply,Abs.Numeric.binary]) last hf hi hc program slots point expected machine
  | eqz ty =>
    exact step_numeric_total_advance_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output
      ambient f rest (.eqz ty) after (by intro a b; simp [Instruction.apply]) last hf hi hc program slots point expected machine
  | localGet localIndex =>
    apply WP.spec_mono (step_localGet_execution_owned_uniform memory hooks floats allocator platform index view code exec store raw inst compiled ambient f rest after localIndex
      C targets next output hi slots last hf hc program point expected machine)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,pc,g,pending,fresh,simulation,uniform,ownership,bounded⟩ := effect
    exact ⟨success,sameStore,samePlatform,⟨pc.val,pending,_,fresh,simulation,uniform,ownership,rfl,bounded⟩⟩
  | localWrite localIndex keep =>
    apply WP.spec_mono (step_localWrite_execution_owned_uniform memory hooks floats allocator platform index view code exec store raw inst compiled ambient f rest after localIndex keep
      C targets next output hi slots last hf hc program point expected machine)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,pc,g,pending,fresh,simulation,uniform,ownership,bounded⟩ := effect
    exact ⟨success,sameStore,samePlatform,⟨pc.val,pending,_,fresh,simulation,uniform,ownership,rfl,bounded⟩⟩
  | branch depth =>
    apply WP.spec_mono (step_branch_execution_uniform memory hooks floats allocator platform index view code exec store raw inst compiled ambient f rest depth after
      C targets next output hi slots last hf hc program point expected machine)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,pc,g,pending,fresh,simulation,uniform,ownership,bounded⟩ := effect
    exact ⟨success,sameStore,samePlatform,⟨pc.val,pending,_,fresh,simulation,uniform,ownership,rfl,bounded⟩⟩
  | branchIf depth =>
    apply WP.spec_mono (step_branchIf_execution_uniform memory hooks floats allocator platform index view code exec store raw inst compiled ambient f rest depth after
      C targets next output hi slots last hf hc program point expected machine)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,pc,g,pending,fresh,simulation,uniform,ownership,bounded⟩ := effect
    exact ⟨success,sameStore,samePlatform,⟨pc.val,pending,_,fresh,simulation,uniform,ownership,rfl,bounded⟩⟩
  | ifElse bt yes no =>
    apply WP.spec_mono (step_if_execution_uniform memory hooks floats allocator platform index view code exec store raw inst compiled ambient f rest bt yes no after
      C targets next output hi slots last hf hc program point expected machine)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,pc,g,pending,fresh,simulation,uniform,ownership,bounded⟩ := effect
    exact ⟨success,sameStore,samePlatform,⟨pc.val,pending,_,fresh,simulation,uniform,ownership,rfl,bounded⟩⟩
theorem step_ordinary_advance {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : OrdinaryOpcode) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      Advance view code store out.2.1 expected compiled.code.length raw.pc.val false initial ⦄ := by
  apply WP.spec_mono (step_ordinary_advance_uniform memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest op after last hf hi hc program slots point expected machine)
  rintro out ⟨success,same,platform,advance⟩
  exact ⟨success,same,platform,advance.forget⟩

end Exec.Interp.StructuredMachine
