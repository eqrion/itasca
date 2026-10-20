import Exec.Code.Body.Reader.Acceptance.BodyReaderAcceptance
import Exec.Code.Local.Capacity.ReaderAcceptance
import Exec.Code.Local.Capacity.EndDispatchAvailability
import Exec.Code.Body.Control.Table.StructuredPrefixDeadWithTables

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Retained scope ownership discharges every end-callback patch and map
lookup, including root epilogues, guarded blocks, and dead scopes. -/
theorem StructuredCompilerPrefixWithTables.end_available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {jumpTables emit initial compiler types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefixWithTables jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (capacity : CallbackCapacity compiler state bound 1)
    (coordinate : compiler.function.body_start.val+state.pos.val ≤ Usize.max)
    (kind : code.LabelKind) (bt : signature.BlockType) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state kind bt ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by
    have size := compiler.frames.property
    simp only [frames,List.length_append,List.length_singleton] at size
    omega
  let rest := alloc.vec.Vec.from prior priorBound
  have rootNoGuard : frame.kind = .Body → frame.if_pc = none := by
    intro root
    have form : current.form = .body := by
      have same := shape.kind
      cases found : current.form <;> simp_all [ScopeForm.kind]
    have guard := shape.guard
    simpa [form,SourceScope.guardPosition] using guard
  have sites := invariant.mode.sites frame (by rw [frames]; simp)
  exact compiler_end_available ops bound available compiler state capacity frame rest
    (by simpa [rest] using frames) rootNoGuard sites.guard sites.branches.branches shape.mapBound coordinate

/-- Replay the independently accepted Wasm 2 end reader through the complete
callback, retaining its exact source state and instruction allowance. -/
theorem reached_profile_end_available_wasm2 {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {jumpTables emit initial compiler types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefixWithTables jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (source : code.OpVisitor V) (before after : V) (st out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (capacity : CallbackCapacity compiler out.core bound 1)
    (coordinate : compiler.function.body_start.val+out.core.pos.val ≤ Usize.max)
    (reference : code.step_profile source st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 11#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [Wasm2.CallbackTrace.dispatch_end] at reference ⊢
  refine Wasm2.CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  rintro ⟨kind,bt⟩ _ _
  exact invariant.end_available ops bound available out.core capacity coordinate kind bt

/-- Wasm 1 end dispatch uses the same retained-scope acceptance proof. -/
theorem reached_reader_end_available_wasm1 {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {jumpTables emit initial compiler types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefixWithTables jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (source : code.OpVisitor V) (before after : V) (st out : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (capacity : CallbackCapacity compiler out bound 1)
    (coordinate : compiler.function.body_start.val+out.pos.val ≤ Usize.max)
    (reference : code.step source st data env ctx code.OP_END before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_END compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  rw [OpDispatch.dispatch_end] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_end st)
    (fun v state arg => source.on_end v state arg.1 (Control.signature arg.2))
    (fun v state arg => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_end v state arg.1
      (Control.signature arg.2)) before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  rintro ⟨kind,bt⟩ _ _
  exact invariant.end_available ops bound available out capacity coordinate kind (Control.signature bt)

end Exec.Code
