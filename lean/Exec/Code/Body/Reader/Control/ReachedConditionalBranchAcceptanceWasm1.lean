import Exec.Code.Local.Capacity.ReaderAcceptance
import Exec.Code.Body.Reader.Control.ReaderBranchWasm1
import Exec.Code.Body.Reader.Table.StructuredReaderBranchLayoutWithTables
import Exec.Code.Local.Capacity.ConditionalBranchAvailability
import Exec.Code.Body.Control.Table.StructuredBranchIfLayoutWithTables
import Exec.Code.Body.Reader.Control.ReaderBranchIfLayout
import Exec.Code.Local.Callbacks.Common.FixupBudget

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Independently accepted conditional source branching selects the retained compiler
frame and proves its argument width. Allocation and instruction room then
establish actual callback acceptance for every depth and label kind. -/
theorem reached_reader_br_if_available_wasm1 {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (capacity : CallbackCapacity compiler out bound 3)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR_IF)
    (reference : code.step source st data env ctx code.OP_BR_IF before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_IF compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 3 else 0) ⦄ := by
  rw [OpDispatch.dispatch_br_if] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_br_if st data)
    (fun v state arg => source.on_br_if v state arg.1 (Control.resultView arg.2))
    (fun v state arg => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br_if
      v state arg.1 (Control.resultView arg.2)) before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 3 else 0)) reference ?_
  rintro ⟨depth,view⟩ read _
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler out depth (Control.resultView view) ⦃ _ ⦄
  by_cases live : compiler.reachable = true
  · obtain ⟨scope,discarded,selected,input,targetStack,_⟩ := reader_br_if_layout_wasm1 p same fronts (invariant.known live)
      (monomorphic live) depth view out read
    obtain ⟨frameIndex,frame,sourceAt,condition,found,position,shape,_,_,width,conditionAt,_⟩ :=
      invariant.branch_if_coordinates live depth.val scope selected discarded input targetStack
    have holes := fixups frame (List.mem_of_getElem? found)
    have codeCapacity := capacity.codeCapacity
    have reserve := capacity.codeReserve
    simp only [alloc.vec.Vec.length] at codeCapacity reserve
    have widthFits : (match frame.kind with | .Loop => frame.params | _ => frame.results).val+1 ≤ compiler.height.val := by
      calc
        _ = slots scope.branchTypes+1 := congrArg (fun n => n+1) shape.toScopeFrameShape.branch_width
        _ ≤ compiler.height.val := by omega
    exact compiler_on_br_if_available ops law bound available compiler out capacity frame frameIndex depth condition (Control.resultView view)
      (fun _ => found) (fun _ => position) (fun _ => widthFits) (fun _ => conditionAt)
      (by change frame.fixups.val.length < Usize.max; omega)
      (by change frame.fixups.val.length+1 ≤ bound; omega)
  · obtain ⟨prior,frame,frames,_,_⟩ := invariant.frames.split
    have member : frame ∈ compiler.frames.val := by rw [frames]; simp
    have holes := fixups frame member
    have codeCapacity := capacity.codeCapacity
    have reserve := capacity.codeReserve
    simp only [alloc.vec.Vec.length] at codeCapacity reserve
    exact compiler_on_br_if_available ops law bound available compiler out capacity frame 0#usize depth 0#u32 (Control.resultView view)
      (fun impossible => False.elim (live impossible)) (fun impossible => False.elim (live impossible))
      (fun impossible => False.elim (live impossible)) (fun impossible => False.elim (live impossible))
      (by change frame.fixups.val.length < Usize.max; omega)
      (by change frame.fixups.val.length+1 ≤ bound; omega)

end Exec.Code
