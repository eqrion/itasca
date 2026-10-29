import Itasca.Runtime.Compiler.Body.Reader.Acceptance.BodyAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.StructuredBranchLayout
import Itasca.Runtime.Compiler.Local.Capacity.BranchAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Independently accepted source branching selects the retained compiler
frame and proves its argument width. Allocation and instruction room then
establish actual callback acceptance for every depth and label kind. -/
theorem reached_profile_br_available_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Pending data env .Wasm2 sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Frames.Saved.vals))
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (capacity : CallbackCapacity compiler out.core bound 2)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (reference : code.step_profile source st data env ctx index .Wasm2 12#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 12#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 2 else 0) ⦄ := by
  rw [CallbackTrace.dispatch_br] at reference ⊢
  refine CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 2 else 0)) reference ?_
  rintro ⟨depth,view⟩ read _
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler out.core depth view ⦃ _ ⦄
  by_cases live : compiler.reachable = true
  · obtain ⟨scope,discarded,selected,input⟩ := reader_br_layout_wasm2 p same fronts (invariant.known live)
      (monomorphic live) depth view out read
    obtain ⟨frameIndex,frame,sourceAt,found,position,shape,_,_,width⟩ :=
      invariant.branch_layout live depth.val scope selected discarded input
    have holes := fixups frame (List.mem_of_getElem? found)
    have codeCapacity := capacity.codeCapacity
    have reserve := capacity.codeReserve
    simp only [alloc.vec.Vec.length] at codeCapacity reserve
    have widthFits : (match frame.kind with | .Loop => frame.params | _ => frame.results).val ≤ compiler.height.val := by
      calc
        _ = slots scope.branchTypes := shape.toScopeFrameShape.branch_width
        _ ≤ compiler.height.val := by omega
    exact compiler_on_br_available ops law bound available compiler out.core capacity frame frameIndex depth view
      (fun _ => found) (fun _ => position) (fun _ => widthFits)
      (by change frame.fixups.val.length < Usize.max; omega)
      (by change frame.fixups.val.length+1 ≤ bound; omega)
  · obtain ⟨prior,frame,frames,_,_⟩ := invariant.frames.split
    have member : frame ∈ compiler.frames.val := by rw [frames]; simp
    have holes := fixups frame member
    have codeCapacity := capacity.codeCapacity
    have reserve := capacity.codeReserve
    simp only [alloc.vec.Vec.length] at codeCapacity reserve
    exact compiler_on_br_available ops law bound available compiler out.core capacity frame 0#usize depth view
      (fun impossible => False.elim (live impossible)) (fun impossible => False.elim (live impossible))
      (fun impossible => False.elim (live impossible))
      (by change frame.fixups.val.length < Usize.max; omega)
      (by change frame.fixups.val.length+1 ≤ bound; omega)

end Itasca.Runtime.Code
