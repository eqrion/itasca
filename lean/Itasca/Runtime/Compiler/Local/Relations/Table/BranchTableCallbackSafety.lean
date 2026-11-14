import Itasca.Runtime.Compiler.Local.Lowering.Control.TableBranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchTableCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSkipSafety
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableMetadata
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableSafetyEffects
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericSafety

/-!
Normal return of br_table compilation, from one target through the target loop and lowering to the compiler callback.
-/

/-! ## Branch Table Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_table_branch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (index frameIndex : Usize) (depth : U32) (frame : runtime.compiler.Frame)
    (depthAt : compiler.table_depths.val[index.val]? = some depth)
    (frameAt : compiler.frames.val[frameIndex.val]? = some frame)
    (position : frameIndex.val + depth.val + 1 = compiler.frames.val.length)
    (tableFits : compiler.function.jump_tables.val.length < Usize.max)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.table_branch ops compiler index ⦃ _ => True ⦄ := by
  apply runtime.compiler.control.FunctionCompiler.table_branch.total ops law compiler index depth depthAt tableFits
  intro budget table
  exact compiler_branch_skip_total ops law
    {compiler with budget, function := {compiler.function with jump_tables := table}}
    frame frameIndex depth 1#u32 frameAt position fixupsFit codeFits sourceFits coordinateFits

@[step] theorem compiler_table_label_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (fits : compiler.table_depths.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops compiler state depth ⦃ _ => True ⦄ := by
  exact runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.total ops law compiler state depth fits

end Itasca.Runtime.Compiler

end

/-! ## Branch Table Loop Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_table_loop_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (limit : Nat) (limitFits : limit ≤ Usize.max)
    (held : status = .Ok () → TableLoopSafe compiler index.val limit) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches_loop ops compiler index status ⦃ _ => True ⦄ := by
  apply runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.spec ops
    (fun current index status => status = .Ok () → TableLoopSafe current index limit) (fun _ => True)
    ?_ ?_ compiler index status held
  · intro current i safe inside
    have held := safe rfl
    let depth := current.table_depths.val[i.val]
    have depthAt : current.table_depths.val[i.val]? = some depth := List.getElem?_eq_getElem inside
    have depthBound := held.depths depth (List.mem_of_getElem? depthAt)
    let frameIndex := Usize.ofNatCore (current.frames.val.length - depth.val - 1)
      (by have h := (alloc.vec.Vec.len current.frames).hBounds; change current.frames.val.length < 2^UScalarTy.Usize.numBits at h; omega)
    have frameBound : frameIndex.val < current.frames.val.length := by
      change current.frames.val.length - depth.val - 1 < current.frames.val.length
      omega
    let frame := current.frames.val[frameIndex.val]
    have frameAt : current.frames.val[frameIndex.val]? = some frame := List.getElem?_eq_getElem frameBound
    have position : frameIndex.val + depth.val + 1 = current.frames.val.length := by
      change current.frames.val.length - depth.val - 1 + depth.val + 1 = current.frames.val.length
      omega
    have room := held.room
    have codeFits : current.function.code.val.length + 2 ≤ Usize.max := by omega
    have sourceFits : current.function.source_offsets.val.length + 2 ≤ Usize.max := by
      rw [held.aligned]; exact codeFits
    have tableFits : current.function.jump_tables.val.length < Usize.max := by
      have := held.tables; omega
    obtain ⟨⟨result,next⟩,called,_⟩ := WP.spec_imp_exists
      (compiler_table_branch_total ops law current i frameIndex depth frame depthAt frameAt position
        tableFits (held.fixups.lookup frameAt (by omega)) codeFits sourceFits held.coordinate)
    apply WP.exists_imp_spec ⟨(result, next), called, ?_⟩
    intro accepted
    change result = .Ok () at accepted
    rw [accepted] at called
    exact held.advance ops law inside called
  · intro current index status safe finished
    trivial

end Itasca.Runtime.Compiler

end

/-! ## Branch Table Lower Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_lower_table_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (aligned : SourceAligned compiler)
    (depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (room : compiler.function.code.val.length + 1 + 2*compiler.table_depths.val.length ≤ Usize.max)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches ops compiler ⦃ _ => True ⦄ := by
  apply runtime.compiler.control.FunctionCompiler.lower_table_branches.total ops law compiler
    (by omega) (by rw [aligned]; omega) coordinate
  intro start length selector emitted effect
  obtain ⟨budget,code,sources,rfl,codeEq,sourcesEq⟩ := effect.emitted
  have size : code.val.length = compiler.function.code.val.length+1 := by
    simp only [codeEq, List.length_append, List.length_singleton]
  have sourceSize : sources.val.length = compiler.function.source_offsets.val.length+1 := by
    have := congrArg List.length sourcesEq
    simpa only [List.length_map,List.length_append,List.length_singleton] using this
  let next := {compiler with budget,function := {compiler.function with code,source_offsets := sources}}
  have safe : TableLoopSafe next 0 Usize.max := by
    refine ⟨?_,depths,fixups.mono (by dsimp [next]; omega),?_,?_,coordinate⟩
    · change sources.val.length = code.val.length
      rw [sourceSize,size,aligned]
    · change code.val.length + 2*(compiler.table_depths.val.length-0) ≤ Usize.max
      simpa only [size,Nat.sub_zero] using room
    · change compiler.function.jump_tables.val.length ≤ code.val.length
      omega
  exact compiler_table_loop_total ops law next 0#usize (.Ok ()) Usize.max (Nat.le_refl _) (fun _ => safe)

end Itasca.Runtime.Compiler

end

/-! ## Branch Table Callback Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_br_table_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (aligned : SourceAligned compiler)
    (depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length)
    (fallbackBound : fallback.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (room : compiler.function.code.val.length + 1 + 2*(compiler.table_depths.val.length+1) ≤ Usize.max)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops compiler state fallback types ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  have normal : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops compiler state fallback = .ok (.Ok (), labeled) →
      labeled.reachable = true → runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled ⦃ _ => True ⦄ := by
    intro labeled labelCall live
    obtain ⟨budget, labels, rfl, labelsEq⟩ := compiler_table_label_success ops law compiler labeled state fallback labelCall
    exact compiler_lower_table_total ops law {compiler with budget, table_depths := labels}
      aligned (by
        intro depth member
        rw [labelsEq] at member
        rcases List.mem_append.mp member with member | member
        · exact depths depth member
        · simp only [List.mem_singleton] at member
          subst depth
          exact fallbackBound)
      fixups (by simpa only [labelsEq, List.length_append, List.length_singleton] using room)
      tables coordinate
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.total ops law compiler state fallback types (by omega) normal)
  rw [called, WP.spec_ok]
  intro accepted
  change status = .Ok () at accepted
  subst status
  obtain ⟨middle, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv
    ops compiler after state fallback types (.Ok ()) called).observation
  have stack := compiler_observe_stack ops law middle state
  rw [observed, WP.spec_ok] at stack
  exact stack rfl

end Itasca.Runtime.Compiler

end
