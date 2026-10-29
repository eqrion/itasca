import Itasca.Visitor.ReaderAcceptance
import Itasca.Visitor.ReachedTableLabels
import Itasca.Runtime.Compiler.Local.Capacity.BranchLabelAvailability
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallback
import Itasca.Runtime.Compiler.Local.Demand.RecordedDemand
import Itasca.Wasm2.Trace.TableBytes
import Itasca.Wasm2.Visitor.AcceptedTable
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableDecodePrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSafetyWasm2
import Itasca.Runtime.Compiler.Local.Capacity.BranchTableAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableBoundary
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableInputsWasm2
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredBranchIfLayout
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedCompilerLedger
import Itasca.Runtime.Compiler.Local.Capacity.BodyResourceRoom
import Itasca.Visitor.BodyReplay

/-!
Source-bounded br_table reader replay. Label-collection invariants, loop framing and callback availability establish successful compilation from the independent source demand.
-/

/-! ## Label Collection Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Collected labels change only scratch storage and budget counters. The
resource allowance is indexed by source labels, independent of emitted code. -/
def LabelCollectionPrefix {A : Type} (initial current : runtime.compiler.FunctionCompiler A)
    (count : Nat) : Prop :=
  ∃ budget depths, current = {initial with budget,table_depths := depths} ∧
    depths.length = initial.table_depths.length+count ∧
    CompilationBudgetEffect initial.budget budget (fun counter => if counter = .branches then count else 0)

theorem LabelCollectionPrefix.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    LabelCollectionPrefix compiler compiler 0 := by
  exact ⟨compiler.budget,compiler.table_depths,rfl,by omega,by
    simpa using CompilationBudgetEffect.refl compiler.budget⟩

/-- The actual next label accepts from the unconsumed portion of independently
bounded scratch and branch demand. All other compiler fields are retained. -/
theorem LabelCollectionPrefix.collect_available {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState) (depth : U32)
    (count total : Nat) (held : LabelCollectionPrefix initial compiler count) (remaining : count < total)
    (branches : initial.budget.branches.val+total ≤ initial.budget.limits.max_branch_table_entries.val)
    (capacity : initial.table_depths.length+total ≤ Usize.max)
    (reserve : initial.table_depths.length+total ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops compiler state depth ⦃ out =>
      out.1 = .Ok () ∧ LabelCollectionPrefix initial out.2 (count+1) ⦄ := by
  obtain ⟨budget,depths,frame,length,effect⟩ := held
  have used := (effect.counts .branches).2
  have limits := effect.limits
  have room : compiler.budget.branches.val < compiler.budget.limits.max_branch_table_entries.val := by
    rw [frame]
    simp only [ChargeCounter.used,ite_true] at used
    simp only
    rw [limits]
    omega
  have fits : compiler.table_depths.length < Usize.max := by rw [frame]; simp only; omega
  have request : compiler.table_depths.length+1 ≤ bound := by rw [frame]; simp only; omega
  obtain ⟨⟨reply,after⟩,called,accepted,growth,appended⟩ := WP.spec_imp_exists
    (compiler_branch_label_available ops bound available compiler state depth room fits request)
  dsimp only at accepted growth appended
  subst reply
  obtain ⟨nextBudget,nextDepths,nextFrame,nextValues⟩ := compiler_table_label_success ops law compiler after state depth called
  have counts : nextDepths.length = initial.table_depths.length+(count+1) := by
    have lengths := congrArg List.length nextValues
    simp only [List.length_append,List.length_singleton] at lengths
    change nextDepths.length = compiler.table_depths.length+1 at lengths
    rw [frame] at lengths
    simp only at lengths
    omega
  have nextEffect : CompilationBudgetEffect initial.budget nextBudget
      (fun counter => if counter = .branches then count+1 else 0) := by
    rw [nextFrame] at growth
    rw [frame] at growth
    exact (effect.trans growth).weaken (by intro counter; cases counter <;> simp)
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),after),called,rfl,nextBudget,nextDepths,?_,counts,nextEffect⟩
  rw [nextFrame,frame]

end Itasca.Runtime.Compiler

end

/-! ## Source Table Demand -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

private theorem table_suffix_final_observation {data start remaining observations result state}
    (trace : Wasm2.CallbackTrace.TableSuffix data start remaining observations result state) :
    result = .Ok () → ∃ prior action reply,
      observations = prior ++ [⟨.op state action,reply⟩] := by
  induction trace with
  | failed error labels count outcomes => intro impossible; cases impossible
  | complete labels length fallback outcomes =>
    intro _
    exact ⟨_,_,_,rfl⟩

/-- The independently accepted table loop records its final marked state.
A retained source body suffix therefore bounds that state by the independent
whole-body demand, without an accepted compiler callback premise. -/
theorem source_table_loop_demand
    (before after final : List Observation) (st : code.OpIterState) (out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (shape : Control.Shape st) (count : U32)
    (reference : code.branch_table_with_loop recorder st data env profile before count none .Empty 0#u32 =
      .ok (.Ok (),out,after))
    (tail : code.body_loop_loop recorder data env ctx index profile after out = .ok (.Ok (),final)) :
    out.core.vals.length ≤ (observationDemand final).operands ∧
    out.core.ctrls.length ≤ (observationDemand final).controls := by
  obtain ⟨observations,recorded,trace⟩ := Wasm2.CallbackTrace.table_loop_records recorder id recorder_records
    ⟨st⟩ data env profile shape (by simp) count 0#u32 none .Empty (by simp) before (.Ok ()) out after reference
  obtain ⟨suffix,retained⟩ := source_body_recorded_prefix after final out data env ctx index profile (.Ok ()) tail
  obtain ⟨prior,action,reply,events⟩ := table_suffix_final_observation trace rfl
  apply observationDemand.recorded_op (prior := before ++ prior) (suffix := suffix) (action := action) (reply := reply)
  dsimp only [id] at recorded
  simp only [retained,recorded,events,List.append_assoc,List.singleton_append]

end Itasca.Runtime.Compiler

end

/-! ## Table Label Collection Replay -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Replay all actual Wasm 2 vector labels with independent scratch and branch
bounds. The remaining final-callback obligation receives the exact decoded
source list, not an arbitrary scratch buffer or an assumed target success. -/
theorem compiler_table_loop_collect_available {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.OpIterState) (out : code.BodyState)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count : U32) (all : List U32)
    (empty : compiler.table_depths.val = []) (length : all.length = count.val+1)
    (decoded : BrTable.LabelsDecoded data st.pos all out.core.pos)
    (branches : compiler.budget.branches.val+count.val ≤ compiler.budget.limits.max_branch_table_entries.val)
    (capacity : count.val ≤ Usize.max) (reserve : count.val ≤ bound)
    (post : code.BodyState → V → runtime.compiler.FunctionCompiler A → Prop)
    (finish : ∀ (state : code.BodyState) current marked depth ts sourceBefore sourceAfter,
      LabelCollectionPrefix compiler current count.val →
      TableDecodeRead data all out.core.pos count.val state.core current.table_depths.val depth →
      state.core.vals = st.vals → state.core.ctrls = st.ctrls →
      code.mark_unreachable state.core = .ok marked →
      source.on_br_table sourceBefore marked depth ts = .ok (.Ok (),sourceAfter) →
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br_table current marked depth ts
        ⦃ result => result.1 = .Ok () ∧ post {state with core := marked} sourceAfter result.2 ⦄)
    (reference : code.branch_table_with_loop source st data env profile before count none .Empty 0#u32 =
      .ok (.Ok (),out,after)) :
    code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env profile compiler count none .Empty 0#u32 ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        post out after result.2.2 ⦄ := by
  let related := fun index state (_ : V) current =>
    LabelCollectionPrefix compiler current index ∧
      TableDecodePrefix data all out.core.pos index state current.table_depths.val ∧
      state.vals = st.vals ∧ state.ctrls = st.ctrls
  let readRelated := fun index state depth (_ : signature.ResultType) (_ : V) current =>
    LabelCollectionPrefix compiler current index ∧
      TableDecodeRead data all out.core.pos index state current.table_depths.val depth ∧
      state.vals = st.vals ∧ state.ctrls = st.ctrls
  have readMoves : ∀ (index : U32) (state : code.BodyState) sourceBefore current depth ts next,
      index.val ≤ count.val → related index.val state.core sourceBefore current →
      code.read_label_info state data = .ok (.Ok (depth,ts),next) →
      readRelated index.val next.core depth ts sourceBefore current := by
    intro index state sourceBefore current depth ts next bounded held read
    have actual := reader_table_label_wasm2 state data (by simp)
    rw [read,WP.spec_ok] at actual
    obtain ⟨values,controls,_,_⟩ := actual depth ts rfl
    exact ⟨held.1,held.2.1.read (by omega) read,values.trans held.2.2.1,controls.trans held.2.2.2⟩
  have label : ∀ (index : U32) state sourceBefore current depth ts sourceAfter,
      index.val < count.val → readRelated index.val state depth ts sourceBefore current →
      source.on_br_table_label sourceBefore state depth = .ok (.Ok (),sourceAfter) →
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_br_table_label current state depth
        ⦃ result => result.1 = .Ok () ∧ related (index.val+1) state sourceAfter result.2 ⦄ := by
    intro index state sourceBefore current depth ts sourceAfter remaining held _
    obtain ⟨⟨reply,targetAfter⟩,called,accepted,collected⟩ := WP.spec_imp_exists
      (held.1.collect_available ops law bound allocation compiler current state depth index.val count.val
        remaining (by simpa [empty] using branches) (by simpa [empty] using capacity) (by simpa [empty] using reserve))
    dsimp only at accepted collected
    subst reply
    obtain ⟨budget,depths,frame,appended⟩ := compiler_table_label_success ops law current targetAfter state depth called
    have decodedPrefix := held.2.1.collect
    apply WP.exists_imp_spec
    refine ⟨(.Ok (),targetAfter),called,rfl,collected,?_,held.2.2⟩
    simpa only [frame,appended] using decodedPrefix
  obtain ⟨targetAfter,called,retained⟩ := Wasm2.Visitor.table_loop_reader_accepted_replay source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) related readRelated post data env profile count
    readMoves label (fun state sourceBefore current marked depth ts sourceAfter held mark call =>
      finish state current marked depth ts sourceBefore sourceAfter held.1 held.2.1 held.2.2.1 held.2.2.2 mark call)
    0#u32 (by simp) none .Empty st out before after compiler
    ⟨LabelCollectionPrefix.initial compiler,by simpa [empty] using TableDecodePrefix.initial st decoded,rfl,rfl⟩ reference
  apply WP.exists_imp_spec
  exact ⟨(.Ok (),out,targetAfter),called,rfl,rfl,retained⟩

end Itasca.Runtime.Compiler

end

/-! ## Table Source Frame -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Independent source table loops retain operands and controls until their
single final unreachable transformation. This describes the source reader,
without any compiler-success or target callback assumption. -/
theorem source_table_loop_frame {V : Type} (source : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count index : U32)
    (arity : Option Usize) (first : signature.ResultType)
    (st : code.OpIterState) (out : code.BodyState) (before after : V)
    (bounded : index.val ≤ count.val)
    (reference : code.branch_table_with_loop source st data env profile before count arity first index =
      .ok (.Ok (),out,after)) :
    ∃ last, last.vals = st.vals ∧ last.ctrls = st.ctrls ∧ code.mark_unreachable last = .ok out.core := by
  let related := fun (_ : Nat) (state : code.OpIterState) (left right : V) =>
    state.vals = st.vals ∧ state.ctrls = st.ctrls ∧ left = right
  let readRelated := fun (_ : Nat) (state : code.OpIterState) (_ : U32) (_ : signature.ResultType) (left right : V) =>
    state.vals = st.vals ∧ state.ctrls = st.ctrls ∧ left = right
  let post := fun (final : code.BodyState) (_ _ : V) =>
    ∃ last, last.vals = st.vals ∧ last.ctrls = st.ctrls ∧ code.mark_unreachable last = .ok final.core
  have readMoves : ∀ (i : U32) (state : code.BodyState) left right depth ts next,
      i.val ≤ count.val → related i.val state.core left right →
      code.read_label_info state data = .ok (.Ok (depth,ts),next) →
      readRelated i.val next.core depth ts left right := by
    intro i state left right depth ts next _ held read
    have actual := reader_table_label_wasm2 state data (by simp)
    rw [read,WP.spec_ok] at actual
    obtain ⟨values,controls,_,_⟩ := actual depth ts rfl
    exact ⟨values.trans held.1,controls.trans held.2.1,held.2.2⟩
  obtain ⟨targetAfter,_,retained⟩ := Wasm2.Visitor.table_loop_reader_accepted_replay source source related readRelated post
    data env profile count readMoves
    (by
      intro i state left right depth ts next _ held called
      obtain ⟨values,controls,rfl⟩ := held
      rw [called,WP.spec_ok]
      exact ⟨rfl,values,controls,rfl⟩)
    (by
      intro state left right marked depth ts next held mark called
      obtain ⟨values,controls,rfl⟩ := held
      rw [called,WP.spec_ok]
      exact ⟨rfl,state.core,values,controls,mark⟩)
    index bounded arity first st out before after before ⟨rfl,rfl,rfl⟩ reference
  exact retained

/-- Source frame preservation and the independently decoded final cursor fix
the final marked state uniquely, including unreachable operand truncation. -/
theorem source_table_loop_marked {V : Type} (source : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count index : U32)
    (arity : Option Usize) (first : signature.ResultType)
    (st : code.OpIterState) (out : code.BodyState) (before after : V)
    (bounded : index.val ≤ count.val) (shape : Control.Shape st)
    (reference : code.branch_table_with_loop source st data env profile before count arity first index =
      .ok (.Ok (),out,after))
    (state marked : code.OpIterState) (values : state.vals = st.vals) (controls : state.ctrls = st.ctrls)
    (position : state.pos = out.core.pos) (mark : code.mark_unreachable state = .ok marked) :
    marked = out.core := by
  obtain ⟨last,lastValues,lastControls,lastMark⟩ := source_table_loop_frame source data env profile count index arity first
    st out before after bounded reference
  have lastShape : Control.Shape last :=
    ⟨by simpa only [lastControls] using shape.ordered,
      by simpa only [lastControls,lastValues] using shape.bounded⟩
  have lastSpec := code.mark_unreachable_total last lastShape
  rw [lastMark,WP.spec_ok] at lastSpec
  have sameValues := values.trans lastValues.symm
  have sameControls := controls.trans lastControls.symm
  have samePosition := position.trans lastSpec.2.2.1
  have same : state = last := by
    cases state
    cases last
    simp_all only [code.OpIterState.mk.injEq]
  rw [same,lastMark] at mark
  simpa only [Result.ok.injEq] using mark.symm

end Itasca.Runtime.Compiler

end

/-! ## Table Loop Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- The full actual Wasm 2 table loop accepts an independent source run.
All streamed label callbacks and the final lowering callback are constructed
from source target geometry, exact decoding, and numeric resource bounds. -/
theorem compiler_table_reader_loop_available {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st : code.OpIterState) (out : code.BodyState)
    (data : Slice U8) (env : module.Env) (count : U32) (all : List U32)
    (shape : Control.Shape st) (empty : compiler.table_depths.val = []) (length : all.length = count.val+1)
    (decoded : BrTable.LabelsDecoded data st.pos all out.core.pos)
    (capacity : CallbackCapacity compiler out.core bound (2*(count.val+1)+1))
    (branches : compiler.budget.branches.val+(count.val+1) ≤ compiler.budget.limits.max_branch_table_entries.val)
    (scratchCapacity : count.val+1 ≤ Usize.max) (scratchReserve : count.val+1 ≤ bound)
    (depthCount : count.val+1 ≤ U32.max)
    (aligned : compiler.reachable = true → SourceAligned compiler)
    (depthsValid : compiler.reachable = true → ∀ depth ∈ all, depth.val < compiler.frames.val.length)
    (widths : compiler.reachable = true → ∀ depth ∈ all,
      ∀ (index : Usize) (frame : runtime.compiler.Frame), compiler.frames.val[index.val]? = some frame →
        index.val+depth.val+1 = compiler.frames.val.length → (frameBranchWidth frame).val+1 ≤ compiler.height.val)
    (fixups : compiler.reachable = true → FixupBudget compiler.frames.val compiler.function.code.val.length)
    (tables : compiler.reachable = true → compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (selector : U32)
    (selectorAt : compiler.reachable = true → compiler.before.val[compiler.before.val.length-1]? = some selector)
    (reference : code.branch_table_with_loop source st data env .Wasm2 before count none .Empty 0#u32 =
      .ok (.Ok (),out,after)) :
    code.branch_table_with_loop (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 compiler count none .Empty 0#u32 ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => match counter with
            | .instructions => 2*(count.val+1)+1 | .branches => count.val+1 | _ => 0) ⦄ := by
  refine compiler_table_loop_collect_available ops law bound allocation source before after compiler st out data env
    .Wasm2 count all empty length decoded (by omega) (by omega) (by omega)
    (fun _ _ targetAfter => CompilationBudgetEffect compiler.budget targetAfter.budget
      (fun counter => match counter with
        | .instructions => 2*(count.val+1)+1 | .branches => count.val+1 | _ => 0)) ?_ reference
  intro state current marked depth ts sourceBefore sourceAfter collected read values controls mark _
  have markedEq := source_table_loop_marked source data env .Wasm2 count 0#u32 none .Empty st out before after (by simp)
    shape reference state.core marked values controls (read.cursor length) mark
  subst marked
  have whole := read.complete length
  have depthLength := read.length
  obtain ⟨budget,depths,frame,_,effect⟩ := collected
  have unchangedInstructions := effect.uncharged .instructions (by simp)
  change budget.instructions = compiler.budget.instructions at unchangedInstructions
  have sameLimits := effect.limits
  have capacityCurrent : CallbackCapacity current out.core bound (2*(count.val+1)+1) := by
    rw [frame]
    refine ⟨capacity.pc,capacity.codeCapacity,capacity.sourceCapacity,capacity.codeReserve,capacity.sourceReserve,
      capacity.coordinate,?_,capacity.operands,capacity.slots⟩
    change budget.instructions.val+(2*(count.val+1)+1) ≤ budget.limits.max_instructions.val
    rw [unchangedInstructions,sameLimits]
    exact capacity.instructions
  have branchRoom : current.budget.branches.val < current.budget.limits.max_branch_table_entries.val := by
    have used := (effect.counts .branches).2
    simp only [ChargeCounter.used,ite_true] at used
    rw [frame]
    simp only
    rw [sameLimits]
    omega
  have callback := compiler_on_br_table_available ops law bound allocation current out.core depth ts selector
    (by simpa only [depthLength] using capacityCurrent) branchRoom
    (by change current.table_depths.val.length < Usize.max; omega)
    (by change current.table_depths.val.length+1 ≤ bound; omega)
    (by omega)
    (by simpa only [SourceAligned,frame] using aligned)
    (by intro live depth member
        rw [← whole] at member
        simpa only [frame] using depthsValid (by simpa only [frame] using live) depth member)
    (by intro live depth member
        rw [← whole] at member
        simpa only [frame] using widths (by simpa only [frame] using live) depth member)
    (by simpa only [frame] using fixups)
    (by simpa only [frame] using tables)
    (by simpa only [frame] using selectorAt)
  apply WP.spec_mono callback
  intro result held
  refine ⟨held.1,?_⟩
  have bufferLength : depths.val.length = count.val := by simpa only [frame] using depthLength
  have lowerEffect := held.2
  rw [frame] at lowerEffect
  exact (effect.trans lowerEffect).weaken (by intro counter; cases counter <;> simp [bufferLength])

end Itasca.Runtime.Compiler

end

/-! ## Reached Table Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Full Wasm 2 table reading accepts from independent source validation,
retained frame/operand geometry, and explicit numeric resource bounds. Both
live and dead tables include every label and the separately decoded fallback. -/
theorem reached_profile_br_table_available_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (depths : List U32) (fallback : U32)
    (encoded : BrTable.Decoded data st.core.pos depths fallback out.core.pos)
    (capacity : CallbackCapacity compiler out.core bound (2*(depths.length+1)+1))
    (branches : compiler.budget.branches.val+(depths.length+1) ≤ compiler.budget.limits.max_branch_table_entries.val)
    (scratchCapacity : depths.length+1 ≤ Usize.max) (scratchReserve : depths.length+1 ≤ bound)
    (depthCount : depths.length+1 ≤ U32.max)
    (boundary : CompilerTableBoundary compiler)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (reference : code.step_profile source st data env ctx index .Wasm2 14#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 14#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => match counter with
            | .instructions => 2*(depths.length+1)+1 | .branches => depths.length+1 | _ => 0) ⦄ := by
  rw [Wasm2.CallbackTrace.dispatch_br_table] at reference ⊢
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  obtain ⟨count,first,selectorType,popped,all,arity,countDecoded,popCall,popControls,popPos,
    countEq,allDecoded,targets⟩ := reader_table_targets_wasm2 source before after st out data env
      _ p.current.ctrl controls p.opened.shape.core reference
  obtain ⟨sourceCount,sourceFirst,last,countSource,lengthSource,labelsSource,defaultSource⟩ := encoded
  obtain ⟨rfl,rfl⟩ := countDecoded.unique countSource
  have allEq : all = depths++[fallback] := (allDecoded.unique (labelsSource.snoc defaultSource)
    (by simp only [List.length_append,List.length_singleton]; omega)).1
  have geometry : ∃ selector : U32,
      (compiler.reachable = true → compiler.before.val[compiler.before.val.length-1]? = some selector) ∧
      (compiler.reachable = true → ∀ depth ∈ all, depth.val < compiler.frames.val.length) ∧
      (compiler.reachable = true → ∀ depth ∈ all,
        ∀ (frameIndex : Usize) (frame : runtime.compiler.Frame), compiler.frames.val[frameIndex.val]? = some frame →
          frameIndex.val+depth.val+1 = compiler.frames.val.length →
          (frameBranchWidth frame).val+1 ≤ compiler.height.val) := by
    by_cases live : compiler.reachable = true
    · have encoded : BrTable.Decoded data st.core.pos depths fallback out.core.pos :=
        ⟨count,first,last,countSource,lengthSource,labelsSource,defaultSource⟩
      obtain ⟨stack,stackEq,inputs⟩ := reader_table_inputs_wasm2 source p same fronts invariant.entryChain
        (invariant.live live).1 (invariant.known live) (monomorphic live) before after out depths fallback
        out.core.pos encoded reference
      have layout := (invariant.live live).2.layout
      rw [stackEq] at layout
      obtain ⟨selector,selectorAt,_⟩ := layout.condition
      refine ⟨selector,fun _ => selectorAt,?_,?_⟩
      · intro _ depth member
        rw [allEq] at member
        obtain ⟨scope,discarded,selected,_,input⟩ := inputs depth member
        have selected' : (current :: parents.reverse)[depth.val]? = some scope := by
          simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using selected
        obtain ⟨frameIndex,frame,sourceAt,condition,found,position,_⟩ :=
          invariant.branch_if_coordinates live depth.val scope selected' discarded stackEq input
        omega
      · intro _ depth member frameIndex frame found position
        rw [allEq] at member
        obtain ⟨scope,discarded,selected,_,input⟩ := inputs depth member
        have selected' : (current :: parents.reverse)[depth.val]? = some scope := by
          simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using selected
        obtain ⟨actualIndex,actualFrame,sourceAt,condition,actualFound,actualPosition,shape,_,_,width,_⟩ :=
          invariant.branch_if_coordinates live depth.val scope selected' discarded stackEq input
        have sameIndex : frameIndex = actualIndex := UScalar.eq_of_val_eq (by omega)
        subst actualIndex
        rw [found] at actualFound
        have sameFrame := Option.some.inj actualFound
        subst actualFrame
        calc
          _ = slots scope.branchTypes+1 := congrArg (fun n => n+1) shape.toScopeFrameShape.branch_width
          _ ≤ compiler.height.val := by omega
    · exact ⟨0#u32,(fun impossible => False.elim (live impossible)),
        (fun impossible => False.elim (live impossible)),(fun impossible => False.elim (live impossible))⟩
  obtain ⟨selector,selectorAt,depthsValid,widths⟩ := geometry
  have poppedShape := code.pop_with_type.total {st.core with pos := first} .I32
    (show Control.Shape {st.core with pos := first} from ⟨p.opened.shape.core.ordered,p.opened.shape.core.bounded⟩)
  rw [popCall,WP.spec_ok] at poppedShape
  have readCount := reader.read_u32_leb.complete data st.core.pos count first countSource
  unfold code.branch_table_with at reference ⊢
  rw [readCount] at reference ⊢
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at reference ⊢
  rw [popCall] at reference ⊢
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at reference ⊢
  have accepted := compiler_table_reader_loop_available ops law bound allocation source before after compiler popped out
    data env count all poppedShape.1 boundary.depths countEq (by simpa only [popPos] using allDecoded)
    (by simpa only [lengthSource] using capacity) (by simpa only [lengthSource] using branches)
    (by omega) (by omega) (by omega) (fun _ => invariant.sources) depthsValid widths
    (fun _ => fixups) (fun _ => boundary.targets) selector selectorAt reference
  obtain ⟨⟨reply,resultOut,targetAfter⟩,called,ok,sameResult,effect⟩ := WP.spec_imp_exists accepted
  dsimp only at ok sameResult effect
  subst reply resultOut
  apply WP.exists_imp_spec
  refine ⟨(.Ok (),out,targetAfter),called,rfl,rfl,?_⟩
  exact effect.weaken (by intro counter; cases counter <;> simp [lengthSource])

end Itasca.Runtime.Compiler

end

/-! ## Source Bound Table Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- A full reached Wasm 2 branch table accepts from source-only demand.
The source reference supplies decoding and stack peaks; consumed bytes pay
all label charges, stubs, reserves, and arithmetic bounds internally. -/
theorem IndexedTableReaderCompilerPointWasm2.table_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (byte : data.val[st.core.pos.val] = 14#u8)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => bodyResourceRate counter * (out.core.pos.val-st.core.pos.val)) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  have raw := canonical
  rw [Wasm2.CallbackTrace.dispatch_br_table] at raw
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := pending.opened
  obtain ⟨count,first,selector,popped,all,arity,countDecoded,popCall,popControls,popPos,
    countEq,allDecoded,targets⟩ := reader_table_targets_wasm2 recorder before after _ out data env
      _ pending.current.ctrl controls pending.opened.shape.core raw
  obtain ⟨depths,fallback,last,allEq,labelsDecoded,fallbackDecoded⟩ := allDecoded.unsnoc (by
    intro empty
    simp only [empty,List.length_nil] at countEq
    omega)
  have lengthSource : depths.length = count.val := by
    rw [allEq,List.length_append,List.length_singleton] at countEq
    omega
  have encoded : BrTable.Decoded data next depths fallback out.core.pos :=
    ⟨count,first,last,countDecoded,lengthSource,labelsDecoded,fallbackDecoded⟩
  have poppedSpec := code.pop_with_type.total {st.core with pos := first} .I32
    (show Control.Shape {st.core with pos := first} from
      ⟨pending.opened.shape.core.ordered,pending.opened.shape.core.bounded⟩)
  rw [popCall,WP.spec_ok] at poppedSpec
  have readCount := reader.read_u32_leb.complete data next count first countDecoded
  have loopReference : code.branch_table_with_loop recorder popped data env .Wasm2 before count none .Empty 0#u32 =
      .ok (.Ok (),out,after) := by
    unfold code.branch_table_with at raw
    rw [readCount] at raw
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at raw
    rw [popCall] at raw
    simpa only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] using raw
  have operands := (source_table_loop_demand before after final popped out data env ⟨sourceLocals,ft.results⟩
    index .Wasm2 poppedSpec.1 count loopReference tail).1
  have countSpan := countDecoded.span
  change next.val < first.val ∧ first.val ≤ next.val+5 ∧ first.val ≤ data.length at countSpan
  have labelSpan := table_labels_length_span allDecoded
  have endBound := (allDecoded.span countSpan.2.2).2
  have spanPositive : st.core.pos.val < out.core.pos.val := by omega
  have remaining : st.core.pos.val+(out.core.pos.val-st.core.pos.val) ≤ data.length := by omega
  have instructionPaid : 2*(depths.length+1)+1 ≤ 3*(out.core.pos.val-st.core.pos.val) := by omega
  have branchPaid : depths.length+1 ≤ out.core.pos.val-st.core.pos.val := by omega
  have capacity := room.capacity budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor remaining instructionPaid out.core operands
  have branchRoom := budget.room .branches (room.counters .branches) remaining (amount := depths.length+1)
    (by simpa only [bodyResourceRate,Nat.one_mul] using branchPaid)
  change compiler.budget.branches.val+(depths.length+1) ≤ compiler.budget.limits.max_branch_table_entries.val at branchRoom
  have sourceSize := room.pc
  have reserve := room.temporary
  have words : U32.max ≤ Usize.max := by scalar_tac
  have accepted := reached_profile_br_table_available_wasm2 pending ops law bound allocation initial compiler recorder
    before after out ⟨sourceLocals,ft.results⟩ state.compiled state.sources state.fronts state.reach.current
    depths fallback encoded capacity branchRoom (by omega) (by omega) (by omega) point.tables ledger.fixups canonical
  rw [byte]
  apply WP.spec_mono accepted
  intro result held
  refine ⟨held.1,held.2.1,held.2.2.weaken ?_⟩
  intro counter
  cases counter <;> simp only [bodyResourceRate] <;> omega

end Itasca.Runtime.Compiler

end
