import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeWasm2
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant

/-!
Sections, each formerly its own module: EnterStacks, Boundary, BranchInfo, BranchEffects, ScopeZipper, ScopeFronts, Reachability.
-/

/-! ## EnterStacks -/

section

/-!
Live Wasm 2 entry exposes the full physical prefix below its block parameters and condition.

Main declarations: `Wasm2.ReaderEnterPost.stacks`. A direct consumer is `Compiler.Body.Reader.Control.KnownFrontEntry`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Live Wasm 2 entry exposes the full physical prefix below its block parameters and condition. -/
theorem _root_.Itasca.Wasm2.ReaderEnterPost.stacks {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderEnterPost p out form bt ins outs remaining base)
    (initial : form.Initial) (live : p.current.ctrl.polymorphic_base = false)
    (known : ConcreteStack st.core.vals.val) :
    ∃ front : List valtype,
      Sequence.stackTypes st.core.vals.val = front ++ form.args ins ∧
      Sequence.stackTypes out.core.vals.val = front ++ ins.map Translate.valueType ∧
      ConcreteStack out.core.vals.val := by
  obtain ⟨C, outer, spine, header, position, typed, controls, blocks, old⟩ := id p.opened
  have old' : st.core.vals.val = p.parents.flatMap Wasm2.Frames.Saved.vals ++ p.current.vals := by
    simpa only [wasm2_spine_values spine] using old
  have knownParts := concrete_stack_append.mp (old' ▸ known)
  have transfer := post.popped
  rw [live] at transfer
  have remainingKnown := concrete_stack_transfer knownParts.2 transfer
  have before := realized_concrete_types knownParts.2 (transfer _ (Sequence.realizes_default false remaining))
  obtain ⟨C', outer', spine', header', position', typed', controls', blocks', new⟩ := post.opened
  have params : form.params ins = ins := by rcases initial with rfl | rfl | rfl <;> rfl
  have new' : out.core.vals.val = p.parents.flatMap Wasm2.Frames.Saved.vals ++ remaining ++ ins.map code.StackType.Val := by
    simpa [wasm2_spine_values spine', Wasm2.Frames.Saved.fresh, params, List.flatMap_append] using new
  refine ⟨Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals) ++ Sequence.stackTypes remaining, ?_, ?_, ?_⟩
  · simp only [old', Sequence.stackTypes, List.map_append] at before ⊢
    simpa [List.append_assoc, Sequence.stackTypes] using
      congrArg (Sequence.stackTypes (p.parents.flatMap Wasm2.Frames.Saved.vals) ++ ·) before.symm
  · simp [new', Sequence.stackTypes, List.map_map, Function.comp_def]
  · rw [new']
    exact concrete_stack_append.mpr ⟨concrete_stack_append.mpr ⟨knownParts.1, remainingKnown⟩,
      (concrete_stack_iff _).mpr ⟨ins, rfl⟩⟩

end Itasca.Runtime.Compiler

end

/-! ## Boundary -/

section

/-!
The pending reader boundary between source scopes and compiler state.

Main declarations: `ReaderBoundaryWasm2` and `ReaderBoundaryWasm2.pending`. A direct consumer is `Compiler.Body.Reader.Control.BoundaryInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

structure ReaderBoundaryWasm2 (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (st : code.BodyState) (parents : List Wasm2.Frames.Saved) (current : Wasm2.Frames.Saved) : Prop where
  signature : env.types.val[index.val]? = some ft
  bounds : Wasm2.Bounds data st
  opened : Wasm2.Frames.Open env (Wasm2.bodyContext env locals ft) st parents current
  bodyType : Wasm2.Frames.bodyType parents current = some (.TypeIndex index)
  consumed : Wasm2.Consumed data 0#usize (Wasm2.Frames.trace parents current) st.core.pos
  declared : Wasm2.TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val))
    (Wasm2.Frames.trace parents current)

def ReaderBoundaryWasm2.pending {data env locals index ft st parents current}
    (boundary : ReaderBoundaryWasm2 data env locals index ft st parents current)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length) :
    Wasm2.Pending data env locals index {core := {st.core with pos := next}} :=
  ⟨st.core.pos, ft, parents, current, boundary.signature, boundary.bounds.size, boundary.opened.with_pos next,
    boundary.bodyType, boundary.consumed, boundary.declared, inbounds, advance, boundary.bounds.ctrls⟩

theorem _root_.Itasca.Wasm2.ReaderPost.boundary {data env locals index st out instruction poly values}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderPost p out instruction poly values)
    (declared : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction) :
    ReaderBoundaryWasm2 data env locals index p.ft {core := out} p.parents
      (p.current.advance (.plain instruction) instruction poly values) := by
  refine ⟨p.signature, post.after.1.bounds, post.opened, ?_, ?_, ?_⟩
  · simpa only [Wasm2.Frames.bodyType_advance] using p.bodyType
  · have consumed := Wasm2.Consumed.snoc p.consumed post.encoded
    simpa [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.advance, List.append_assoc] using consumed
  · have trace : Wasm2.Frames.trace p.parents (p.current.advance (.plain instruction) instruction poly values) =
        Wasm2.Frames.trace p.parents p.current ++ [.plain instruction] := by
      simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.advance, List.append_assoc]
    rw [trace, Wasm2.tokensDeclared_append, Wasm2.tokensDeclared_singleton]
    exact ⟨p.declared, declared⟩

end Itasca.Runtime.Compiler

end

/-! ## BranchInfo -/

section

/-!
Branch stack processing cannot change the label metadata produced by its actual reader.

Main declarations: `reader_branch_info_label` and `reader_branch_info_selected`. A direct consumer is `Compiler.Body.Reader.Control.BranchEffects`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2
set_option maxHeartbeats 2000000

/-- Branch stack processing cannot change the label metadata produced by its actual reader. -/
theorem reader_branch_info_label (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (conditional : Bool) (depth : U32) (view : signature.ResultType)
    (out : code.BodyState)
    (accepted : code.branch_info st data env conditional = .ok (.Ok (depth, view), out)) :
    ∃ middle, code.read_label_info st data = .ok (.Ok (depth, view), middle) := by
  unfold code.branch_info at accepted
  obtain ⟨⟨result, middle⟩, read, accepted⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
  simp only [Std.uncurry] at accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨selected, label⟩ := pair
    have same : selected = depth ∧ label = view := by
      cases conditional <;> simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        repeat' first
          | (solve | simp at accepted | simpa using accepted)
          | (split at accepted <;> try simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              Std.uncurry, bind_ok] at accepted)
          | (obtain ⟨value, equation, accepted⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
             try simp only [core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               Std.uncurry, bind_ok] at accepted)
      all_goals simp_all
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨middle, read⟩

/-- A successful branch's actual callback depth selects exactly its reported label view. -/
theorem reader_branch_info_selected (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (conditional : Bool) (depth : U32) (view : signature.ResultType)
    (out : code.BodyState)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length)
    (accepted : code.branch_info st data env conditional = .ok (.Ok (depth, view), out)) :
    labelAt st depth.val = some view := by
  obtain ⟨middle, read⟩ := reader_branch_info_label st data env conditional depth view out accepted
  have erased : code.read_multi_value_label st data = .ok (.Ok view, middle) := by
    simp [code.read_multi_value_label, read, core.result.Result.Insts.CoreOpsTry.branch]
  have effect := code.read_multi_value_label.spec st data aligned
  rw [erased, WP.spec_ok] at effect
  obtain ⟨_, _, _, _, post⟩ := effect
  obtain ⟨selected, decoded, label⟩ := post view rfl
  dsimp only at decoded label
  have bytes := code.read_label_info.bytes st data aligned
  rw [read, WP.spec_ok] at bytes
  obtain ⟨rfl, _⟩ := Leb128.Decoded.deterministic data st.core.pos depth selected middle.core.pos middle.core.pos
    (bytes.2.2 depth view rfl) decoded
  exact label
end Itasca.Runtime.Compiler

end

/-! ## BranchEffects -/

section

/-!
Checked branch arguments form the exact source suffix of a live concrete stack.

Main declarations: `reader_br_arguments` and `reader_br_if_arguments`. A direct consumer is `Compiler.Body.Reader.Control.BranchLayout`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- Checked branch arguments form the exact source suffix of a live concrete stack. -/
theorem reader_br_arguments (st out : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (depth : U32) (view : signature.ResultType) (expected : List wasm_types.ValueType)
    (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (monomorphic : Control.polymorphic st.core = false) (known : ConcreteStack segment)
    (resolved : resolve env view = some expected)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length)
    (accepted : code.branch_info st data env false = .ok (.Ok (depth, view), out)) :
    ∃ front : List valtype, Sequence.stackTypes segment = front ++ expected.map Translate.valueType := by
  obtain ⟨middle, read⟩ := reader_branch_info_label st data env false depth view out accepted
  have readEffect := code.read_label_info.bytes st data aligned
  rw [read, WP.spec_ok] at readEffect
  obtain ⟨sameValues, controls, _⟩ := readEffect
  dsimp only at sameValues controls
  obtain ⟨⟨result, popped⟩, pop, _, _, rest, _, _, transfer⟩ := WP.spec_imp_exists
    (code.pop_results.realizes middle.core env view expected outer segment resolved
      (by simpa [sameValues] using values) (by simpa [Control.base, controls] using base))
  dsimp only at transfer
  cases result with
  | Err error => simp [code.branch_info, read, pop, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok unit =>
    cases unit
    have poly : Control.polymorphic middle.core = false := by simpa [Control.polymorphic, controls] using monomorphic
    rw [poly] at transfer
    exact ⟨Sequence.stackTypes rest, (realized_concrete_types known (transfer rfl _ (Sequence.realizes_default false rest))).symm⟩

/-- Conditional branches consume exactly the condition and retain the checked target arguments. -/
theorem reader_br_if_arguments (st out : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (depth : U32) (view : signature.ResultType) (expected : List wasm_types.ValueType)
    (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (monomorphic : Control.polymorphic st.core = false) (known : ConcreteStack segment)
    (resolved : resolve env view = some expected)
    (aligned : st.blocks.val.length = st.core.ctrls.val.length)
    (accepted : code.branch_info st data env true = .ok (.Ok (depth, view), out)) :
    ∃ rest : List code.StackType, segment = rest ++ [.Val .I32] ∧
      out.core.vals.val = outer ++ rest ∧
      ∃ front : List valtype, Sequence.stackTypes rest = front ++ expected.map Translate.valueType := by
  obtain ⟨middle, read⟩ := reader_branch_info_label st data env true depth view out accepted
  have readEffect := code.read_label_info.bytes st data aligned
  rw [read, WP.spec_ok] at readEffect
  obtain ⟨sameValues, controls, _⟩ := readEffect
  dsimp only at sameValues controls
  have middleBase : (Control.base middle.core).val = outer.length := by simpa [Control.base, controls] using base
  have poly : Control.polymorphic middle.core = false := by simpa [Control.polymorphic, controls] using monomorphic
  obtain ⟨⟨conditionResult, conditionState⟩, popCondition, conditionControls, _, remaining, conditionValues, conditionEffect⟩ := WP.spec_imp_exists
    (code.pop_with_type.segment middle.core outer segment .I32 (by simpa [sameValues] using values) middleBase)
  dsimp only at conditionControls conditionValues conditionEffect
  cases conditionResult with
  | Err error => simp [code.branch_info, read, popCondition, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok raw =>
    rw [poly] at conditionEffect
    have segmentEq := typed_pop_exact known conditionEffect
    have remainingKnown : ConcreteStack remaining := (concrete_stack_append.mp (segmentEq ▸ known)).1
    obtain ⟨⟨argumentResult, argumentState⟩, popArguments, argumentControls, _, rest, argumentValues, _, transfer⟩ := WP.spec_imp_exists
      (code.pop_results.realizes conditionState env view expected outer remaining resolved conditionValues
        (by simpa [Control.base, conditionControls] using middleBase))
    dsimp only at argumentControls argumentValues transfer
    cases argumentResult with
    | Err error => simp [code.branch_info, read, popCondition, popArguments, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok unit =>
      cases unit
      have argumentPoly : Control.polymorphic conditionState = false := by
        simpa [Control.polymorphic, conditionControls] using poly
      rw [argumentPoly] at transfer
      have interpreted := realized_concrete_types remainingKnown (transfer rfl _ (Sequence.realizes_default false rest))
      have restKnown := concrete_stack_transfer remainingKnown (transfer rfl)
      obtain ⟨remainingTypes, remainingEq⟩ := (concrete_stack_iff remaining).mp remainingKnown
      obtain ⟨restTypes, restEq⟩ := (concrete_stack_iff rest).mp restKnown
      have rawTypes : remainingTypes = restTypes ++ expected := by
        apply List.map_injective_iff.mpr Translate.valueType_injective
        simpa [remainingEq, restEq, Sequence.stackTypes, List.map_append, List.map_map,
          Function.comp_def] using interpreted.symm
      have remainingShape : remaining = rest ++ expected.map code.StackType.Val := by
        simp [remainingEq, rawTypes, restEq]
      have capacity : argumentState.vals.val.length + expected.length ≤ Usize.max := by
        have bound : st.core.vals.val.length ≤ Usize.max := by scalar_tac
        simp only [argumentValues, values, segmentEq, remainingShape, List.length_append,
          List.length_map, List.length_singleton] at *
        omega
      obtain ⟨⟨pushResult, final⟩, push, pushOk, finalValues, _, _⟩ := WP.spec_imp_exists
        (code.push_results.spec argumentState env view expected resolved capacity)
      cases pushResult with
      | Err error => contradiction
      | Ok unit =>
        simp [code.branch_info, read, popCondition, popArguments, push,
          core.result.Result.Insts.CoreOpsTry.branch] at accepted
        subst out
        refine ⟨remaining, segmentEq, ?_, Sequence.stackTypes rest, interpreted.symm⟩
        simpa [argumentValues, remainingShape, List.append_assoc] using finalValues
end Itasca.Runtime.Compiler

end

/-! ## ScopeZipper -/

section

/-!
Compiler source scopes and the canonical validator zipper retain the same source syntax.

Main declarations: `ReaderScopeZipperWasm2`. A direct consumer is `Compiler.Body.Reader.Control.ElseExitSlots`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

private theorem matched_at {α β : Type} {R : α → β → Prop} {left right}
    (same : List.Forall₂ R left right) (index : Nat) (value : β)
    (found : right[index]? = some value) : ∃ item, left[index]? = some item ∧ R item value := by
  induction same generalizing index with
  | nil => simp at found
  | @cons a b left right head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst value; exact ⟨a, rfl, head⟩
    | succ index => exact ih index (by simpa using found)

private theorem matched_last {α β : Type} {R : α → β → Prop} {left right value}
    (same : List.Forall₂ R left (right ++ [value])) :
    ∃ beginning item, left = beginning ++ [item] ∧ List.Forall₂ R beginning right ∧ R item value := by
  have beginning := List.forall₂_take_append left right [value] same
  have ending := List.forall₂_drop_append left right [value] same
  have singleton : ∀ {items : List α}, List.Forall₂ R items [value] → ∃ item, items = [item] ∧ R item value := by
    intro items related
    cases related with
    | cons head tail => cases tail; exact ⟨_, rfl, head⟩
  obtain ⟨item, rest, related⟩ := singleton ending
  exact ⟨left.take right.length, item, by rw [← rest, List.take_append_drop], beginning, related⟩

/-- Compiler source scopes and the canonical validator zipper retain the same source syntax. -/
structure ReaderScopeZipperWasm2 (parents : List SourceScope) (current : SourceScope)
    (savedParents : List Wasm2.Frames.Saved) (savedCurrent : Wasm2.Frames.Saved) : Prop where
  parents : List.Forall₂ SourceScopeMatchesWasm2 parents savedParents
  current : SourceScopeMatchesWasm2 current savedCurrent

theorem ReaderScopeZipperWasm2.advance {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (token : Wasm2.Token) (instruction : instr) (poly : Bool) (values : List code.StackType) :
    ReaderScopeZipperWasm2 parents (current.advance instruction) savedParents
      (savedCurrent.advance token instruction poly values) :=
  ⟨same.parents, (SourceScopeMatchesWasm2.advance_iff _ _ _ _).mpr same.current⟩

theorem ReaderScopeZipperWasm2.enter {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (child : SourceScope) (savedChild : Wasm2.Frames.Saved)
    (fresh : SourceScopeMatchesWasm2 child savedChild) (remaining : List code.StackType) :
    ReaderScopeZipperWasm2 (parents ++ [current]) child
      (savedParents ++ [{savedCurrent with vals := remaining}]) savedChild :=
  ⟨List.rel_append same.parents (.cons (same.current.suspend remaining) .nil), fresh⟩

theorem ReaderScopeZipperWasm2.begin_else {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (type : blocktype) (condition : U32) (form : current.form = .then_ type condition)
    (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderScopeZipperWasm2 parents (current.begin_else type condition yesExit noEntry normal)
      savedParents savedCurrent.nextElse :=
  ⟨same.parents, same.current.begin_else type condition form yesExit noEntry normal⟩

theorem ReaderScopeZipperWasm2.lookup {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (depth : Nat) (saved : Wasm2.Frames.Saved)
    (found : (savedCurrent :: savedParents.reverse)[depth]? = some saved) :
    ∃ scope, (current :: parents.reverse)[depth]? = some scope ∧ SourceScopeMatchesWasm2 scope saved :=
  matched_at (.cons same.current (List.rel_reverse same.parents)) depth saved found

theorem ReaderScopeZipperWasm2.close {parents current savedParents savedCurrent}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (grandparents : List Wasm2.Frames.Saved) (parent : Wasm2.Frames.Saved)
    (split : savedParents = grandparents ++ [parent]) (instruction : instr) :
    ∃ outer scope, parents = outer ++ [scope] ∧
      ReaderScopeZipperWasm2 outer (scope.advance instruction) grandparents
        (Wasm2.resumedSource parent savedCurrent instruction) := by
  obtain ⟨outer, scope, shape, paired, last⟩ := matched_last (split ▸ same.parents)
  exact ⟨outer, scope, shape, paired, last.resume⟩

/-- Actual Wasm 2 label lookup selects the paired compiler source scope and its full type list. -/
theorem ReaderScopeZipperWasm2.label {parents current savedParents savedCurrent env root st}
    (same : ReaderScopeZipperWasm2 parents current savedParents savedCurrent)
    (opened : Wasm2.Frames.Open env root st savedParents savedCurrent)
    (depth : Nat) (view : signature.ResultType)
    (selected : Wasm2.labelAt st depth = some view) :
    ∃ scope types, (current :: parents.reverse)[depth]? = some scope ∧
      Wasm2.resolve env view = some types ∧ scope.branchTypes = types.map Translate.valueType := by
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, values⟩ := id opened
  have bound : depth < (savedCurrent :: savedParents.reverse).length := by
    by_contra outside
    have outside' : ¬depth < st.core.ctrls.val.length := by simpa [controls] using outside
    simp [Wasm2.labelAt, outside'] at selected
  have found := List.getElem?_eq_getElem bound
  obtain ⟨scope, scopeFound, matchScope⟩ := same.lookup depth _ found
  have label := opened.labels depth
  rw [selected] at label
  simp only [Wasm2.Frames.labels, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.getElem?_map, found, Option.map_some,
    Option.bind_some] at label
  cases resolved : Wasm2.resolve env view with
  | none => simp [resolved] at label
  | some types =>
    simp only [resolved, Option.map_some, Option.some.injEq, list.mk_list.injEq] at label
    exact ⟨scope, types, scopeFound, rfl, matchScope.branch_types.trans label.symm⟩

end Itasca.Runtime.Compiler

end

/-! ## ScopeFronts -/

section

/-!
Saved operand segments determine the exact source prefix below every open scope. Compiler slot heights alone cannot recover these source types.

Main declarations: `SourceFronts` and `ReaderScopeFronts`. A direct consumer is `Compiler.Body.Reader.Control.BranchLayout`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Saved operand segments determine the exact source prefix below every open
scope. Compiler slot heights alone cannot recover these source types. -/
inductive SourceFronts : List SourceScope → List (List code.StackType) → List code.StackType → Prop where
  | root : SourceFronts [] [] []
  | push {parents values front} (prior : SourceFronts parents values front)
      (scope : SourceScope) (segment : List code.StackType)
      (same : scope.front = Sequence.stackTypes front) :
      SourceFronts (parents ++ [scope]) (values ++ [segment]) (front ++ segment)

theorem SourceFronts.flatten {parents values front} (fronts : SourceFronts parents values front) :
    front = values.flatten := by
  induction fronts with
  | root => rfl
  | push prior scope segment same ih => simp [List.flatten_append, ih]

structure ReaderScopeFronts (parents : List SourceScope) (current : SourceScope)
    (values : List (List code.StackType)) : Prop where
  prior : SourceFronts parents values values.flatten
  current : current.front = Sequence.stackTypes values.flatten

theorem ReaderScopeFronts.initial (returns : List valtype) :
    ReaderScopeFronts [] (SourceScope.initial returns) [] := ⟨.root, rfl⟩

theorem ReaderScopeFronts.advance {parents current values} (fronts : ReaderScopeFronts parents current values)
    (instruction : instr) : ReaderScopeFronts parents (current.advance instruction) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderScopeFronts.begin_else {parents current values} (fronts : ReaderScopeFronts parents current values)
    (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderScopeFronts parents (current.begin_else bt condition yesExit noEntry normal) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderScopeFronts.push {parents current values} (fronts : ReaderScopeFronts parents current values)
    (child : SourceScope) (remaining : List code.StackType)
    (front : child.front = Sequence.stackTypes (values.flatten ++ remaining)) :
    ReaderScopeFronts (parents ++ [current]) child (values ++ [remaining]) := by
  refine ⟨?_, ?_⟩
  · simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using
      fronts.prior.push current remaining fronts.current
  · simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using front

theorem SourceFronts.pop {parents parent values segment front}
    (fronts : SourceFronts (parents ++ [parent]) (values ++ [segment]) front) :
    SourceFronts parents values values.flatten ∧ parent.front = Sequence.stackTypes values.flatten := by
  generalize scopesEq : parents ++ [parent] = allScopes at fronts
  generalize valuesEq : values ++ [segment] = allValues at fronts
  cases fronts with
  | root => simp at scopesEq
  | @push oldScopes oldValues previous prior scope actualSegment same =>
    have ss : parents = oldScopes ∧ parent = scope := by simpa using scopesEq
    have vs : values = oldValues ∧ segment = actualSegment := by simpa using valuesEq
    obtain ⟨rfl, rfl⟩ := ss
    obtain ⟨rfl, rfl⟩ := vs
    exact ⟨prior.flatten ▸ prior, by simpa only [prior.flatten] using same⟩

theorem ReaderScopeFronts.pop {parents parent current values segment}
    (fronts : ReaderScopeFronts (parents ++ [parent]) current (values ++ [segment]))
    (instruction : instr) : ReaderScopeFronts parents (parent.advance instruction) values := by
  obtain ⟨prior, same⟩ := fronts.prior.pop
  exact ⟨prior, same⟩

theorem SourceFronts.prefix {parents values front} (fronts : SourceFronts parents values front)
    (scope : SourceScope) (member : scope ∈ parents) :
    ∃ rest, Sequence.stackTypes front = scope.front ++ rest := by
  induction fronts with
  | root => simp at member
  | @push parents values front prior current segment same ih =>
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with previous | rfl
    · obtain ⟨rest, eq⟩ := ih previous
      exact ⟨rest ++ Sequence.stackTypes segment, by
        simp only [Sequence.stackTypes, List.map_append] at *
        simpa only [Sequence.stackTypes, List.append_assoc] using congrArg (fun xs => xs ++ Sequence.stackTypes segment) eq⟩
    · exact ⟨Sequence.stackTypes segment, by simp [Sequence.stackTypes, same]⟩

theorem ReaderScopeFronts.selected {parents current values}
    (fronts : ReaderScopeFronts parents current values) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope) :
    ∃ rest, current.front = scope.front ++ rest := by
  have member := List.mem_of_getElem? selected
  simp only [List.mem_cons, List.mem_reverse] at member
  rcases member with rfl | member
  · exact ⟨[], by simp⟩
  · obtain ⟨rest, eq⟩ := fronts.prior.prefix scope member
    exact ⟨rest, fronts.current.trans eq⟩

theorem ReaderScopeFronts.branch {parents current values}
    (fronts : ReaderScopeFronts parents current values) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope)
    (raw : List code.StackType) (front : List valtype)
    (arguments : Sequence.stackTypes raw = front ++ scope.branchTypes) :
    ∃ discarded, Sequence.stackTypes (values.flatten ++ raw) =
      scope.front ++ discarded ++ scope.branchTypes := by
  obtain ⟨outer, prefixEq⟩ := fronts.selected depth scope selected
  refine ⟨outer ++ front, ?_⟩
  have whole : Sequence.stackTypes (values.flatten ++ raw) =
      current.front ++ Sequence.stackTypes raw := by
    simpa only [Sequence.stackTypes, List.map_append] using
      congrArg (fun xs => xs ++ Sequence.stackTypes raw) fronts.current.symm
  rw [whole, prefixEq, arguments]
  simp only [List.append_assoc]

end Itasca.Runtime.Compiler

end

/-! ## Reachability -/

section

/-!
Every entered child was opened from a monomorphic suspended source parent. This retains the fact needed when END later restores that parent's stack.

Main declarations: `ReaderParentReachability` and `ReaderReachability`. A direct consumer is `Compiler.Body.Reader.Control.BlockDormantPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Every entered child was opened from a monomorphic suspended source parent.
This retains the fact needed when END later restores that parent's stack. -/
inductive ReaderParentReachability {Saved : Type} (poly : Saved → Bool) :
    List SourceScope → SourceScope → List Saved → Prop
  | root (current : SourceScope) : ReaderParentReachability poly [] current []
  | push {parents parent savedParents} (outer : ReaderParentReachability poly parents parent savedParents)
      (savedParent : Saved) (child : SourceScope)
      (entered : child.entered = true → poly savedParent = false) :
      ReaderParentReachability poly (parents ++ [parent]) child (savedParents ++ [savedParent])

theorem ReaderParentReachability.change_current {Saved : Type} {poly : Saved → Bool}
    {parents current savedParents} (chain : ReaderParentReachability poly parents current savedParents)
    (next : SourceScope) (entered : next.entered = current.entered) :
    ReaderParentReachability poly parents next savedParents := by
  cases chain with
  | root => exact .root next
  | push outer savedParent child mono => exact .push outer savedParent next (by simpa [entered] using mono)

theorem ReaderParentReachability.pop {Saved : Type} {poly : Saved → Bool}
    {parents parent child savedParents savedParent}
    (chain : ReaderParentReachability poly (parents ++ [parent]) child (savedParents ++ [savedParent])) :
    ReaderParentReachability poly parents parent savedParents ∧
      (child.entered = true → poly savedParent = false) := by
  generalize sourceEq : parents ++ [parent] = allParents at chain
  generalize savedEq : savedParents ++ [savedParent] = allSaved at chain
  cases chain with
  | root => simp at sourceEq
  | @push outerParents outerParent outerSaved outer stored current entered =>
    have source : parents = outerParents ∧ parent = outerParent := by simpa using sourceEq
    have saved : savedParents = outerSaved ∧ savedParent = stored := by simpa using savedEq
    rcases source with ⟨rfl, rfl⟩
    rcases saved with ⟨rfl, rfl⟩
    exact ⟨outer, entered⟩

/-- Compiler liveness implies a monomorphic active validator frame. The reverse
implication is unnecessary: END can restore a monomorphic dead continuation. -/
structure ReaderReachability {Saved : Type} (poly : Saved → Bool) (reachable : Bool)
    (parents : List SourceScope) (current : SourceScope) (savedParents : List Saved)
    (savedCurrent : Saved) : Prop where
  parents : ReaderParentReachability poly parents current savedParents
  current : reachable = true → poly savedCurrent = false

theorem ReaderReachability.initial {Saved : Type} (poly : Saved → Bool)
    (reachable : Bool) (current : SourceScope) (saved : Saved) (mono : poly saved = false) :
    ReaderReachability poly reachable [] current [] saved := ⟨.root current, fun _ => mono⟩

theorem ReaderReachability.change_current {Saved : Type} {poly : Saved → Bool}
    {reachable parents current savedParents savedCurrent}
    (state : ReaderReachability poly reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (next : SourceScope) (nextSaved : Saved)
    (entered : next.entered = current.entered)
    (mono : nextReachable = true → poly nextSaved = false) :
    ReaderReachability poly nextReachable parents next savedParents nextSaved :=
  ⟨state.parents.change_current next entered, mono⟩

theorem ReaderReachability.push {Saved : Type} {poly : Saved → Bool}
    {reachable parents current savedParents savedCurrent}
    (state : ReaderReachability poly reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (child : SourceScope) (suspended savedChild : Saved)
    (suspendedPoly : poly suspended = poly savedCurrent)
    (entered : child.entered = true → reachable = true)
    (mono : nextReachable = true → poly savedChild = false) :
    ReaderReachability poly nextReachable (parents ++ [current]) child
      (savedParents ++ [suspended]) savedChild := by
  refine ⟨.push state.parents suspended child ?_, mono⟩
  intro live
  rw [suspendedPoly]
  exact state.current (entered live)

theorem ReaderReachability.pop {Saved : Type} {poly : Saved → Bool}
    {reachable parents parent child savedParents savedParent savedCurrent}
    (state : ReaderReachability poly reachable (parents ++ [parent]) child
      (savedParents ++ [savedParent]) savedCurrent)
    (nextReachable : Bool) (instruction : instr) (resumed : Saved)
    (resumedPoly : poly resumed = poly savedParent)
    (entered : nextReachable = true → child.entered = true) :
    ReaderReachability poly nextReachable parents (parent.advance instruction) savedParents resumed := by
  obtain ⟨outer, parentMono⟩ := state.parents.pop
  refine ⟨outer.change_current _ rfl, ?_⟩
  intro live
  rw [resumedPoly]
  exact parentMono (entered live)

abbrev ReaderReachabilityWasm2 := ReaderReachability (fun saved : Wasm2.Frames.Saved => saved.ctrl.polymorphic_base)
end Itasca.Runtime.Compiler

end
