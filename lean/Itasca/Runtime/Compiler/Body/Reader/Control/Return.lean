import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Wasm2.Control.Return

/-!
Sections, each formerly its own module: KnownFronts, KnownFrontEntry, ReachabilitySteps, Return.
-/

/-! ## KnownFronts -/

section

/-!
Entered scopes retain concrete saved operands even when the current unreachable segment later contains polymorphic stack entries.

Main declarations: `ScopeConcreteFronts` and `ReaderKnownFronts`. A direct consumer is `Compiler.Body.Reader.Control.ElseEnteredPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Entered scopes retain concrete saved operands even when the current
unreachable segment later contains polymorphic stack entries. -/
inductive ScopeConcreteFronts : List SourceScope → List (List code.StackType) → Prop where
  | root : ScopeConcreteFronts [] []
  | push {parents values} (prior : ScopeConcreteFronts parents values)
      (scope : SourceScope) (segment : List code.StackType)
      (known : scope.entered = true → ConcreteStack values.flatten) :
      ScopeConcreteFronts (parents ++ [scope]) (values ++ [segment])

structure ReaderKnownFronts (parents : List SourceScope) (current : SourceScope)
    (values : List (List code.StackType)) : Prop where
  prior : ScopeConcreteFronts parents values
  current : current.entered = true → ConcreteStack values.flatten

theorem ReaderKnownFronts.initial (returns : List valtype) :
    ReaderKnownFronts [] (SourceScope.initial returns) [] := by
  exact ⟨.root, fun _ => by simp [ConcreteStack]⟩

theorem ReaderKnownFronts.advance {parents current values}
    (fronts : ReaderKnownFronts parents current values) (instruction : instr) :
    ReaderKnownFronts parents (current.advance instruction) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderKnownFronts.begin_else {parents current values}
    (fronts : ReaderKnownFronts parents current values)
    (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderKnownFronts parents (current.begin_else bt condition yesExit noEntry normal) values :=
  ⟨fronts.prior, fronts.current⟩

theorem ReaderKnownFronts.push {parents current values}
    (fronts : ReaderKnownFronts parents current values) (child : SourceScope)
    (remaining : List code.StackType)
    (known : child.entered = true → ConcreteStack (values.flatten ++ remaining)) :
    ReaderKnownFronts (parents ++ [current]) child (values ++ [remaining]) := by
  refine ⟨fronts.prior.push current remaining fronts.current, ?_⟩
  simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using known

theorem ScopeConcreteFronts.pop {parents parent values segment}
    (fronts : ScopeConcreteFronts (parents ++ [parent]) (values ++ [segment])) :
    ScopeConcreteFronts parents values ∧ (parent.entered = true → ConcreteStack values.flatten) := by
  generalize scopesEq : parents ++ [parent] = allScopes at fronts
  generalize valuesEq : values ++ [segment] = allValues at fronts
  cases fronts with
  | root => simp at scopesEq
  | @push oldScopes oldValues prior scope actualSegment known =>
    have ss : parents = oldScopes ∧ parent = scope := by simpa using scopesEq
    have vs : values = oldValues ∧ segment = actualSegment := by simpa using valuesEq
    obtain ⟨rfl, rfl⟩ := ss
    obtain ⟨rfl, rfl⟩ := vs
    exact ⟨prior, known⟩

theorem ReaderKnownFronts.pop {parents parent current values segment}
    (fronts : ReaderKnownFronts (parents ++ [parent]) current (values ++ [segment]))
    (instruction : instr) : ReaderKnownFronts parents (parent.advance instruction) values := by
  obtain ⟨prior, known⟩ := fronts.prior.pop
  exact ⟨prior, known⟩
end Itasca.Runtime.Compiler

end

/-! ## KnownFrontEntry -/

section

/-!
Known operand fronts when entering a reader scope.

Main declarations: `Wasm2.ReaderEnterPost.known_fronts`. A direct consumer is `Compiler.Body.Reader.Control.EnterCompilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Wasm2.ReaderEnterPost.known_fronts {data env locals index st out form bt ins outs remaining base}
    {p : Wasm2.Pending data env locals index st}
    (post : Wasm2.ReaderEnterPost p out form bt ins outs remaining base)
    {parents current} (fronts : ReaderKnownFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (child : SourceScope)
    (live : child.entered = true → p.current.ctrl.polymorphic_base = false)
    (known : child.entered = true → ConcreteStack st.core.vals.val) :
    ReaderKnownFronts (parents ++ [current]) child
      ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.vals) := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  apply fronts.push child remaining
  intro entered
  obtain ⟨C, outer, spine, header, position, typed, controls, blocks, old⟩ := id p.opened
  have old' : st.core.vals.val = (p.parents.map Wasm2.Frames.Saved.vals).flatten ++ p.current.vals := by
    simpa only [wasm2_spine_values spine, List.flatMap_def] using old
  have knownParts := concrete_stack_append.mp (old' ▸ known entered)
  have transfer := post.popped
  rw [live entered] at transfer
  exact concrete_stack_append.mpr ⟨knownParts.1, concrete_stack_transfer knownParts.2 transfer⟩
end Itasca.Runtime.Compiler

end

/-! ## ReachabilitySteps -/

section

/-!
Reader scope initialization and reachability preservation through advance, else and closure.
-/

/-! ## Reader Scope Initial -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderScopeZipperWasm2.initial (bt : signature.BlockType) (base : Usize)
    (ins outs : List wasm_types.ValueType) :
    ReaderScopeZipperWasm2 [] (SourceScope.initial (outs.map Translate.valueType)) []
      (Wasm2.Frames.Saved.fresh base .body bt ins outs) := by
  refine ⟨.nil, ?_⟩
  constructor
  · exact .body
  · rfl
  · rfl
  · rfl
end Itasca.Runtime.Compiler

end

/-! ## Reader Reachability Steps -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderReachabilityWasm2.advance {reachable parents current savedParents savedCurrent}
    (invariant : ReaderReachabilityWasm2 reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (token : Wasm2.Token) (instruction : instr) (poly : Bool)
    (values : List code.StackType) (mono : nextReachable = true → poly = false) :
    ReaderReachabilityWasm2 nextReachable parents (current.advance instruction) savedParents
      (savedCurrent.advance token instruction poly values) :=
  invariant.change_current nextReachable _ _ rfl mono

theorem ReaderReachabilityWasm2.begin_else {reachable parents current savedParents savedCurrent}
    (invariant : ReaderReachabilityWasm2 reachable parents current savedParents savedCurrent)
    (nextReachable : Bool) (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    ReaderReachabilityWasm2 nextReachable parents (current.begin_else bt condition yesExit noEntry normal)
      savedParents savedCurrent.nextElse :=
  invariant.change_current nextReachable _ _ rfl (fun _ => rfl)

theorem ReaderReachabilityWasm2.close {reachable parents parent child savedParents savedParent savedCurrent}
    (invariant : ReaderReachabilityWasm2 reachable (parents ++ [parent]) child
      (savedParents ++ [savedParent]) savedCurrent)
    (nextReachable : Bool) (instruction : instr)
    (entered : nextReachable = true → child.entered = true) :
    ReaderReachabilityWasm2 nextReachable parents (parent.advance instruction) savedParents
      (Wasm2.resumedSource savedParent savedCurrent instruction) :=
  invariant.pop nextReachable instruction _ rfl entered

end Itasca.Runtime.Compiler

end

end

/-! ## Return -/

section

/-!
The source effect of an accepted return reader step.

Main declarations: `reader_return_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.ControlEffects`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_return_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_profile visitor st data env ctx index 15#u8 before = .ok (.Ok (), out, after)) :
    visitor.on_return before out.core = .ok (.Ok (), after) ∧
      Wasm2.returnStep st env index = .ok (.Ok (), out) ∧
      out.core.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      Wasm2.ReaderPost p out.core .RETURN true [] := by
  rw [Wasm2.CallbackTrace.dispatch_return] at accepted
  obtain ⟨value, read, callback⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  cases value
  have effect := p.return_reader byte
  rw [read, WP.spec_ok] at effect
  exact ⟨callback, read, effect rfl⟩

end Itasca.Runtime.Compiler

end
