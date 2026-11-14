import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Runtime.Compiler.Local.Relations.Layout.CompileInv
import Itasca.Runtime.Representation.Values

/-!
Sections, each formerly its own module: Observe, Frame.
-/

/-! ## Observe -/

section

/-! The extracted compiler rebuilds operand offsets from the validator's current
stack before each callback. These proofs cover the allocation-aware loop, its
reset, and the resulting concrete slot-layout invariant. Allocation rejection
and checked height overflow remain explicit compiler errors. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca.ResultFacts

def observedOffsets (height : Nat) : List Itasca.code.StackType → List Nat
  | [] => []
  | ty :: rest => height :: observedOffsets (height + compilerStackWidth ty) rest

def observedHeight (height : Nat) : List Itasca.code.StackType → Nat
  | [] => height
  | ty :: rest => observedHeight (height + compilerStackWidth ty) rest

@[step] theorem observe_values_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (before : alloc.vec.Vec U32) (height : U32) (values : Slice Itasca.code.StackType)
    (i : Usize) (index : i.val ≤ values.val.length)
    (fits : before.val.length + (values.val.length - i.val) ≤ Usize.max) :
    runtime.compiler.observe_values_loop ops budget before height values i (.Ok ()) ⦃ out =>
      out.1 = .Ok () → out.2.1 = budget ∧
        out.2.2.1.val.map (fun word => word.val) =
          before.val.map (fun word => word.val) ++ observedOffsets height.val (values.val.drop i.val) ∧
        out.2.2.2.val = observedHeight height.val (values.val.drop i.val) ⦄ := by
  unfold runtime.compiler.observe_values_loop
  apply loop.spec_decr_nat (fun p => values.val.length - p.2.2.2.1.val)
    (fun p => p.2.2.2.1.val ≤ values.val.length ∧
      (p.2.2.2.2 = .Ok () → p.1 = budget ∧
        p.2.1.val.map (fun word => word.val) ++
          observedOffsets p.2.2.1.val (values.val.drop p.2.2.2.1.val) =
          before.val.map (fun word => word.val) ++ observedOffsets height.val (values.val.drop i.val) ∧
        observedHeight p.2.2.1.val (values.val.drop p.2.2.2.1.val) =
          observedHeight height.val (values.val.drop i.val) ∧
        p.2.1.val.length + (values.val.length - p.2.2.2.1.val) ≤ Usize.max))
  · rintro ⟨b, v, h, j, r⟩ ⟨hj, hinv⟩
    dsimp only at hj hinv
    unfold runtime.compiler.observe_values_loop.body
    dsimp only
    split
    · rename_i hmore
      have hlt : j.val < values.val.length := by scalar_tac
      cases r with
      | Err err => simp [core.result.Result.is_ok]
      | Ok value =>
        cases value
        obtain ⟨rfl, hoff, hheight, hcapacity⟩ := hinv rfl
        have hcap : v.val.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨ty, hty⟩
        step with observe_value ops law b v h ty hcap as ⟨result, b1, v1, h1, hp⟩
        step as ⟨j1, hj1⟩
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · intro success
          subst result
          obtain ⟨rfl, hv1, hh1⟩ := hp
          refine ⟨rfl, ?_, ?_, ?_⟩
          · rw [hv1, List.map_append, List.map_singleton, hj1, hh1, hty]
            rw [List.drop_eq_getElem_cons hlt] at hoff
            simpa [observedOffsets, List.append_assoc] using hoff
          · rw [hj1, hh1, hty]
            rw [List.drop_eq_getElem_cons hlt] at hheight
            simpa [observedHeight] using hheight
          · simp only [hv1, List.length_append, List.length_singleton]
            omega
        · scalar_tac
    · rename_i hstop
      have heq : j.val = values.val.length := by scalar_tac
      simp only [WP.spec_ok]
      intro success
      obtain ⟨hb, hoff, hheight, _⟩ := hinv success
      simpa [heq, observedOffsets, observedHeight] using And.intro hb (And.intro hoff hheight)
  · exact ⟨index, fun _ => ⟨rfl, rfl, rfl, fits⟩⟩

@[step] theorem observe_values {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (before : alloc.vec.Vec U32) (height : U32) (values : Slice Itasca.code.StackType)
    (fits : before.val.length + values.val.length ≤ Usize.max) :
    runtime.compiler.observe_values ops budget before height values ⦃ out =>
      out.1 = .Ok () → out.2.1 = budget ∧
        out.2.2.1.val.map (fun word => word.val) =
          before.val.map (fun word => word.val) ++ observedOffsets height.val values.val ∧
        out.2.2.2.val = observedHeight height.val values.val ⦄ := by
  simpa [runtime.compiler.observe_values] using
    observe_values_loop ops law budget before height values 0#usize (by simp) (by simpa using fits)

@[step] theorem compiler_observe {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      out.1 = .Ok () →
        out.2.before.val.map (fun word => word.val) =
          observedOffsets compiler.function.local_slots.val state.vals.val ∧
        out.2.height.val = observedHeight compiler.function.local_slots.val state.vals.val ∧
        out.2.function.locals = compiler.function.locals ∧
        out.2.function.local_slots = compiler.function.local_slots ∧
        out.2.local_offsets = compiler.local_offsets ∧
        out.2.reachable = compiler.reachable ∧
        out.2.function.code = compiler.function.code ∧
        out.2.function.source_offsets = compiler.function.source_offsets ∧
        out.2.next_source = state.pos ∧
        (out.2.reachable = true → out.2.height.val ≤ out.2.function.slot_count.val) ∧
        compiler.function.slot_count.val ≤ out.2.function.slot_count.val ∧
        out.2.frames = compiler.frames ∧ out.2.function.controls = compiler.function.controls ⦄ := by
  unfold runtime.compiler.FunctionCompiler.observe
  split <;> step*
  all_goals cases r <;> simp_all [core.cmp.impls.OrdU32.max, alloc.vec.Vec.deref]
  all_goals try exact fun e => ⟨e⟩
  split <;> simp_all
  scalar_tac

theorem observed_height_values (height : Nat) (types : List Itasca.wasm_types.ValueType) :
    observedHeight height (types.map Itasca.code.StackType.Val) =
      height + slots (types.map Itasca.Translate.valueType) := by
  induction types generalizing height with
  | nil => simp [observedHeight, slots]
  | cons ty rest ih => simp [observedHeight, compilerStackWidth, slots, ih, Nat.add_assoc]

theorem observed_offsets_values (height : Nat) (types : List Itasca.wasm_types.ValueType) :
    observedOffsets height (types.map Itasca.code.StackType.Val) =
      (List.range types.length).map (fun index =>
        height + offset (types.map Itasca.Translate.valueType) index) := by
  induction types generalizing height with
  | nil => simp [observedOffsets]
  | cons ty rest ih =>
    simp only [List.map_cons, List.length_cons, observedOffsets, compilerStackWidth,
      List.range_succ_eq_map, List.map_map, offset, List.take_zero, slots,
      Nat.add_zero, List.map_cons]
    rw [ih]
    congr 1
    apply List.map_congr_left
    intro index _
    simp [offset, List.take_succ_cons, slots, Nat.add_assoc]

@[step] theorem compiler_observe_layout {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (localSlots : compiler.function.local_slots.val = slots (compilerLocals compiler))
    (localOffsets : compiler.local_offsets.val.map (fun word => word.val) =
      (List.range (compilerLocals compiler).length).map (offset (compilerLocals compiler))) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      out.1 = .Ok () → CompilerLayout out.2 (types.map Itasca.Translate.valueType) ⦄ := by
  step with compiler_observe ops law compiler state as ⟨out, h⟩
  rename_i success
  obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := h success
  have hlocals : compilerLocals out.2 = compilerLocals compiler := by simp [compilerLocals, hl]
  refine ⟨?_, ?_, ?_, ?_, hcap⟩
  · simpa [hls, hlocals] using localSlots
  · simpa [hlo, hlocals] using localOffsets
  · rw [hoff, concrete, observed_offsets_values, localSlots]
    simp [stackOffsets, hlocals]
  · rw [hh, concrete, observed_height_values, localSlots, hlocals]

end Itasca.Runtime.Compiler

end

/-! ## Observe Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Observation of one scalar, reference, SIMD, or polymorphic-bottom value
accepts when its independently computed slot width and reserve request fit. -/
theorem observe_value_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (before : alloc.vec.Vec U32)
    (height : U32) (ty : Itasca.code.StackType)
    (fits : before.length < Usize.max) (request : before.length + 1 ≤ bound)
    (slotsFit : height.val + compilerStackWidth ty ≤ U32.max) :
    runtime.compiler.observe_value ops budget before height ty ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.1.val = before.val ++ [height] ∧
      out.2.2.2.val = height.val + compilerStackWidth ty ⦄ := by
  unfold runtime.compiler.observe_value
  step with budget_push_available ops bound available budget before height fits request
    as ⟨status,charged,values,accepted,same,appended⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  cases ty with
  | Bot =>
    simp only [runtime.compiler.stack_width, bind_ok]
    step as ⟨added,addSpec⟩
    cases added with
    | none => simp [compilerStackWidth] at slotsFit; scalar_tac
    | some next =>
      simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,compilerStackWidth,appended]
      scalar_tac
  | Val type =>
    simp only [runtime.compiler.stack_width]
    step with compiler_width type as ⟨width,widthEq⟩
    step as ⟨added,addSpec⟩
    cases added with
    | none =>
      simp only [compilerStackWidth] at slotsFit
      scalar_tac
    | some next =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
      exact ⟨trivial,trivial,appended,by simpa [compilerStackWidth,widthEq] using addSpec.2.1⟩

private theorem stack_width_le_two (ty : Itasca.code.StackType) : compilerStackWidth ty ≤ 2 := by
  cases ty with
  | Bot => decide
  | Val type => cases type <;> decide

/-- Rebuilding the remaining observed stack accepts under conservative
independent two-slots-per-value and one-entry-per-value bounds. This includes
polymorphic bottom values in unreachable code. -/
theorem observe_values_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (before : alloc.vec.Vec U32) (height : U32)
    (values : Slice Itasca.code.StackType) (index : Usize)
    (inside : index.val ≤ values.val.length)
    (capacity : before.length + (values.val.length-index.val) ≤ Usize.max)
    (request : before.length + (values.val.length-index.val) ≤ bound)
    (slotsFit : height.val + 2*(values.val.length-index.val) ≤ U32.max) :
    runtime.compiler.observe_values_loop ops budget before height values index (.Ok ()) ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧
      out.2.2.1.length = before.length + (values.val.length-index.val) ∧
      out.2.2.2.val ≤ height.val + 2*(values.val.length-index.val) ⦄ := by
  unfold runtime.compiler.observe_values_loop
  apply loop.spec_decr_nat (fun state => values.val.length-state.2.2.2.1.val)
    (fun state => state.1 = budget ∧ state.2.2.2.2 = .Ok () ∧
      state.2.2.2.1.val ≤ values.val.length ∧
      state.2.1.length + (values.val.length-state.2.2.2.1.val) =
        before.length + (values.val.length-index.val) ∧
      state.2.2.1.val + 2*(values.val.length-state.2.2.2.1.val) ≤
        height.val + 2*(values.val.length-index.val))
  · rintro ⟨charged,offsets,current,next,status⟩ ⟨same,accepted,position,count,words⟩
    dsimp only at same accepted position count words
    subst charged status
    unfold runtime.compiler.observe_values_loop.body
    dsimp only
    split
    · rename_i more
      have atValue : next.val < values.val.length := by scalar_tac
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step as ⟨ty,found⟩
      have widthBound := stack_width_le_two ty
      step with observe_value_available ops bound available budget offsets current ty
        (by omega) (by omega) (by omega)
        as ⟨status,charged,after,afterHeight,accepted,same,appended,advanced⟩
      subst status charged
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · scalar_tac
      · simp only [alloc.vec.Vec.length] at count
        simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        omega
      · omega
      · scalar_tac
    · have last : next.val = values.val.length := by scalar_tac
      simp [last]
      exact ⟨by simpa [last] using count,by simpa [last] using words⟩
  · exact ⟨rfl,rfl,inside,rfl,by dsimp only; omega⟩

end Itasca.Runtime.Compiler

end

/-! ## Observe Budget Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Available stack observation leaves the complete compilation budget intact,
including every resource counter and any earlier error marker. -/
theorem compiler_observe_available_budget {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out => out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have initial : (if compiler.reachable then do
      let maximum ← lift (core.cmp.impls.OrdUsize.max compiler.function.max_stack (alloc.vec.Vec.len state.vals))
      .ok ({compiler.function with max_stack := maximum},state)
    else .ok (compiler.function,state)) ⦃ out =>
      out.1.local_slots = compiler.function.local_slots ∧ out.2 = state ⦄ := by
    split <;> step* <;> simp
  unfold runtime.compiler.FunctionCompiler.observe
  apply WP.spec_bind initial
  rintro ⟨function,otherState⟩ ⟨locals,sameState⟩
  dsimp only at locals sameState
  subst otherState
  step with runtime_clear compiler.before as ⟨cleared,empty⟩
  have capacity : cleared.length + (alloc.vec.Vec.deref state.vals).val.length ≤ Usize.max := by
    simpa [alloc.vec.Vec.length,empty,alloc.vec.Vec.deref] using state.vals.property
  have reserve : cleared.length + (alloc.vec.Vec.deref state.vals).val.length ≤ bound := by
    simpa [alloc.vec.Vec.length,empty,alloc.vec.Vec.deref] using request
  have words : function.local_slots.val + 2*(alloc.vec.Vec.deref state.vals).val.length ≤ U32.max := by
    simpa [locals,alloc.vec.Vec.deref] using slotsFit
  step with observe_values_available ops bound available compiler.budget cleared function.local_slots
    (alloc.vec.Vec.deref state.vals) 0#usize (by simp) (by simpa using capacity)
    (by simpa using reserve) (by simpa using words)
    as ⟨status,budget,offsets,height,accepted,same,count,wordBound⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  split
  · step as ⟨maximum,maximumEq⟩
    exact same
  · exact WP.spec.ret ⟨rfl,same⟩



end Itasca.Runtime.Compiler

end

/-! ## Frame -/

section

/-!
Frame and resource-measure preservation for compiler observation, used by callback capacity proofs.
-/

/-! ## Observe Frame -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca.ResultFacts

/-- Observation changes only compiler work state and allocation high-water marks. -/
def ObserveFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = { before with budget := after.budget, before := after.before, height := after.height, next_source := after.next_source, function := { before.function with max_stack := after.function.max_stack, slot_count := after.function.slot_count } }

theorem compiler_observe_frame_raw {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (status : core.result.Result Unit Itasca.error.VisitError) (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.FunctionCompiler.observe ops compiler state = .ok (status, after)) :
    ObserveFrame compiler after := by
  unfold runtime.compiler.FunctionCompiler.observe at accepted
  cases reachable : compiler.reachable <;>
    simp only [reachable, Bool.false_eq_true, ite_false, ite_true, lift, bind_ok] at accepted
  all_goals
    obtain ⟨cleared, clearRun, rest⟩ := bind_ok_inv _ _ _ accepted
    obtain ⟨⟨result, budget, values, height⟩, valuesRun, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      simp only [ObserveFrame, reachable]
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
        reachable, Bool.false_eq_true, ite_false, ite_true, lift,
        Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      simp only [ObserveFrame, reachable]

theorem compiler_observe_inv {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      ObserveFrame compiler out.2 ∧
      compiler.function.slot_count.val ≤ out.2.function.slot_count.val ⦄ := by
  unfold runtime.compiler.FunctionCompiler.observe
  split <;> step*
  all_goals cases r <;> simp_all [ObserveFrame, core.cmp.impls.OrdU32.max, alloc.vec.Vec.deref]
  all_goals try exact fun e => ⟨e⟩
  all_goals split <;> simp_all
  all_goals scalar_tac

@[step] theorem compiler_observe_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out => ObserveFrame compiler out.2 ⦄ := by
  exact WP.spec_mono (compiler_observe_inv ops law compiler state) (fun _ post => post.1)

/-- Observation never lowers the remembered slot capacity, including when the
current stack observation returns an error. -/
theorem compiler_observe_slot_count_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      compiler.function.slot_count.val ≤ out.2.function.slot_count.val ⦄ := by
  exact WP.spec_mono (compiler_observe_inv ops law compiler state) (fun _ post => post.2)
end Itasca.Runtime.Compiler

end

/-! ## Observe Measures -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- High-water marks are exactly the maxima of previously observed capacity
and the current validator stack; dead source positions do not increase them. -/
@[step] theorem compiler_observe_measures {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      out.1 = .Ok () →
        out.2.function.max_stack.val = (if compiler.reachable then
          max compiler.function.max_stack.val state.vals.val.length else compiler.function.max_stack.val) ∧
        out.2.function.slot_count.val = (if compiler.reachable then
          max compiler.function.slot_count.val (observedHeight compiler.function.local_slots.val state.vals.val)
          else compiler.function.slot_count.val) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.observe
  split <;> step*
  all_goals cases r <;> simp_all [core.cmp.impls.OrdUsize.max, core.cmp.impls.OrdU32.max, alloc.vec.Vec.deref]
  all_goals try exact fun e => ⟨e⟩
  all_goals split <;> simp_all
  all_goals split <;> simp_all
  all_goals scalar_tac
end Itasca.Runtime.Compiler

end

end
