import Exec.Code.Local.Relations.Common.LayoutProofs
import Exec.Code.Local.Relations.Common.CompileInv
import Exec.Representation.Collection

/-! The extracted compiler rebuilds operand offsets from the validator's current
stack before each callback. These proofs cover the allocation-aware loop, its
reset, and the resulting concrete slot-layout invariant. Allocation rejection
and checked height overflow remain explicit compiler errors. -/

namespace Exec.Code
open Aeneas Aeneas.Std

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

/-- Observation preserves reachability and never reduces allocated frame capacity. -/
@[step] theorem compiler_observe_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      out.1 = .Ok () →
        out.2.reachable = compiler.reachable ∧
        compiler.function.slot_count.val ≤ out.2.function.slot_count.val ∧
        (out.2.reachable = true → out.2.height.val ≤ out.2.function.slot_count.val) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.observe
  split <;> step*
  all_goals cases r <;> simp_all [core.cmp.impls.OrdU32.max, alloc.vec.Vec.deref]
  all_goals try exact fun e => ⟨e⟩
  split <;> simp_all
  all_goals scalar_tac

theorem observedHeight_values (height : Nat) (types : List Itasca.types.ValueType) :
    observedHeight height (types.map Itasca.code.StackType.Val) =
      height + slots (types.map Itasca.Translate.valueType) := by
  induction types generalizing height with
  | nil => simp [observedHeight, slots]
  | cons ty rest ih => simp [observedHeight, compilerStackWidth, slots, ih, Nat.add_assoc]

theorem observedOffsets_values (height : Nat) (types : List Itasca.types.ValueType) :
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
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
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
  · rw [hoff, concrete, observedOffsets_values, localSlots]
    simp [stackOffsets, hlocals]
  · rw [hh, concrete, observedHeight_values, localSlots, hlocals]

end Exec.Code
