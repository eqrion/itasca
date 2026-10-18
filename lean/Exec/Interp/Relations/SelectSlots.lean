import Exec.Interp.Relations.Select
import Exec.Interp.Relations.Regions
import Exec.Code.Local.Relations.Common.SelectLowering
set_option maxHeartbeats 1000000
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem select_slots {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (front : List val) (left right : val) (bits : Nat)
    (a b condition : U32) (ty : valtype)
    (values : ValuesAt exec.slots.val raw.base.val (front ++ [left,right,Abs.integerVal .I32 bits]))
    (leftType : Code.valueType left = ty) (rightType : Code.valueType right = ty)
    (leftPos : a.val = Code.slots (front.map Code.valueType))
    (rightPos : b.val = a.val+Code.width ty) (conditionPos : condition.val = b.val+Code.width ty)
    (bitsBound : bits < 2^32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index raw.instance raw.function raw.base
      (Code.selectInstruction (decide (Code.width ty = 2)) a b condition) ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ValuesAt out.2.1.slots.val raw.base.val (front ++ [if bits = 0 then right else left]) ∧
      {out.2.1 with slots := exec.slots} = exec ∧
      SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  have words : WordsAt exec.slots.val raw.base.val
      ((Code.encodeValues front ++ Code.encodeValue left ++ Code.encodeValue right) ++ [bits]) := by
    simpa only [ValuesAt,Code.encodeValues_append,Code.encodeValues,Code.encodeValue,Abs.integerVal,
      numtype_Inn,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using values
  have frontLength : (Code.encodeValues front).length = a.val := by rw [Code.encodeValues_length,leftPos]
  have leftLength : (Code.encodeValue left).length = Code.width ty := by rw [Code.encodeValue_length,leftType]
  have rightLength : (Code.encodeValue right).length = Code.width ty := by rw [Code.encodeValue_length,rightType]
  have conditionLength : (Code.encodeValues front ++ Code.encodeValue left ++ Code.encodeValue right).length = condition.val := by
    simp only [List.length_append,frontLength,leftLength,rightLength]
    omega
  obtain ⟨bound,wordEq⟩ := words.append_right 0 (by simp)
  have hc : raw.base.val+condition.val < exec.slots.length := by simpa only [conditionLength,Nat.add_zero] using bound
  have conditionWord : exec.slots.val[raw.base.val+condition.val]!.val = bits := by
    simpa only [conditionLength,Nat.add_zero,List.getElem!_cons_zero] using wordEq
  have castEq : (UScalar.cast .U32 exec.slots.val[raw.base.val+condition.val]!).val = bits := by scalar_tac
  have zeroEq : (UScalar.cast .U32 exec.slots.val[raw.base.val+condition.val]! = 0#u32) ↔ bits = 0 := by
    constructor
    · intro eq; have v := congrArg UScalar.val eq; change (UScalar.cast .U32 exec.slots.val[raw.base.val+condition.val]!).val = 0 at v; rwa [castEq] at v
    · intro eq; apply UScalar.eq_of_val_eq; change (UScalar.cast .U32 exec.slots.val[raw.base.val+condition.val]!).val = 0; rw [castEq,eq]
  have widthPositive := Code.width_positive ty
  have sourceBound : raw.base.val+b.val+Code.width ty ≤ exec.slots.length := by omega
  have destinationBound : raw.base.val+a.val+Code.width ty ≤ exec.slots.length := by omega
  have representation : ∀ newWords,
      newWords = (if bits = 0 then copyWords exec.slots.val (raw.base.val+a.val) (raw.base.val+b.val) (Code.width ty) else exec.slots.val) →
      ValuesAt newWords raw.base.val (front ++ [if bits = 0 then right else left]) ∧
      SlotPrefix raw.base.val exec.slots.val newWords := by
    intro newWords effect
    rw [effect]
    by_cases zero : bits = 0
    · rw [if_pos zero,if_pos zero]
      have input : WordsAt exec.slots.val (raw.base.val+b.val) (Code.encodeValue right) := by
        have last := words.append_left.append_right
        simpa only [List.length_append,frontLength,leftLength,← rightPos,Nat.add_assoc] using last
      have copied := words.append_left.append_left.append_left.copy_append input
        (Or.inl (by omega)) (by simpa only [rightLength] using sourceBound)
        (by simpa only [frontLength,rightLength] using destinationBound)
      refine ⟨?_,SlotPrefix.copy raw.base.val exec.slots.val (raw.base.val+a.val) (raw.base.val+b.val) (Code.width ty) (by omega)⟩
      rw [frontLength,rightLength] at copied
      simpa only [ValuesAt,Code.encodeValues_append,Code.encodeValues,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,frontLength,rightLength] using copied
    · rw [if_neg zero,if_neg zero]
      refine ⟨?_,.refl _ _⟩
      simpa only [ValuesAt,Code.encodeValues_append,Code.encodeValues,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using words.append_left.append_left
  have scalarWidth : Code.width ty = 1 ∨ Code.width ty = 2 := by cases ty <;> decide
  rcases scalarWidth with width | width
  · have narrow : decide (Code.width ty = 2) = false := by simp [width]
    rw [show Code.selectInstruction (decide (Code.width ty = 2)) a b condition = .Select a b condition by simp [narrow,Code.selectInstruction]]
    simp only [runtime.interp.dispatch]
    obtain ⟨out,result,success,changed,fields⟩ := WP.spec_imp_exists
      (select_effect memory hooks floats allocator exec raw.base a b condition hc (by omega) (by omega))
    rw [result,bind_ok]
    rcases out with ⟨status,updated⟩
    with_unfolding_all apply WP.spec.ret
    have converted := changed
    simp only [zeroEq] at converted
    have fresh := representation updated.slots.val (by simpa only [width] using converted)
    exact ⟨success,rfl,rfl,fresh.1,fields,fresh.2⟩
  · have wide : decide (Code.width ty = 2) = true := by simp [width]
    rw [show Code.selectInstruction (decide (Code.width ty = 2)) a b condition = .Select2 a b condition by simp [wide,Code.selectInstruction]]
    simp only [runtime.interp.dispatch]
    obtain ⟨out,result,success,changed,fields⟩ := WP.spec_imp_exists
      (select2_effect memory hooks floats allocator exec raw.base a b condition hc (by omega) (by omega))
    rw [result,bind_ok]
    rcases out with ⟨status,updated⟩
    with_unfolding_all apply WP.spec.ret
    have converted := changed
    simp only [zeroEq] at converted
    have fresh := representation updated.slots.val (by simpa only [width] using converted)
    exact ⟨success,rfl,rfl,fresh.1,fields,fresh.2⟩
end Exec.Interp
