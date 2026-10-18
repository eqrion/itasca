import Exec.Spec.Wf

/-! Slot layout derived from specification value types. Prefix widths give
positions independently of the compiler's counters. Vector values use adjacent
low/high slots; every scalar or reference uses one slot. -/

namespace Exec.Code

def width : valtype → Nat
  | .V128 => 2
  | _ => 1

def slots : List valtype → Nat
  | [] => 0
  | t :: ts => width t + slots ts

def offset (types : List valtype) (index : Nat) : Nat := slots (types.take index)

theorem width_positive (t : valtype) : 0 < width t := by cases t <;> decide

theorem slots_append (xs ys : List valtype) : slots (xs ++ ys) = slots xs + slots ys := by
  induction xs with
  | nil => simp [slots]
  | cons t ts ih => simp only [List.cons_append, slots, ih, Nat.add_assoc]

theorem slots_take_add_drop (ts : List valtype) (n : Nat) :
    slots (ts.take n) + slots (ts.drop n) = slots ts := by
  rw [← slots_append, List.take_append_drop]

theorem offset_le (ts : List valtype) (n : Nat) : offset ts n ≤ slots ts := by
  have := slots_take_add_drop ts n
  unfold offset
  omega

/-- A local's complete slot range lies inside the local region. -/
theorem offset_add_width_le {ts : List valtype} {index : Nat} {ty : valtype}
    (h : ts[index]? = some ty) : offset ts index + width ty ≤ slots ts := by
  have bound := offset_le ts (index + 1)
  simpa [offset, List.take_add_one, h, slots_append, slots] using bound

theorem offset_lt_slots {ts : List valtype} {index : Nat} {ty : valtype}
    (h : ts[index]? = some ty) : offset ts index < slots ts := by
  have := offset_add_width_le h
  have := width_positive ty
  omega

/-- Local transfers cannot be elided as a self-copy: operand slots begin
strictly after every local's starting slot. -/
theorem local_before_stack {locals stack : List valtype} {index : Nat} {ty : valtype}
    (h : locals[index]? = some ty) : offset locals index < slots locals + slots stack := by
  have := offset_lt_slots h
  omega

/-- Every source value has at least one slot, including references. -/
theorem length_le_slots (ts : List valtype) : ts.length ≤ slots ts := by
  induction ts with
  | nil => simp [slots]
  | cons t ts ih =>
    have := width_positive t
    simp only [List.length_cons, slots]
    omega

/-- A source value uses at most two slots. -/
theorem slots_le_twice_length (ts : List valtype) : slots ts ≤ 2 * ts.length := by
  induction ts with
  | nil => simp [slots]
  | cons t ts ih =>
    have h : width t ≤ 2 := by cases t <;> decide
    simp only [List.length_cons, slots]
    omega

end Exec.Code
