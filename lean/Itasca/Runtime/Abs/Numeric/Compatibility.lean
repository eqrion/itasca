import Itasca.Runtime.Abs.Numeric.Transition

namespace Itasca.Runtime.Abs.Numeric

theorem binary_add_nat (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    (a + b).toNat = (a.toNat + b.toNat) % 2^integerWidth ty := by
  rw [BitVec.toNat_add]
  cases ty <;> rfl

theorem binary_sub_nat (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    (a - b).toNat = (a.toNat + 2^integerWidth ty - b.toNat) % 2^integerWidth ty := by
  rw [BitVec.toNat_sub]
  have width : sizenn (numtype_Inn ty) = integerWidth ty := by cases ty <;> rfl
  simp only [width]
  congr 1
  have := word_bound ty b
  omega

theorem finish_add (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.binary ty .ADD) a b =
      advance s { f with code := after, vals := front ++ [integerVal ty ((a.toNat + b.toNat) % 2^integerWidth ty)] } rest := by
  simp only [finish, Instruction.apply, binary, Instruction.output, binary_add_nat]

theorem finish_sub (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.binary ty .SUB) a b =
      advance s { f with code := after, vals := front ++ [integerVal ty ((a.toNat + 2^integerWidth ty - b.toNat) % 2^integerWidth ty)] } rest := by
  simp only [finish, Instruction.apply, binary, Instruction.output, binary_sub_nat]

theorem finish_eqz (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.eqz ty) a b =
      advance s { f with code := after, vals := front ++ [integerVal .I32 (if a.toNat = 0 then 1 else 0)] } rest := by
  change advance s { f with code := after, vals := front ++ [integerVal .I32
      (BitVec.ofNat 32 (if a.toNat = 0 then 1 else 0)).toNat] } rest = _
  have bits : (BitVec.ofNat 32 (if a.toNat = 0 then 1 else 0)).toNat =
      (if a.toNat = 0 then 1 else 0) := by split <;> decide
  rw [bits]

theorem finish_eq (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.compare ty .EQ) a b =
      advance s { f with code := after, vals := front ++ [integerVal .I32 (if a.toNat = b.toNat then 1 else 0)] } rest := by
  simp only [finish, Instruction.apply, Instruction.output, compare, BitVec.toNat_ofNat]
  split <;> simp_all

theorem finish_ltU (s f rest after front) (ty : Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    finish s f rest after front (.compare ty (.LT .U)) a b =
      advance s { f with code := after, vals := front ++ [integerVal .I32 (if a.toNat < b.toNat then 1 else 0)] } rest := by
  simp only [finish, Instruction.apply, Instruction.output, compare, BitVec.toNat_ofNat]
  split <;> simp_all

end Itasca.Runtime.Abs.Numeric
