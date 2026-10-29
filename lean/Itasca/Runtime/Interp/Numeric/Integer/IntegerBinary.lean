import Itasca.Runtime.Interp.Numeric.Integer.IntRotate
import Itasca.Runtime.Interp.Numeric.Integer.IntSigned
import Itasca.Runtime.SourceMachine.Numeric.Instruction
import Itasca.Runtime.Spec.IntegerDeterminism

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def integerWord (ty : Inn) (raw : U64) : BitVec (sizenn (numtype_Inn ty)) :=
  match ty with
  | .I32 => (UScalar.cast .U32 raw).bv
  | .I64 => raw.bv

@[simp] theorem integer_word32_to_nat (raw : U64) :
    (integerWord .I32 raw).toNat = raw.val % 4294967296 := by
  change (UScalar.cast .U32 raw).bv.toNat = _
  rw [UScalar.bv_toNat, UScalar.cast_val_eq]
  rfl

@[simp] theorem integer_word64_to_nat (raw : U64) :
    (integerWord .I64 raw).toNat = raw.val := by
  change raw.bv.toNat = _
  exact UScalar.bv_toNat raw

def binaryOpcode (ty : Inn) (op : binop_Inn) : U16 :=
  match ty, op with
  | .I32, .ADD => 106#u16
  | .I32, .SUB => 107#u16
  | .I32, .MUL => 108#u16
  | .I32, .DIV .S => 109#u16
  | .I32, .DIV .U => 110#u16
  | .I32, .REM .S => 111#u16
  | .I32, .REM .U => 112#u16
  | .I32, .AND => 113#u16
  | .I32, .OR => 114#u16
  | .I32, .XOR => 115#u16
  | .I32, .SHL => 116#u16
  | .I32, .SHR .S => 117#u16
  | .I32, .SHR .U => 118#u16
  | .I32, .ROTL => 119#u16
  | .I32, .ROTR => 120#u16
  | .I64, .ADD => 124#u16
  | .I64, .SUB => 125#u16
  | .I64, .MUL => 126#u16
  | .I64, .DIV .S => 127#u16
  | .I64, .DIV .U => 128#u16
  | .I64, .REM .S => 129#u16
  | .I64, .REM .U => 130#u16
  | .I64, .AND => 131#u16
  | .I64, .OR => 132#u16
  | .I64, .XOR => 133#u16
  | .I64, .SHL => 134#u16
  | .I64, .SHR .S => 135#u16
  | .I64, .SHR .U => 136#u16
  | .I64, .ROTL => 137#u16
  | .I64, .ROTR => 138#u16

/-- Numeric handlers either return their exact source result or a numeric trap. -/
def BinaryStatus (ty : Inn) (op : binop_Inn) (a b : U64)
    (status : core.result.Result U64 runtime.ExecError) : Prop :=
  match status with
  | .Ok value => fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op)
      (.mk_num__0 ty (.mk_uN (integerWord ty a).toNat))
      (.mk_num__0 ty (.mk_uN (integerWord ty b).toNat))
      (some [.mk_num__0 ty (.mk_uN value.val)])
  | .Err (.Trap trap) => (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
      fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op)
        (.mk_num__0 ty (.mk_uN (integerWord ty a).toNat))
        (.mk_num__0 ty (.mk_uN (integerWord ty b).toNat)) (some [])
  | _ => False

theorem scalar_binary_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (op : binop_Inn) (a b : U64) :
    runtime.interp.int.scalar floats (binaryOpcode ty op) a b ⦃ BinaryStatus ty op a b ⦄ := by
  cases ty with
  | I32 =>
    cases op with
    | ADD =>
      apply WP.spec_mono (scalar_i32_add_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SUB =>
      apply WP.spec_mono (scalar_i32_sub_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | MUL =>
      apply WP.spec_mono (scalar_i32_mul_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | DIV sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_divs_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨trap, rfl, allowed, relation⟩
          exact ⟨allowed, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
      | U =>
        apply WP.spec_mono (scalar_i32_divu_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
    | REM sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_rems_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
      | U =>
        apply WP.spec_mono (scalar_i32_remu_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
    | AND =>
      apply WP.spec_mono (scalar_i32_and_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | OR =>
      apply WP.spec_mono (scalar_i32_or_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | XOR =>
      apply WP.spec_mono (scalar_i32_xor_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SHL =>
      apply WP.spec_mono (scalar_i32_shl_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SHR sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_shrs_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
      | U =>
        apply WP.spec_mono (scalar_i32_shru_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | ROTL =>
      apply WP.spec_mono (scalar_i32_rotl_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | ROTR =>
      apply WP.spec_mono (scalar_i32_rotr_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
  | I64 =>
    cases op with
    | ADD =>
      apply WP.spec_mono (scalar_i64_add_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SUB =>
      apply WP.spec_mono (scalar_i64_sub_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | MUL =>
      apply WP.spec_mono (scalar_i64_mul_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | DIV sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_divs_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨trap, rfl, allowed, relation⟩
          exact ⟨allowed, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
      | U =>
        apply WP.spec_mono (scalar_i64_divu_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
    | REM sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_rems_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
      | U =>
        apply WP.spec_mono (scalar_i64_remu_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
    | AND =>
      apply WP.spec_mono (scalar_i64_and_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | OR =>
      apply WP.spec_mono (scalar_i64_or_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | XOR =>
      apply WP.spec_mono (scalar_i64_xor_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SHL =>
      apply WP.spec_mono (scalar_i64_shl_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SHR sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_shrs_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
      | U =>
        apply WP.spec_mono (scalar_i64_shru_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | ROTL =>
      apply WP.spec_mono (scalar_i64_rotl_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | ROTR =>
      apply WP.spec_mono (scalar_i64_rotr_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)

/-- Concrete results equal the deterministic word semantics; traps preserve the
same empty source result, and cannot become unrelated runtime errors. -/
def BinaryExact (ty : Inn) (op : binop_Inn) (a b : U64)
    (status : core.result.Result U64 runtime.ExecError) : Prop :=
  match status with
  | .Ok value => ∃ word, SourceMachine.Numeric.binary ty op (integerWord ty a) (integerWord ty b) = some word ∧ value.val = word.toNat
  | .Err (.Trap trap) => (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
      SourceMachine.Numeric.binary ty op (integerWord ty a) (integerWord ty b) = none
  | _ => False

theorem BinaryStatus.exact {ty : Inn} {op : binop_Inn} {a b : U64}
    {status : core.result.Result U64 runtime.ExecError} (sound : BinaryStatus ty op a b status) :
    BinaryExact ty op a b status := by
  have specified := SourceMachine.Numeric.binary_relation ty op (integerWord ty a) (integerWord ty b)
  cases status with
  | Ok value =>
    have same := Spec.integer_binop_deterministic sound specified
    cases result : SourceMachine.Numeric.binary ty op (integerWord ty a) (integerWord ty b) with
    | none => simp [result, SourceMachine.Numeric.binaryNumbers] at same
    | some word =>
      refine ⟨word, result, ?_⟩
      simpa only [result, SourceMachine.Numeric.binaryNumbers, List.singleton_inj, num_.mk_num__0.injEq, uN.mk_uN.injEq, true_and] using same
  | Err error =>
    cases error <;> try exact False.elim sound
    rename_i trap
    have same := Spec.integer_binop_deterministic sound.2 specified
    refine ⟨sound.1, ?_⟩
    cases result : SourceMachine.Numeric.binary ty op (integerWord ty a) (integerWord ty b) with
    | none => rfl
    | some word => simp [result, SourceMachine.Numeric.binaryNumbers] at same

theorem scalar_binary_exact {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (op : binop_Inn) (a b : U64) :
    runtime.interp.int.scalar floats (binaryOpcode ty op) a b ⦃ BinaryExact ty op a b ⦄ := by
  apply WP.spec_mono (scalar_binary_sound floats ty op a b)
  exact fun _ sound => sound.exact

end Itasca.Runtime.Interp
