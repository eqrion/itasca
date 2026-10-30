import Itasca.Module.Readers.Basic

/-!
# UTF-8 validation

`metadata.validate_utf8.spec`: an accepted byte string satisfies the independent strict `Utf8`
predicate (canonical encodings of Unicode scalar values, including four-byte sequences). The
helpers `metadata.utf8_cont` and `metadata.utf8_sequence_len` get their own specs. Completeness is in
`Module/Readers/Utf8Complete`.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 1200000

namespace Itasca.ModuleBinary

/-- The `count` bytes at `pos` are in range and form one canonical UTF-8 character. -/
def Utf8Sequence (bytes : Slice U8) (pos count : Usize) : Prop :=
  pos.val + count.val ≤ bytes.length ∧ 0 < count.val ∧
    Utf8Char ((bytes.val.drop pos.val).take count.val)

/-- UTF-8 validity is closed under concatenation. -/
theorem Utf8.append {first rest} (h : Utf8 first) (h' : Utf8 rest) : Utf8 (first ++ rest) := by
  induction h with
  | nil => simpa using h'
  | cons hc _ ih => simpa [List.append_assoc] using Utf8.cons hc ih

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary

private theorem take_one (xs : List U8) (i : Nat) (hb : i < xs.length) :
    (xs.drop i).take 1 = [xs[i]] := by
  rw [List.drop_eq_getElem_cons hb, List.take, List.take]

private theorem take_two (xs : List U8) (i : Nat) (hb : i + 1 < xs.length) :
    (xs.drop i).take 2 = [xs[i]'(by omega), xs[i + 1]] := by
  rw [List.drop_eq_getElem_cons (by omega : i < xs.length)]
  simp only [List.take_succ_cons]
  rw [take_one xs (i + 1) hb]

private theorem take_three (xs : List U8) (i : Nat) (hb : i + 2 < xs.length) :
    (xs.drop i).take 3 = [xs[i]'(by omega), xs[i + 1]'(by omega), xs[i + 2]] := by
  rw [List.drop_eq_getElem_cons (by omega : i < xs.length)]
  simp only [List.take_succ_cons]
  rw [take_two xs (i + 1) (by omega)]

private theorem take_four (xs : List U8) (i : Nat) (hb : i + 3 < xs.length) :
    (xs.drop i).take 4 = [xs[i]'(by omega), xs[i + 1]'(by omega), xs[i + 2]'(by omega), xs[i + 3]] := by
  rw [List.drop_eq_getElem_cons (by omega : i < xs.length)]
  simp only [List.take_succ_cons]
  rw [take_three xs (i + 1) (by omega)]

/-- An accepted `metadata.utf8_cont` found an in-range byte between `lo` and `hi`. -/
@[step]
theorem metadata.utf8_cont.spec (bytes : Slice U8) (pos : Usize) (lo hi : U8) :
    metadata.utf8_cont bytes pos lo hi ⦃ r => r = .Ok () →
      ∃ hb : pos.val < bytes.length, lo.val ≤ bytes.val[pos.val].val ∧ bytes.val[pos.val].val ≤ hi.val ⦄ := by
  unfold metadata.utf8_cont
  step*

/-- `metadata.utf8_sequence_len` returns the length of one valid UTF-8 character at `pos`. -/
theorem metadata.utf8_sequence_len.spec (bytes : Slice U8) (pos : Usize)
    (hb : pos.val < bytes.length) :
    metadata.utf8_sequence_len bytes pos ⦃ r => match r with
      | .Ok count => Utf8Sequence bytes pos count
      | .Err _ => True ⦄ := by
  unfold metadata.utf8_sequence_len
  step
  split <;> step*
  all_goals try casesm* core.result.Result Unit error.Error
  all_goals simp_all
  all_goals have hbval := congrArg UScalar.val b_post
  all_goals clear b_post
  all_goals try simp only [show (224#8#uscalar : U8).val = 224 from rfl,
    show (237#8#uscalar : U8).val = 237 from rfl,
    show (240#8#uscalar : U8).val = 240 from rfl,
    show (244#8#uscalar : U8).val = 244 from rfl] at *
  all_goals try casesm* (∃ _, _), (_ ∧ _)
  all_goals try scalar_tac
  all_goals unfold Utf8Sequence
  all_goals refine ⟨by scalar_tac, by scalar_tac, ?_⟩
  all_goals simp only [UScalar.ofNatCore_val_eq]
  all_goals first
    | (rw [take_one bytes.val pos.val (by scalar_tac)]; apply Utf8Char.one; scalar_tac)
    | (rw [take_two bytes.val pos.val (by scalar_tac)]; apply Utf8Char.two <;> scalar_tac)
    | (rw [take_three bytes.val pos.val (by scalar_tac)]; apply Utf8Char.three <;> scalar_tac)
    | (rw [take_four bytes.val pos.val (by scalar_tac)]; apply Utf8Char.four <;> scalar_tac)

/-- `metadata.validate_utf8` returns normally, and acceptance implies `Utf8`. -/
@[step]
theorem metadata.validate_utf8.spec (bytes : Slice U8) :
    metadata.validate_utf8 bytes ⦃ r => r = .Ok () → Utf8 bytes.val ⦄ := by
  unfold metadata.validate_utf8 metadata.validate_utf8_loop
  apply loop.spec_decr_nat (fun i => bytes.length - i.val)
    (fun i => i.val ≤ bytes.length ∧ Utf8 (bytes.val.take i.val))
  · intro pos hp
    obtain ⟨hb, hprefix⟩ := hp
    by_cases hend : bytes.length ≤ pos.val
    · have heq : pos.val = bytes.length := by omega
      have hd : pos ≥ Slice.len bytes := by scalar_tac
      simp [metadata.validate_utf8_loop.body, hd]
      simpa [heq] using hprefix
    · have hlt : pos.val < bytes.length := by omega
      have hd : ¬pos ≥ Slice.len bytes := by scalar_tac
      obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (metadata.utf8_sequence_len.spec bytes pos hlt)
      cases r with
      | Err e =>
          simp [metadata.validate_utf8_loop.body, hd, hr,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok count =>
          obtain ⟨hbound, hpositive, hchar⟩ := hs
          simp [metadata.validate_utf8_loop.body, hd, hr,
            core.result.Result.Insts.CoreOpsTry.branch]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [i2_post, List.take_add]
          exact hprefix.append (by simpa using Utf8.cons hchar Utf8.nil)
  · exact ⟨by simp, by simpa using Utf8.nil⟩

end Itasca
