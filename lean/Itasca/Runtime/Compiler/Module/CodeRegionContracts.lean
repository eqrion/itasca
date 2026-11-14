import Itasca.Generated.FunsCompiler
import Itasca.Binary.Leb128
import Itasca.Module.Readers.Types
import Itasca.Support.Result

/-! Bounds and exact section transitions for the compiler source scanner. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts Itasca ModuleBinary

/-- The execution extraction's LEB reader is definitionally the canonical
reader, including its loop. This bridge adds no decoding assumption. -/
theorem compiler_leb_eq (bytes : Slice U8) (pos : Usize) :
    reader.read_u32_leb bytes pos = Itasca.reader.read_u32_leb bytes pos := by rfl

@[step] theorem compiler_leb_spec (bytes : Slice U8) (pos : Usize) :
    reader.read_u32_leb bytes pos ⦃ out => match out with
      | .Err _ => True
      | .Ok (_, next) => pos.val < next.val ∧ next.val ≤ bytes.length ⦄ := by
  rw [compiler_leb_eq]
  step with Itasca.reader.read_u32_leb.spec bytes pos as ⟨out, decoded⟩
  cases out with
  | Err error => trivial
  | Ok pair =>
    obtain ⟨value, next⟩ := pair
    have span := Itasca.Leb128.Decoded.span bytes pos value next decoded
    exact ⟨span.1, span.2.2⟩

def regionMeasure (bytes : Slice U8) (pos : Usize) (found : Bool) : Nat :=
  (bytes.length - pos.val) * 2 + if found then 0 else 1

theorem _root_.Itasca.runtime.compiler.code_region_loop.body.total (bytes : Slice U8) (pos : Usize) (found : Bool)
    (first last : Usize) (ordered : first.val ≤ last.val) (bounded : last.val ≤ bytes.length) :
    runtime.compiler.code_region_loop.body bytes pos found first last ⦃ out => match out with
      | .done (start, finish) => start.val ≤ finish.val ∧ finish.val ≤ bytes.length
      | .cont (next, seen, start, finish) => start.val ≤ finish.val ∧ finish.val ≤ bytes.length ∧
          regionMeasure bytes next seen < regionMeasure bytes pos found ⦄ := by
  unfold runtime.compiler.code_region_loop.body
  dsimp only
  split
  · rename_i more
    split
    · simp only [WP.spec_ok]
      exact ⟨ordered, bounded⟩
    · rename_i unseen
      have notFound : found = false := by simpa using unseen
      subst found
      step as ⟨id, idEq⟩
      split
      · split
        · simp only [WP.spec_ok, regionMeasure]
          scalar_tac
        · step as ⟨start, startEq⟩
          step with compiler_leb_spec bytes start as ⟨result, span⟩
          cases result with
          | Err error =>
            simp only [bind_ok]
            split <;> simp only [WP.spec_ok, regionMeasure] <;> scalar_tac
          | Ok pair =>
            obtain ⟨len, contents⟩ := pair
            dsimp only at span
            step as ⟨count, countEq⟩
            step as ⟨remaining, remainingEq⟩
            simp only [core.cmp.impls.OrdUsize.min, lift, bind_ok]
            split <;> step* <;> simp_all [regionMeasure] <;> scalar_tac
      · step as ⟨start, startEq⟩
        step with compiler_leb_spec bytes start as ⟨result, span⟩
        cases result with
        | Err error =>
          simp only [bind_ok]
          split <;> simp only [WP.spec_ok, regionMeasure] <;> scalar_tac
        | Ok pair =>
          obtain ⟨len, contents⟩ := pair
          dsimp only at span
          step as ⟨count, countEq⟩
          step as ⟨remaining, remainingEq⟩
          simp only [core.cmp.impls.OrdUsize.min, lift, bind_ok]
          split <;> step* <;> simp_all [regionMeasure] <;> scalar_tac
  · simp only [WP.spec_ok]
    exact ⟨ordered, bounded⟩

/-- One completed scanner body determines the loop result exactly. -/
theorem _root_.Itasca.runtime.compiler.code_region_loop.done
    (bytes : Slice U8) (pos : Usize) (found : Bool) (first last start finish : Usize)
    (called : runtime.compiler.code_region_loop.body bytes pos found first last = .ok (.done (start, finish))) :
    runtime.compiler.code_region_loop bytes pos found first last = .ok (start, finish) := by
  rw [runtime.compiler.code_region_loop, loop]
  dsimp only
  rw [called]
  simp only [bind_ok]

/-- A continuing scanner body transfers directly to the next loop state. -/
theorem _root_.Itasca.runtime.compiler.code_region_loop.step
    (bytes : Slice U8) (pos : Usize) (found : Bool) (first last next : Usize)
    (seen : Bool) (start finish : Usize)
    (called : runtime.compiler.code_region_loop.body bytes pos found first last = .ok (.cont (next, seen, start, finish))) :
    runtime.compiler.code_region_loop bytes pos found first last =
      runtime.compiler.code_region_loop bytes next seen start finish := by
  rw [runtime.compiler.code_region_loop, loop]
  dsimp only
  rw [called]
  simp only [bind_ok]
  rfl

/-- Found code or end-of-input stops without changing the retained boundaries. -/
theorem _root_.Itasca.runtime.compiler.code_region_loop.body.stopped
    (bytes : Slice U8) (pos : Usize) (found : Bool) (first last : Usize)
    (stopped : bytes.length ≤ pos.val ∨ found = true) :
    runtime.compiler.code_region_loop.body bytes pos found first last = .ok (.done (first, last)) := by
  unfold runtime.compiler.code_region_loop.body
  by_cases inside : pos < Slice.len bytes
  · have seen : found = true := by
      rcases stopped with outside | seen
      · scalar_tac
      · exact seen
    simp only [inside, seen, ↓reduceIte]
  · simp only [inside, ↓reduceIte]

/-- Every scanner state with ordered bounded coordinates terminates normally. -/
theorem _root_.Itasca.runtime.compiler.code_region_loop.total
    (bytes : Slice U8) (pos : Usize) (found : Bool) (first last : Usize)
    (ordered : first.val ≤ last.val) (bounded : last.val ≤ bytes.length) :
    runtime.compiler.code_region_loop bytes pos found first last ⦃ (start, finish) =>
      start.val ≤ finish.val ∧ finish.val ≤ bytes.length ⦄ := by
  unfold runtime.compiler.code_region_loop
  apply loop.spec_decr_nat (fun state => regionMeasure bytes state.1 state.2.1)
    (fun state => state.2.2.1.val ≤ state.2.2.2.val ∧ state.2.2.2.val ≤ bytes.length)
  · rintro ⟨cursor, seen, start, finish⟩ ⟨ordered, bounded⟩
    apply WP.spec_mono (runtime.compiler.code_region_loop.body.total bytes cursor seen start finish ordered bounded)
    intro result post
    cases result with
    | done pair =>
      rcases pair with ⟨start, finish⟩
      exact post
    | cont next => simpa only [and_assoc] using post
  · exact ⟨ordered, bounded⟩

/-- Initial scanning returns ordered in-bounds coordinates, even for malformed input. -/
theorem _root_.Itasca.runtime.compiler.code_region.total (bytes : Slice U8) :
    runtime.compiler.code_region bytes ⦃ (start, finish) => start.val ≤ finish.val ∧ finish.val ≤ bytes.length ⦄ := by
  unfold runtime.compiler.code_region
  exact runtime.compiler.code_region_loop.total bytes 8#usize false (Slice.len bytes) (Slice.len bytes)
    (Nat.le_refl _) (by simpa only [Slice.len_val] using Nat.le_refl bytes.length)

/-- An independently encoded section determines the precise scanner transition.
Sections after code stop at their header; data-count remains skippable. -/
theorem _root_.Itasca.runtime.compiler.code_region_loop.body.available
    (data : Slice U8) (pos first last : Usize) (id : U8)
    (header : SectionHeader data pos id first last) :
    runtime.compiler.code_region_loop.body data pos false (Slice.len data) (Slice.len data) =
      .ok (if id > 10#u8 ∧ id ≠ 12#u8 then .cont (pos, true, pos, pos)
        else if id = 10#u8 then .cont (last, true, pos, last)
        else .cont (last, false, Slice.len data, Slice.len data)) := by
  obtain ⟨middle, count, head, decoded, lastValue, bounded⟩ := header
  obtain ⟨position, byte, advance⟩ := head.byte.single
  have read := Itasca.reader.read_u32_leb.complete data middle count first decoded
  have post : runtime.compiler.code_region_loop.body data pos false (Slice.len data) (Slice.len data) ⦃ result =>
      result = if id > 10#u8 ∧ id ≠ 12#u8 then .cont (pos, true, pos, pos)
        else if id = 10#u8 then .cont (last, true, pos, last)
        else .cont (last, false, Slice.len data, Slice.len data) ⦄ := by
    unfold runtime.compiler.code_region_loop.body
    have inside : pos < Slice.len data := by scalar_tac
    simp only [inside, ↓reduceIte, Bool.false_eq_true]
    step as ⟨opcode, lookup⟩
    have actual : opcode = id := by simpa only [lookup] using byte
    simp only [actual, byte]
    by_cases high : id > 10#u8
    · by_cases isCount : id = 12#u8
      · rw [isCount]
        have highCount : (12#u8) > 10#u8 := by decide
        have notCode : (12#u8) ≠ 10#u8 := by decide
        have noStop : ¬ ((12#u8) > 10#u8 ∧ (12#u8) ≠ 12#u8) := fun pair => pair.2 rfl
        simp only [if_neg noStop]
        simp only [highCount, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
        step as ⟨advanced, advancedValue⟩
        have same : advanced = middle := UScalar.eq_of_val_eq (by omega)
        subst advanced
        simp only [compiler_leb_eq, read, bind_ok, lift]
        step as ⟨remaining, remainingValue⟩
        step as ⟨finish, finishValue⟩
        have same : finish = last := UScalar.eq_of_val_eq (by scalar_tac)
        subst finish
        simp only [notCode, ↓reduceIte, WP.spec_ok]
      · have different : (id != 12#u8) = true := by simpa only [bne_iff_ne] using isCount
        simp only [if_pos (And.intro high isCount)]
        simp only [high, different, ↓reduceIte, WP.spec_ok]
    · have noStop : ¬ (id > 10#u8 ∧ id ≠ 12#u8) := fun pair => high pair.1
      simp only [high, ↓reduceIte, if_neg noStop]
      step as ⟨advanced, advancedValue⟩
      have same : advanced = middle := UScalar.eq_of_val_eq (by omega)
      subst advanced
      simp only [compiler_leb_eq, read, bind_ok, lift]
      step as ⟨remaining, remainingValue⟩
      step as ⟨finish, finishValue⟩
      have same : finish = last := UScalar.eq_of_val_eq (by scalar_tac)
      subst finish
      split <;> simp_all only [WP.spec_ok, ↓reduceIte]
  obtain ⟨result, called, same⟩ := WP.spec_imp_exists post
  exact called.trans (congrArg Result.ok same)

end Itasca.Runtime.Compiler
