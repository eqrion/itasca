import Itasca.Runtime.Compiler.Module.Stream
import Itasca.Binary.Leb128
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

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

@[step] theorem code_region_body_spec (bytes : Slice U8) (pos : Usize) (found : Bool)
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

/-- Code-region scanning always returns ordered in-bounds source views,
including malformed and truncated modules. -/
@[step] theorem code_region_spec (bytes : Slice U8) :
    runtime.compiler.code_region bytes ⦃ result => result.1.val ≤ result.2.val ∧ result.2.val ≤ bytes.length ⦄ := by
  unfold runtime.compiler.code_region runtime.compiler.code_region_loop
  apply loop.spec_decr_nat (fun state => regionMeasure bytes state.1 state.2.1)
    (fun state => state.2.2.1.val ≤ state.2.2.2.val ∧ state.2.2.2.val ≤ bytes.length)
  · rintro ⟨pos, found, first, last⟩ ⟨ordered, bounded⟩
    apply WP.spec_mono (code_region_body_spec bytes pos found first last ordered bounded)
    intro result post
    cases result <;> simpa only [and_assoc] using post
  · simp
end Itasca.Runtime.Code
