import Itasca.Module.Readers.FramingComplete
import Itasca.Binary.Utf8

open Aeneas Aeneas.Std

set_option maxHeartbeats 1600000

namespace Itasca.Wasm

theorem BytesAt.get {data start bytes next} (h : BytesAt data start bytes next)
    (i : Nat) (hi : i < bytes.length) :
    data.val[start.val + i]'(by have := h.length; have := h.bound; scalar_tac) = bytes[i] := by
  have hd : i < (data.val.drop start.val).length := by
    simp only [List.length_drop]
    have := h.length
    have := h.bound
    scalar_tac
  have he : (data.val.drop start.val)[i] = bytes[i] := by
    simp only [h.suffix, List.getElem_append_left hi]
  simpa only [List.getElem_drop] using he

end Itasca.Wasm

namespace Itasca
open ModuleBinary

@[local step] private theorem utf8_cont_accepts (data : Slice U8) (pos : Usize) (lo hi : U8)
    (hp : pos.val < data.length)
    (hl : lo.val ≤ data.val[pos.val].val) (hh : data.val[pos.val].val ≤ hi.val) :
    module.utf8_cont data pos lo hi ⦃ r => r = .Ok () ⦄ := by
  unfold module.utf8_cont
  step*

theorem module.utf8_sequence_len.complete (data : Slice U8) (pos next : Usize)
    (encoded : List U8) (hc : Utf8Char encoded) (hb : Wasm.BytesAt data pos encoded next) :
    ∃ count, module.utf8_sequence_len data pos = .ok (.Ok count) ∧ count.val = encoded.length := by
  have hs : module.utf8_sequence_len data pos ⦃ r =>
      ∃ count, r = .Ok count ∧ count.val = encoded.length ⦄ := by
    have hlen := hb.length
    have hbound := hb.bound
    have heqval (a b : U8) : a = b ↔ a.val = b.val :=
      ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
    cases hc with
    | one a ha =>
        have h0 := hb.get 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at h0
        unfold module.utf8_sequence_len
        step
        split
        all_goals have hbval := congrArg UScalar.val b_post
        all_goals clear b_post
        all_goals try simp only [heqval, show (224#8#uscalar : U8).val = 224 from rfl,
          show (237#8#uscalar : U8).val = 237 from rfl,
          show (240#8#uscalar : U8).val = 240 from rfl,
          show (244#8#uscalar : U8).val = 244 from rfl] at *
        all_goals try (exfalso; scalar_tac)
        all_goals step* -grind
    | two a b ha ha' hb0 hb1 =>
        have h0 := hb.get 0 (by simp)
        have h1 := hb.get 1 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
        unfold module.utf8_sequence_len
        step
        split
        all_goals have hbval := congrArg UScalar.val b_post
        all_goals clear b_post
        all_goals try simp only [heqval, show (224#8#uscalar : U8).val = 224 from rfl,
          show (237#8#uscalar : U8).val = 237 from rfl,
          show (240#8#uscalar : U8).val = 240 from rfl,
          show (244#8#uscalar : U8).val = 244 from rfl] at *
        all_goals try (exfalso; scalar_tac)
        all_goals step* -grind
    | three a b c ha hc0 hc1 =>
        have h0 := hb.get 0 (by simp)
        have h1 := hb.get 1 (by simp)
        have h2 := hb.get 2 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2
        rcases ha with ha | ha | ha | ha
        all_goals unfold module.utf8_sequence_len
        all_goals step
        all_goals split
        all_goals have hbval := congrArg UScalar.val b_post
        all_goals clear b_post
        all_goals try simp only [heqval, show (224#8#uscalar : U8).val = 224 from rfl,
          show (237#8#uscalar : U8).val = 237 from rfl,
          show (240#8#uscalar : U8).val = 240 from rfl,
          show (244#8#uscalar : U8).val = 244 from rfl] at *
        all_goals try (exfalso; scalar_tac)
        all_goals step* -grind
    | four a b c d ha hc0 hc1 hd0 hd1 =>
        have h0 := hb.get 0 (by simp)
        have h1 := hb.get 1 (by simp)
        have h2 := hb.get 2 (by simp)
        have h3 := hb.get 3 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2 h3
        rcases ha with ha | ha | ha
        all_goals unfold module.utf8_sequence_len
        all_goals step
        all_goals split
        all_goals have hbval := congrArg UScalar.val b_post
        all_goals clear b_post
        all_goals try simp only [heqval, show (224#8#uscalar : U8).val = 224 from rfl,
          show (237#8#uscalar : U8).val = 237 from rfl,
          show (240#8#uscalar : U8).val = 240 from rfl,
          show (244#8#uscalar : U8).val = 244 from rfl] at *
        all_goals try (exfalso; scalar_tac)
        all_goals step* -grind
  obtain ⟨r, hr, count, rfl, hc⟩ := WP.spec_imp_exists hs
  exact ⟨count, hr, hc⟩


/-- The scanner accepts a complete independently valid UTF-8 suffix. -/
theorem module.validate_utf8_loop.complete (data : Slice U8) (pos : Usize)
    (encoded : List U8) (hc : Utf8 encoded)
    (hb : Wasm.BytesAt data pos encoded (Slice.len data)) :
    module.validate_utf8_loop data pos = .ok (.Ok ()) := by
  induction hc generalizing pos with
  | nil =>
      have he := hb.empty
      subst pos
      unfold module.validate_utf8_loop
      rw [loop]
      simp [module.validate_utf8_loop.body]
  | @cons first rest hchar hrest ih =>
      obtain ⟨middle, hfirst, htail⟩ := hb.split
      have hpositive : 0 < first.length := by cases hchar <;> simp
      have hmore : ¬ pos ≥ Slice.len data := by
        have := hfirst.length
        have := hfirst.bound
        scalar_tac
      obtain ⟨count, hcount, hlen⟩ := module.utf8_sequence_len.complete data pos middle first hchar hfirst
      obtain ⟨next, hnext, hn⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := pos) (y := count) (by have := hfirst.length; scalar_tac))
      have he : next = middle := UScalar.eq_of_val_eq (by have := hfirst.length; omega)
      subst next
      have hbody : module.validate_utf8_loop.body data pos = .ok (.cont middle) := by
        simp [module.validate_utf8_loop.body, hmore, hcount, hnext,
          core.result.Result.Insts.CoreOpsTry.branch]
      have hloop := ih middle htail
      unfold module.validate_utf8_loop at hloop ⊢
      rw [loop]
      simp only [hbody, bind_ok]
      exact hloop

/-- Strict independent UTF-8 validity suffices for actual scanner acceptance,
including every Unicode scalar through U+10FFFF. -/
theorem module.validate_utf8.complete (data : Slice U8) (h : Utf8 data.val) :
    module.validate_utf8 data = .ok (.Ok ()) := by
  apply module.validate_utf8_loop.complete data 0#usize data.val h
  constructor <;> simp

end Itasca
