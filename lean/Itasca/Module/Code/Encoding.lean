import Itasca.Module.Code.Locals
import Itasca.Binary.Wasm1.EncodingComplete

/-!
# Code entry encodings from byte provenance

Conversions between the streaming byte provenance used by the extracted code-entry reader
(`Wasm1.Consumed`, `Wasm1.BytesAt`) and the independent module grammar
(`At`, `Rep`), and `slice_bytes` for the body slice a parser returns.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The streaming token provenance of a body is an `At (Rep Wasm1.TokenEncoding)` of the module
grammar. -/
theorem consumed_rep {data start tokens next}
    (h : Wasm1.Consumed data start tokens next) :
    At (Rep Wasm1.TokenEncoding) data start tokens next := by
  induction h with
  | nil hb => exact ⟨[], .nil, Wasm1.BytesAt.nil _ _ hb⟩
  | snoc hprev ht ih =>
    obtain ⟨bs, he, hs⟩ := ih
    obtain ⟨cs, hc, hp⟩ := ht
    exact ⟨bs ++ cs, he.snoc hc, hs.append hp⟩

/-- A slice taken from `first` to `last` holds exactly the parent buffer's bytes in that
interval. -/
theorem slice_bytes {data : Slice U8} {first last : Usize} {body : Slice U8}
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length)
    (hbody : body.val = data.val.slice first.val last.val) :
    Wasm1.BytesAt data first body.val last := by
  refine ⟨?_, ?_, hlast⟩
  · rw [hbody, List.slice]
    have he : first.val + (last.val - first.val) = last.val := by omega
    simpa only [List.drop_drop, he] using
      (List.take_append_drop (last.val - first.val) (data.val.drop first.val)).symm
  · rw [hbody, List.slice_length]
    simp only [Slice.length] at hlast
    omega

/-- A token repetition with matching bytes gives streaming provenance. -/
theorem rep_consumed {data start next tokens bytes}
    (he : Rep Wasm1.TokenEncoding tokens bytes) (hs : Wasm1.BytesAt data start bytes next) :
    Wasm1.Consumed data start tokens next := by
  induction he generalizing start with
  | nil =>
    have hn := hs.empty
    subst next
    exact .nil _ hs.bound
  | cons ht hrest ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hs.split
    exact Wasm1.Consumed.cons_iff.mpr ⟨middle, ⟨_, ht, hfirst⟩, ih hrest⟩

end Itasca.ModuleBinary
