import Itasca.Module.Code.Framing
import Itasca.Stream.Source

open Aeneas Aeneas.Std

namespace Itasca.StreamFraming

/-- A frame records the entry's declared byte extent and the corresponding
absolute offsets. It does not certify local declarations or instructions. -/
def EntryFrame (data : Slice U8) (pos index offset : Usize)
    (entry : stream.CodeEntry) : Prop :=
  ∃ content finish, ModuleCode.Extent data pos content finish ∧
    entry.index = index ∧ entry.start.val = offset.val + pos.val ∧
    entry.contents.val = offset.val + content.val ∧
    entry.end.val = offset.val + finish.val ∧
    entry.end.val ≤ limits.MAX_MODULE_BYTES.val

end Itasca.StreamFraming

namespace Itasca

@[step]
theorem stream.frame_entry.spec (data : Slice U8) (pos index offset : Usize) :
    stream.frame_entry data pos index offset ⦃ r => match r with
      | .Ok entry => StreamFraming.EntryFrame data pos index offset entry
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.code_entry_extent.spec data pos)
  rw [stream.frame_entry, hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨content, finish⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨r, hs, hsp⟩ := WP.spec_imp_exists (limits.add_offset.spec offset pos)
    rw [hs]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok start =>
      simp
      obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (limits.add_offset.spec offset content)
      rw [hc]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok contents =>
        simp
        obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec offset finish)
        rw [hf]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok last =>
          simp only [bind_ok, WP.spec_ok]
          exact ⟨content, finish, hp, rfl, hsp.1, hcp.1, hfp.1, hfp.2⟩

theorem stream.frame_entry.total (data : Slice U8) (pos index offset : Usize) :
    ∃ r, stream.frame_entry data pos index offset = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (stream.frame_entry.spec data pos index offset)
  exact ⟨r, hr⟩

theorem stream.frame_entry.sound (data : Slice U8) (pos index offset : Usize)
    (entry : stream.CodeEntry)
    (h : stream.frame_entry data pos index offset = .ok (.Ok entry)) :
    StreamFraming.EntryFrame data pos index offset entry := by
  have hs := stream.frame_entry.spec data pos index offset
  simpa [h] using hs

/-- A declared extent within the module offset cap can always be framed. -/
theorem stream.frame_entry.complete (data : Slice U8) (pos index offset content finish : Usize)
    (hext : ModuleCode.Extent data pos content finish)
    (hbound : offset.val + finish.val ≤ limits.MAX_MODULE_BYTES.val) :
    ∃ entry, stream.frame_entry data pos index offset = .ok (.Ok entry) ∧
      StreamFraming.EntryFrame data pos index offset entry := by
  have hp := hext.span
  obtain ⟨start, hs, hsp⟩ := limits.add_offset.complete offset pos (by omega)
  obtain ⟨contents, hc, hcp⟩ := limits.add_offset.complete offset content (by omega)
  obtain ⟨last, hf, hfp⟩ := limits.add_offset.complete offset finish hbound
  refine ⟨⟨index, start, contents, last⟩, ?_,
    content, finish, hext, rfl, hsp, hcp, hfp, by change last.val ≤ _; omega⟩
  simp [stream.frame_entry, module.code_entry_extent.complete data pos content finish hext,
    hs, hc, hf, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
