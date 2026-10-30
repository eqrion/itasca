import Itasca.Module.Env.Requirements
import Itasca.Module.Readers.NamesComplete

/-!
# Replaying the environment loop

Equations that unfold `metadata.validate_env_with_loop` with the empty module visitor, abbreviated
`ModuleEnv.parseLoop`, one step at a time. Stopping at a code or data header
(`complete_stop`), skipping custom sections (`complete_custom`, `complete_customs`) and decoding
a declaration section (`complete_section`) are each stated as an equation on `parseLoop`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A custom section encoding has a section header and a name span inside it. The remaining payload
bytes are uninterpreted. -/
theorem At.custom_split {data pos next} (h : At (fun (_ : Unit) => CustomEncoding) data pos () next) :
    ∃ first nameEnd nm, SectionHeader data pos 0#u8 first next ∧
      At NameEncoding data first nm nameEnd ∧ nameEnd.val ≤ next.val := by
  obtain ⟨bytes, ⟨nm, payload, nameBytes, hn, hs⟩, hb⟩ := h
  obtain ⟨first, hh, encoded, he, hpayload⟩ :=
    At.section_split (show At (SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = nameBytes ++ payload))
      data pos () next from ⟨bytes, hs, hb⟩)
  subst encoded
  obtain ⟨nameEnd, hname, hrest⟩ := hpayload.split
  exact ⟨first, nameEnd, nm, hh, ⟨nameBytes, hn, hname⟩, by have := hrest.length; omega⟩

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary ModuleEnv

/-- The environment section loop run with the empty module visitor. -/
abbrev ModuleEnv.parseLoop (data : Slice U8) (env : metadata.Env) (pos : Usize) (last : U8)
    (profile : ValidationProfile := .Wasm1) :=
  metadata.validate_env_with_loop metadata.EmptyModuleVisitor.Insts.ItascaMetadataModuleVisitor
    data profile () env pos last

/-- At end of input or at a code or data header, the loop returns the current environment and
position. -/
theorem metadata.validate_env_with_loop.complete_stop (data : Slice U8) (env : metadata.Env)
    (pos : Usize) (last : U8) (hstop : StopAt data pos) (profile : ValidationProfile := .Wasm1) :
    ModuleEnv.parseLoop data env pos last profile = .ok (.Ok (env, pos), ()) := by
  rcases hstop with rfl | ⟨id, first, next, hh, hid⟩
  · unfold ModuleEnv.parseLoop metadata.validate_env_with_loop
    rw [Aeneas.Std.loop]
    simp [metadata.validate_env_with_loop.body]
  · have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
    have hr := metadata.read_section_header.complete data pos id first next hh
    unfold ModuleEnv.parseLoop metadata.validate_env_with_loop
    rw [Aeneas.Std.loop]
    rcases hid with rfl | rfl <;>
      simp [metadata.validate_env_with_loop.body, hmore, hr, global_simps,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- The loop skips one custom section. -/
theorem metadata.validate_env_with_loop.complete_custom (data : Slice U8) (env : metadata.Env)
    (pos next : Usize) (last : U8)
    (hb : At (fun (_ : Unit) => CustomEncoding) data pos () next)
    (profile : ValidationProfile := .Wasm1) :
    ModuleEnv.parseLoop data env pos last profile = ModuleEnv.parseLoop data env next last profile := by
  obtain ⟨first, nameEnd, nm, hh, hn, hbefore⟩ := hb.custom_split
  have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hr := metadata.read_section_header.complete data pos 0#u8 first next hh
  obtain ⟨custom, hc, _⟩ := metadata.decode_custom_section.complete_raw data first nameEnd next nm hn hbefore
  unfold ModuleEnv.parseLoop metadata.validate_env_with_loop
  conv_lhs => rw [Aeneas.Std.loop]
  simp [metadata.validate_env_with_loop.body, hmore, hr, hc, global_simps,
    metadata.ModuleVisitor.on_custom_section.default, core.result.Result.Insts.CoreOpsTry.branch]

/-- The loop skips any run of custom sections. -/
theorem metadata.validate_env_with_loop.complete_customs (data : Slice U8) (env : metadata.Env)
    (pos next : Usize) (last : U8)
    (hb : At (fun (_ : Unit) => CustomsEncoding) data pos () next)
    (profile : ValidationProfile := .Wasm1) :
    ModuleEnv.parseLoop data env pos last profile = ModuleEnv.parseLoop data env next last profile := by
  obtain ⟨bytes, hc, hs⟩ := hb
  induction hc generalizing pos with
  | nil => rw [hs.empty]
  | cons hcustom hrest ih =>
    obtain ⟨middle, hfirst, hremaining⟩ := hs.split
    rw [metadata.validate_env_with_loop.complete_custom data env pos middle last ⟨_, hcustom, hfirst⟩ profile]
    exact ih middle hremaining

/-- When `metadata.decode_env_section` succeeds on a declaration section in increasing order, the
loop continues from the end of the section with the updated environment and last-seen rank. -/
theorem metadata.validate_env_with_loop.complete_section {profile : ValidationProfile} (data : Slice U8)
    (env result : metadata.Env) (pos first next : Usize) (last id : U8)
    (hh : SectionHeader data pos id first next)
    (hlo : 1 ≤ (sectionRank id).val) (hhi : (sectionRank id).val ≤ 10)
    (horder : last.val < (sectionRank id).val)
    (hread : metadata.decode_env_section data first id env profile = .ok (.Ok next, result)) :
    ModuleEnv.parseLoop data env pos last profile = ModuleEnv.parseLoop data result next (sectionRank id) profile := by
  have hid := sectionRank_prefix hlo hhi
  have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hcustom : id ≠ metadata.SECTION_CUSTOM := by simp only [global_simps]; scalar_tac
  have hcode : id ≠ metadata.SECTION_CODE := by simp only [global_simps]; scalar_tac
  have hdata : id ≠ metadata.SECTION_DATA := by simp only [global_simps]; scalar_tac
  have hlast : ¬ (sectionRank id).val ≤ last.val := by omega
  have hrank := metadata.section_order.complete id (by omega) (by omega)
  have hr := metadata.read_section_header.complete data pos id first next hh
  unfold ModuleEnv.parseLoop metadata.validate_env_with_loop
  conv_lhs => rw [Aeneas.Std.loop]
  simp [metadata.validate_env_with_loop.body, hmore, hr, hcustom, hcode, hdata, hlast,
    hrank, hread, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
