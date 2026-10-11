import Itasca.Module.ModuleEnvRequirements
import Itasca.Module.ModuleNamesComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A complete independent custom section exposes both its header and exact
name span; arbitrary remaining payload bytes are intentionally uninterpreted. -/
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

abbrev ModuleEnv.parseLoop (data : Slice U8) (env : module.Env) (pos : Usize) (last : U8)
    (profile : ValidationProfile := .Wasm1) :=
  module.validate_env_with_loop module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
    data profile () env pos last

theorem module.validate_env_with_loop.complete_stop (data : Slice U8) (env : module.Env)
    (pos : Usize) (last : U8) (hstop : StopAt data pos) (profile : ValidationProfile := .Wasm1) :
    ModuleEnv.parseLoop data env pos last profile = .ok (.Ok (env, pos), ()) := by
  rcases hstop with rfl | ⟨id, first, next, hh, hid⟩
  · unfold ModuleEnv.parseLoop module.validate_env_with_loop
    rw [Aeneas.Std.loop]
    simp [module.validate_env_with_loop.body]
  · have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
    have hcustom : id ≠ module.SECTION_CUSTOM := by simp only [global_simps]; scalar_tac
    have hcode : module.SECTION_CODE.val ≤ id.val := by simp only [global_simps]; scalar_tac
    have hr := module.read_section_header.complete data pos id first next hh
    unfold ModuleEnv.parseLoop module.validate_env_with_loop
    rw [Aeneas.Std.loop]
    simp [module.validate_env_with_loop.body, hmore, hr, hcustom, hcode,
      core.result.Result.Insts.CoreOpsTry.branch]

theorem module.validate_env_with_loop.complete_custom (data : Slice U8) (env : module.Env)
    (pos next : Usize) (last : U8)
    (hb : At (fun (_ : Unit) => CustomEncoding) data pos () next)
    (profile : ValidationProfile := .Wasm1) :
    ModuleEnv.parseLoop data env pos last profile = ModuleEnv.parseLoop data env next last profile := by
  obtain ⟨first, nameEnd, nm, hh, hn, hbefore⟩ := hb.custom_split
  have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hr := module.read_section_header.complete data pos 0#u8 first next hh
  obtain ⟨custom, hc, _⟩ := module.decode_custom_section.complete_raw data first nameEnd next nm hn hbefore
  unfold ModuleEnv.parseLoop module.validate_env_with_loop
  conv_lhs => rw [Aeneas.Std.loop]
  simp [module.validate_env_with_loop.body, hmore, hr, hc, global_simps,
    module.ModuleVisitor.on_custom_section.default, core.result.Result.Insts.CoreOpsTry.branch]

theorem module.validate_env_with_loop.complete_customs (data : Slice U8) (env : module.Env)
    (pos next : Usize) (last : U8)
    (hb : At (fun (_ : Unit) => CustomsEncoding) data pos () next)
    (profile : ValidationProfile := .Wasm1) :
    ModuleEnv.parseLoop data env pos last profile = ModuleEnv.parseLoop data env next last profile := by
  obtain ⟨bytes, hc, hs⟩ := hb
  induction hc generalizing pos with
  | nil => rw [hs.empty]
  | cons hcustom hrest ih =>
    obtain ⟨middle, hfirst, hremaining⟩ := hs.split
    rw [module.validate_env_with_loop.complete_custom data env pos middle last ⟨_, hcustom, hfirst⟩ profile]
    exact ih middle hremaining

theorem module.validate_env_with_loop.complete_section {profile : ValidationProfile} (data : Slice U8)
    (env result : module.Env) (pos first next : Usize) (last id : U8)
    (hh : SectionHeader data pos id first next) (hlo : 1 ≤ id.val) (hhi : id.val < 10)
    (horder : last.val < id.val)
    (hread : module.decode_env_section data first id env profile = .ok (.Ok next, result)) :
    ModuleEnv.parseLoop data env pos last profile = ModuleEnv.parseLoop data result next id profile := by
  have hmore : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hcustom : id ≠ module.SECTION_CUSTOM := by simp only [global_simps]; scalar_tac
  have hcode : ¬ module.SECTION_CODE.val ≤ id.val := by simp only [global_simps]; scalar_tac
  have hlast : ¬ id.val ≤ last.val := by scalar_tac
  have hr := module.read_section_header.complete data pos id first next hh
  unfold ModuleEnv.parseLoop module.validate_env_with_loop
  conv_lhs => rw [Aeneas.Std.loop]
  simp [module.validate_env_with_loop.body, hmore, hr, hcustom, hcode, hlast,
    hread, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
