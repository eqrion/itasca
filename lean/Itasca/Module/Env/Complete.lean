import Itasca.Module.Env.Replay
import Itasca.Module.Env.Chain
import Itasca.Module.Env.DispatchComplete

/-!
# Completeness of the environment parser

`module.validate_env.profile_complete` shows that an independently encoded declaration prefix
meeting the declarative requirements makes `module.validate_env` succeed at the greedy boundary
and reach a ready state. `Chain.profile_complete` is the loop induction behind it. The Wasm 1.0
specializations are `Chain.complete` and `module.validate_env.complete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary

/-- The parser loop `parseLoop` accepts any `Chain` encoding. Absent slots advance the ghost
phase, and only actual sections update the parser's last-seen section id. -/
theorem Chain.profile_complete {profile raw n bytes} (h : Chain raw n bytes profile)
    (data : Slice U8) (env : module.Env) (decls : Declarations) (pos next : Usize) (last : U8)
    (hb : Wasm1.BytesAt data pos bytes next) (hstop : StopAt data next)
    (hready : Ready raw n decls env) (hbound : Bounded env pos.val)
    (hlast : last.val ≤ n) (hreq : Requirements raw profile)
    (hallowed : ModuleTypesAllowed profile {raw with codes := [], data := []}) :
    ∃ result finalDecls, parseLoop data env pos last profile = .ok (.Ok (result, next), ()) ∧
      Ready raw 10 finalDecls result := by
  induction h generalizing env decls pos last with
  | @done profile bytes hc =>
    refine ⟨env, decls, ?_, hready⟩
    rw [module.validate_env_with_loop.complete_customs data env pos next last ⟨_, hc, hb⟩ profile]
    exact module.validate_env_with_loop.complete_stop data env next last hstop profile
  | @step profile n id first rest hn hid hslot hrest ih =>
    obtain ⟨middle, hfirst, hremaining⟩ := hb.split
    obtain ⟨customs, body, hc, hbody, heq⟩ := hslot
    rw [heq] at hfirst
    obtain ⟨afterCustoms, hcustoms, hsection⟩ := hfirst.split
    have hcustomeq := module.validate_env_with_loop.complete_customs data env pos afterCustoms last ⟨_, hc, hcustoms⟩ profile
    have hbound' : Bounded env afterCustoms.val := hbound.mono (by have := hcustoms.length; omega)
    have hlo : 1 ≤ (sectionRank id).val := by omega
    have hhi : (sectionRank id).val ≤ 10 := by omega
    have hready' : Ready raw ((sectionRank id).val - 1) decls env := by simpa only [hid, Nat.add_sub_cancel] using hready
    rcases hbody with ⟨hempty, rfl⟩ | hpresent
    · have hend := hsection.empty
      subst middle
      have hr : Ready raw (n + 1) decls env := by simpa only [hid] using hready'.absent hlo hhi hempty
      obtain ⟨result, finalDecls, hrun, hr⟩ := ih env decls afterCustoms last hremaining hr hbound' (by omega) hreq hallowed
      exact ⟨result, finalDecls, hcustomeq.trans hrun, hr⟩
    · obtain ⟨payloadStart, hh, hencoding⟩ := At.section_split
        (show At (SectionEncoding id (fun u bs => Payload raw (sectionRank id).val u bs profile)) data afterCustoms () middle from ⟨_, hpresent, hsection⟩)
      have hboundPayload := hbound'.mono (Nat.le_of_lt hh.span.1)
      obtain ⟨updated, hread, heffect⟩ := module.decode_env_section.profile_complete data payloadStart id env decls raw middle profile
        hlo hhi hencoding (hreq (sectionRank id).val decls env hlo hhi hready') hready' hboundPayload hallowed
      have hrep := heffect.represents hready'.represents hready'.phase (by omega)
      have hr : Ready raw (n + 1) (update raw (sectionRank id).val decls) updated := by
        simpa only [hid] using hready'.updated hlo hhi hrep
      have hupdated : Bounded updated middle.val := by
        have hs := module.decode_env_section.profile_spec data payloadStart id env decls profile hboundPayload
        simp only [hread, WP.spec_ok] at hs
        exact hs.choose_spec.2
      obtain ⟨result, finalDecls, hrun, hr⟩ := ih updated (update raw (sectionRank id).val decls) middle (sectionRank id) hremaining hr hupdated (by omega) hreq hallowed
      refine ⟨result, finalDecls, hcustomeq.trans ?_, hr⟩
      exact (module.validate_env_with_loop.complete_section data env updated afterCustoms payloadStart middle last id
        hh hlo (by omega) (by omega) hread).trans hrun

end Itasca.ModuleEnv

namespace Itasca

open ModuleBinary ModuleEnv

/-- Declarative requirements and an independently encoded complete environment
prefix imply success of the actual environment parser at its greedy boundary. -/
theorem module.validate_env.profile_complete (data : Slice U8) (raw : ModuleBinary.Module) (profile : ValidationProfile)
    (decls : Declarations) (next : Usize)
    (hprefix : At (fun ds bs => PrefixEncoding ds bs profile) data 0#usize decls next)
    (hraw : raw = decls.module raw.codes raw.data)
    (hstop : StopAt data next) (hrequirements : Requirements raw profile) :
    ∃ env finalDecls, module.validate_env data profile = .ok (.Ok (env, next)) ∧
      Ready raw 10 finalDecls env := by
  obtain ⟨bytes, hp, hs⟩ := hprefix
  obtain ⟨suffix, hchain, hbytes⟩ := hp.chain raw.codes raw.data
  have hchain' : Chain raw 0 suffix profile := by simpa only [← hraw] using hchain
  rw [hbytes] at hs
  obtain ⟨start, hheader, hsections⟩ := hs.split
  have hread := module.read_header.complete data start hheader
  obtain ⟨initial, hnew, hrep, _, _, hbound, hphase⟩ := WP.spec_imp_exists module.Env.new.declarations
  have hready : Ready raw 0 {} initial := by
    refine ⟨hrep, hphase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have hallowed : ModuleTypesAllowed profile {raw with codes := [], data := []} := by
    have he := congrArg (fun (value : ModuleBinary.Module) => {value with codes := [], data := []}) hraw
    rw [he]
    exact hp.allowed
  obtain ⟨env, finalDecls, hrun, hready⟩ := hchain'.profile_complete data initial {} start next 0#u8
    hsections hstop hready (hbound.mono (Nat.zero_le _)) (by simp) hrequirements hallowed
  refine ⟨env, finalDecls, ?_, hready⟩
  simp [module.validate_env, module.validate_env_with, hnew, hread,
    core.result.Result.Insts.CoreOpsTry.branch, hrun]

/-- `module.validate_env.profile_complete` for Wasm 1.0. -/
theorem module.validate_env.complete (data : Slice U8) (raw : ModuleBinary.Module)
    (decls : Declarations) (next : Usize)
    (hprefix : At PrefixEncoding data 0#usize decls next)
    (hraw : raw = decls.module raw.codes raw.data)
    (hstop : StopAt data next) (hrequirements : Requirements raw) :
    ∃ env finalDecls, module.validate_env data .Wasm1 = .ok (.Ok (env, next)) ∧
      Ready raw 10 finalDecls env := by
  exact module.validate_env.profile_complete data raw .Wasm1 decls next hprefix hraw hstop hrequirements

end Itasca
