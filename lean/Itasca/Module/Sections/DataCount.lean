import Itasca.Module.Readers.BasicComplete

/-!
# Section order and data count section

`ModuleBinary.sectionRank` is the Wasm 2.0 section order, and `module.section_order` computes it
and rejects ids outside `1` to `12` (spec and `.complete`). `module.decode_data_count` reads the
data count section, which only Wasm 2.0 accepts, and records the count in the environment.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The position of a section id in the Wasm 2.0 order, which places the data count section (`12`)
before code (`10`) and data (`11`). Custom sections have no rank. -/
def sectionRank (id : U8) : U8 :=
  match id.val with
  | 12 => 10#u8
  | 10 => 11#u8
  | 11 => 12#u8
  | _ => id

/-- Ranks `1` to `10` belong to the ids `1` to `9` and `12`. -/
theorem sectionRank_prefix {id : U8} (hlo : 1 ≤ (sectionRank id).val)
    (hhi : (sectionRank id).val ≤ 10) :
    id.val = 1 ∨ id.val = 2 ∨ id.val = 3 ∨ id.val = 4 ∨ id.val = 5 ∨
      id.val = 6 ∨ id.val = 7 ∨ id.val = 8 ∨ id.val = 9 ∨ id.val = 12 := by
  by_cases h12 : id.val = 12
  · omega
  by_cases h10 : id.val = 10
  · have : (11#u8).val ≤ 10 := by simpa only [sectionRank, h10] using hhi
    change 11 ≤ 10 at this
    omega
  by_cases h11 : id.val = 11
  · have : (12#u8).val ≤ 10 := by simpa only [sectionRank, h11] using hhi
    change 12 ≤ 10 at this
    omega
  have he : sectionRank id = id := by simp [sectionRank]
  rw [he] at hlo hhi
  omega

end Itasca.ModuleBinary

namespace Itasca

/-- `module.section_order` returns the rank of an id from `1` to `12` and rejects other ids. -/
@[step]
theorem module.section_order.spec (id : U8) :
    module.section_order id ⦃ result => match result with
      | .Ok rank => rank = ModuleBinary.sectionRank id ∧ 1 ≤ id.val ∧ id.val ≤ 12
      | .Err _ => id.val = 0 ∨ 12 < id.val ⦄ := by
  have h10 : (10#uscalar : U8).val = 10 := rfl
  have h11 : (11#uscalar : U8).val = 11 := rfl
  have h12 : (12#uscalar : U8).val = 12 := rfl
  unfold module.section_order
  repeat' first | split
  all_goals simp_all [ModuleBinary.sectionRank, global_simps]
  all_goals first | omega | (split <;> simp_all; omega)

/-- `module.section_order` accepts every id from `1` to `12`. -/
theorem module.section_order.complete (id : U8) (hlo : 1 ≤ id.val) (hhi : id.val ≤ 12) :
    module.section_order id = .ok (.Ok (ModuleBinary.sectionRank id)) := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (module.section_order.spec id)
  cases result with
  | Err e => rcases hp with hz | hh <;> omega
  | Ok rank => simpa only [hp.1] using hr

/-- An accepted `module.decode_data_count` reads a `u32` count, sets only `data_count`, and
happens under Wasm 2.0. -/
@[step]
theorem module.decode_data_count.spec (data : Slice U8) (pos : Usize) (env : module.Env)
    (profile : ValidationProfile) :
    module.decode_data_count data pos env profile ⦃ result => match result.1 with
      | .Ok next => ∃ count,
          ModuleBinary.At ModuleBinary.StartEncoding data pos (some count) next ∧
          result.2 = { env with data_count := some count } ∧ profile = .Wasm2
      | .Err _ => True ⦄ := by
  cases profile with
  | Wasm1 => simp [module.decode_data_count]
  | Wasm2 =>
    obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
    cases r with
    | Err e =>
      simp [module.decode_data_count, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
    | Ok pair =>
      obtain ⟨count, next⟩ := pair
      simp only [module.decode_data_count, hr, bind_ok,
        core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨bytes, hs, hl, hb, he⟩ := hd
      exact ⟨count, ⟨bytes, ⟨count, rfl, he⟩, hs, hl, hb⟩, rfl, trivial⟩

/-- Under Wasm 2.0, `module.decode_data_count` accepts a count span and sets `data_count`. -/
theorem module.decode_data_count.complete (data : Slice U8) (pos : Usize) (env : module.Env)
    (count : U32) (next : Usize)
    (hb : ModuleBinary.At ModuleBinary.StartEncoding data pos (some count) next) :
    module.decode_data_count data pos env .Wasm2 = .ok (.Ok next, {env with data_count := some count}) := by
  obtain ⟨bytes, ⟨idx, hi, he⟩, hs⟩ := hb
  have hidx : idx = count := Option.some.inj hi.symm
  subst idx
  simp [module.decode_data_count, hs.read_u32 count he,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
