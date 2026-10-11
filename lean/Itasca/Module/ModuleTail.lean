import Itasca.Module.ModuleDataTyping
import Itasca.Module.ModuleData
import Itasca.Module.ModuleNames

open Aeneas Aeneas.Std

namespace Itasca.ModuleTail

open ModuleBinary

theorem customs_append {xs ys} (hx : CustomsEncoding xs) (hy : CustomsEncoding ys) :
    CustomsEncoding (xs ++ ys) := by
  induction hx with
  | nil => simpa using hy
  | cons h _ ih => simpa [List.append_assoc] using CustomsEncoding.cons h ih

/-- A tail prefix records whether the unique data chunk has occurred. -/
inductive Prefix :
    Bool → List ModuleBinary.Data → List U8 → (profile : optParam ValidationProfile .Wasm1) → Prop where
  | empty {profile} : Prefix false [] [] profile
  | custom {profile seen segments before bytes} : Prefix seen segments before profile →
      CustomEncoding bytes → Prefix seen segments (before ++ bytes) profile
  | data {profile before bytes segments} : Prefix false [] before profile →
      SectionEncoding 11#u8 (VecEncoding (DataEncodingFor profile)) segments bytes →
      Prefix true segments (before ++ bytes) profile

theorem Prefix.not_seen {profile seen segments bytes} (h : Prefix seen segments bytes profile)
    (hs : seen = false) : segments = [] ∧ CustomsEncoding bytes := by
  induction h with
  | empty => exact ⟨rfl, .nil⟩
  | custom _ hc ih =>
    obtain ⟨he, hp⟩ := ih hs
    exact ⟨he, by simpa using customs_append hp (.cons hc .nil)⟩
  | data => cases hs

def Encoding (segments : List ModuleBinary.Data) (bytes : List U8)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  ∃ chunk customs, PaddedEncoding 11#u8 (VecEncoding (DataEncodingFor profile)) [] segments chunk ∧
    CustomsEncoding customs ∧ bytes = chunk ++ customs

theorem Prefix.encoding {profile seen segments bytes} (h : Prefix seen segments bytes profile) :
    Encoding segments bytes profile := by
  induction h with
  | empty => exact ⟨[], [], ⟨[], [], .nil, .absent, rfl⟩, .nil, rfl⟩
  | custom _ hc ih =>
    obtain ⟨chunk, customs, hs, ht, he⟩ := ih
    exact ⟨chunk, _, hs, (by simpa using customs_append ht (.cons hc .nil)), by simp [he, List.append_assoc]⟩
  | data hp hd =>
    exact ⟨_, [], ⟨_, _, (hp.not_seen rfl).2, .present hd, rfl⟩, .nil, by simp⟩

theorem header_payload {α : Type} {R : α → List U8 → Prop} {data start id first last value}
    (hh : SectionHeader data start id first last)
    (hp : At R data first value last) :
    At (SectionEncoding id R) data start value last := by
  obtain ⟨pos, size, hb, hd, he, hend⟩ := hh
  obtain ⟨payload, hp, hs⟩ := hp
  obtain ⟨sizeBytes, hd, hl, hn, hc⟩ := hd
  have hlen : payload.length = size.val := by have := hs.length; omega
  have hsize : Wasm.BytesAt data pos sizeBytes first := ⟨hd, hl, hn⟩
  refine ⟨id :: (sizeBytes ++ payload), ⟨sizeBytes, payload, ?_, hp, rfl⟩, ?_⟩
  · simpa [hlen] using hc
  · simpa using hb.byte.append (hsize.append hs)

theorem custom_encoded {data start first last nm} {custom : types.CustomSection}
    (hh : SectionHeader data start 0#u8 first last)
    (hn : At NameEncoding data first nm custom.payload_start)
    (hp : custom.payload_start.val ≤ last.val) :
    At (fun (_ : Unit) => CustomEncoding) data start () last := by
  obtain ⟨payload, _, hs⟩ := WP.spec_imp_exists
    (module.copy_bytes.spec data custom.payload_start last hp hh.span.2.2)
  obtain ⟨nameBytes, hn, hns⟩ := hn
  have hpayload : At (fun (_ : Unit) bs => bs = nameBytes ++ payload.val) data first () last :=
    ⟨nameBytes ++ payload.val, rfl, hns.append hs⟩
  obtain ⟨bytes, he, hb⟩ := header_payload hh hpayload
  exact ⟨bytes, ⟨nm, payload.val, nameBytes, hn, he⟩, hb⟩

theorem append_custom {profile seen segments data start pos next}
    (hp : At (fun segments bytes => Prefix seen segments bytes profile) data start segments pos)
    (hc : At (fun (_ : Unit) => CustomEncoding) data pos () next) :
    At (fun segments bytes => Prefix seen segments bytes profile) data start segments next := by
  obtain ⟨before, hp, hs⟩ := hp
  obtain ⟨bytes, hc, ht⟩ := hc
  exact ⟨before ++ bytes, .custom hp hc, hs.append ht⟩

theorem append_data {profile old segments data start pos next}
    (hp : At (fun segments bytes => Prefix false segments bytes profile) data start old pos)
    (hd : At (SectionEncoding 11#u8 (VecEncoding (DataEncodingFor profile))) data pos segments next) :
    At (fun segments bytes => Prefix true segments bytes profile) data start segments next := by
  obtain ⟨before, hp, hs⟩ := hp
  obtain ⟨bytes, hd, ht⟩ := hd
  have he := (hp.not_seen rfl).1
  subst old
  exact ⟨before ++ bytes, .data hp hd, hs.append ht⟩

/-- Module custom-chunk hooks may reject; totality excludes host panic/divergence. -/
def HooksTotal {V : Type} (visitor : module.ModuleVisitor V) : Prop :=
  ∀ (v : V) (chunk : types.CustomSection), ∃ r, visitor.on_custom_section v chunk = .ok r

theorem empty_hooks_total : HooksTotal module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor := by
  intro v chunk
  exact ⟨(.Ok (), v), rfl⟩

end Itasca.ModuleTail

namespace Itasca

/-- The actual tail loop consumes the entire remaining input, allowing custom
sections around at most one data section. Hooks may reject. -/
theorem module.validate_tail_with.spec {V : Type} (visitor : module.ModuleVisitor V)
    (htotal : ModuleTail.HooksTotal visitor) (data : Slice U8) (start : Usize)
    (env : module.Env) (v : V) (hstart : start.val ≤ data.length)
    (profile : ValidationProfile := .Wasm1) :
    module.validate_tail_with visitor data start env profile v ⦃ r => match r.1 with
      | .Ok tail => ModuleBinary.At (fun segments bytes => ModuleTail.Encoding segments bytes profile) data start
          (tail.data.val.map ModuleData.raw) (Slice.len data) ∧
          (∀ segment ∈ tail.data.val, ModuleData.Valid env segment) ∧
          ∀ count, env.data_count = some count → count.val = tail.data.val.length
      | .Err _ => True ⦄ := by
  unfold module.validate_tail_with module.validate_tail_with_loop
  apply loop.spec_decr_nat (fun s => data.length - s.2.2.1.val)
    (fun s => ModuleBinary.At (fun segments bytes => ModuleTail.Prefix s.2.2.2 segments bytes profile) data start
        (s.2.1.val.map ModuleData.raw) s.2.2.1 ∧
      ∀ segment ∈ s.2.1.val, ModuleData.Valid env segment)
  · rintro ⟨state, segments, pos, seen⟩ ⟨hbytes, hvalid⟩
    dsimp only at hbytes hvalid
    have hpos : pos.val ≤ data.length := hbytes.span.2
    unfold module.validate_tail_with_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : pos = Slice.len data := by apply UScalar.eq_of_val_eq; scalar_tac
      obtain ⟨bytes, hp, hs⟩ := hbytes
      cases hcount : env.data_count with
      | none =>
        simp only [WP.spec_ok]
        exact ⟨⟨bytes, hp.encoding, heq ▸ hs⟩, hvalid, by simp [hcount]⟩
      | some count =>
        step
        split
        · simp
        · simp only [WP.spec_ok]
          refine ⟨⟨bytes, hp.encoding, heq ▸ hs⟩, hvalid, ?_⟩
          intro other ho
          have he : other = count := Option.some.inj ho.symm
          subst other
          scalar_tac
    · rename_i hmore
      have hlt : pos.val < data.length := by scalar_tac
      obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
      rw [hr]
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok triple =>
        rcases triple with ⟨id, first, last⟩
        change ModuleBinary.SectionHeader data pos id first last at hh
        have hspan := hh.span
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        by_cases hc : id = module.SECTION_CUSTOM
        · simp only [hc, ↓reduceIte]
          obtain ⟨r, hcustom, hp⟩ := WP.spec_imp_exists (module.decode_custom_section.spec data first last)
          rw [hcustom]
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok custom =>
            obtain ⟨nm, hn, hbefore, hend, _⟩ := hp
            have hb := ModuleTail.custom_encoded (by simpa [hc, module.SECTION_CUSTOM] using hh) hn hbefore
            obtain ⟨⟨res, state'⟩, hvisit⟩ := htotal state custom
            simp [hvisit]
            cases res with
            | Err e => simp
            | Ok u =>
              exact ⟨ModuleTail.append_custom hbytes hb, hvalid, by scalar_tac⟩
        · simp only [hc, ↓reduceIte]
          by_cases hd : id = module.SECTION_DATA
          · subst id
            simp only [↓reduceIte]
            cases seen with
            | true => simp
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              obtain ⟨r, hdata, hp⟩ := WP.spec_imp_exists (module.decode_data_section.profile_spec data first env profile)
              rw [hdata]
              cases r with
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok pair =>
                rcases pair with ⟨decoded, next⟩
                obtain ⟨hencoded, htyped⟩ := hp
                simp
                by_cases he : next = last
                · subst next
                  simp only [↓reduceIte, WP.spec_ok]
                  have hb := ModuleTail.header_payload hh hencoded
                  exact ⟨ModuleTail.append_data hbytes (by simpa [module.SECTION_DATA] using hb), htyped, by scalar_tac⟩
                · have hn : next.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                  simp [hn]
          · have hn : id.val ≠ module.SECTION_DATA.val := fun h => hd (UScalar.eq_of_val_eq h)
            simp [hn]
  · refine ⟨?_, by simp [alloc.vec.Vec.new]⟩
    exact ⟨[], .empty, Wasm.BytesAt.nil data start hstart⟩

theorem module.validate_tail.spec (data : Slice U8) (start : Usize) (env : module.Env)
    (hstart : start.val ≤ data.length) (profile : ValidationProfile := .Wasm1) :
    module.validate_tail data start env profile ⦃ r => match r with
      | .Ok tail => ModuleBinary.At (fun segments bytes => ModuleTail.Encoding segments bytes profile) data start
          (tail.data.val.map ModuleData.raw) (Slice.len data) ∧
          (∀ segment ∈ tail.data.val, ModuleData.Valid env segment) ∧
          ∀ count, env.data_count = some count → count.val = tail.data.val.length
      | .Err _ => True ⦄ := by
  obtain ⟨⟨r, state⟩, hr, hp⟩ := WP.spec_imp_exists
    (module.validate_tail_with.spec module.EmptyModuleVisitor.Insts.ItascaModuleModuleVisitor
      ModuleTail.empty_hooks_total data start env () hstart profile)
  simpa [module.validate_tail, hr] using hp

end Itasca
