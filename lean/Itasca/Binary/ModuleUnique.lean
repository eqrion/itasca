import Itasca.Binary.UnicodeUnique

/-!
Sections, each formerly its own module: ModuleUniquePrimitives, ModuleUniqueSections, ModuleUniqueSegments, ModuleUnique.
-/

/-! ## ModuleUniquePrimitives -/

section

/-!
# Prefix uniqueness of module components

Proves `PrefixUnique` for the encodings of value, element, function, table, memory and global
types, constant expressions, imports, exports, globals, locals, and the start section.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem valueByte_injective : Function.Injective valueByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [valueByte]

theorem elemByte_injective : Function.Injective elemByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [elemByte]

theorem mutByte_injective : Function.Injective mutByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [mutByte]

/-- Value type encodings are prefix-unique. -/
theorem valueType_prefix_unique : PrefixUnique ValueTypeEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨hv, rfl⟩ := List.cons.inj he
  obtain rfl := valueByte_injective hv
  exact ⟨rfl, rfl, rfl⟩

/-- Function type encodings are prefix-unique. -/
theorem funcType_prefix_unique : PrefixUnique FuncTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xp, xr, hp, hr, rfl⟩ := hx
  obtain ⟨yp, yr, hp', hr', rfl⟩ := hy
  have hseq1 := (List.cons.inj he).2
  obtain ⟨hpv, rfl, hseq2⟩ := valueType_prefix_unique.vec hp hp' (by simpa [List.append_assoc] using hseq1)
  obtain ⟨hrv, rfl, rfl⟩ := valueType_prefix_unique.vec hr hr' hseq2
  have hp := alloc.vec.Vec.ext _ _ hpv
  have hr := alloc.vec.Vec.ext _ _ hrv
  have hxy : x = y := by cases x; cases y; simp_all
  exact ⟨hxy, rfl, rfl⟩

/-- Limits encodings are prefix-unique. -/
theorem limits_prefix_unique : PrefixUnique LimitsEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have : (0#u8) = 1#u8 := he.1; contradiction }
  all_goals try { have : (1#u8) = 0#u8 := he.1; contradiction }
  case noMax.noMax x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case max.max x xmax a b hx hm y ymax c d hy hn =>
    obtain ⟨rfl, rfl, ht⟩ := index_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hm hn ht
    exact ⟨rfl, rfl, rfl⟩

/-- Table type encodings are prefix-unique. -/
theorem tableType_prefix_unique : PrefixUnique TableTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨a, hx, rfl⟩ := hx
  obtain ⟨b, hy, rfl⟩ := hy
  obtain ⟨helem, hrest⟩ := List.cons.inj he
  have helem := elemByte_injective helem
  obtain ⟨hv, rfl, rfl⟩ := limits_prefix_unique hx hy hrest
  have hxy : x = y := by cases x; cases y; simp_all
  exact ⟨hxy, by simp [helem], rfl⟩

/-- Memory type encodings are prefix-unique. -/
theorem memType_prefix_unique : PrefixUnique MemTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨hv, rfl, rfl⟩ := limits_prefix_unique hx hy he
  have hxy : x = y := by cases x; cases y; cases hv; rfl
  exact ⟨hxy, rfl, rfl⟩

/-- Global type encodings are prefix-unique. -/
theorem globalType_prefix_unique : PrefixUnique GlobalTypeEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨hv, hseq1⟩ := List.cons.inj he
  obtain ⟨hm, rfl⟩ := List.cons.inj hseq1
  have hv := valueByte_injective hv
  have hm := mutByte_injective hm
  have hxy : x = y := by cases x; cases y; simp_all
  exact ⟨hxy, by simp [hv, hm], rfl⟩

/-- Constant expression encodings are prefix-unique. -/
theorem const_prefix_unique : PrefixUnique ConstEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  case i32.i32 x a hx y b hy =>
    obtain ⟨hv, rfl, hseq1⟩ := signed32_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := IScalar.eq_of_val_eq hv
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case i64.i64 x a hx y b hy =>
    obtain ⟨hv, rfl, hseq1⟩ := signed64_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := IScalar.eq_of_val_eq hv
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case f32.f32 x a hx y b hy =>
    obtain ⟨hv, rfl, hseq1⟩ := float_prefix_unique 4 hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case f64.f64 x a hx y b hy =>
    obtain ⟨hv, rfl, hseq1⟩ := float_prefix_unique 8 hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case globalGet.globalGet x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := index_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case refFunc.refFunc x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := index_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case refNull.refNull x y =>
    obtain rfl := elemByte_injective he.2.1
    exact ⟨rfl, rfl, he.2.2.2⟩
  case v128.v128 low high sub first second hs hl hh low' high' sub' first' second' hs' hl' hh' =>
    obtain ⟨_, rfl, hseq1⟩ := index_prefix_unique hs hs' (by simpa [List.append_assoc] using he.2)
    obtain ⟨hlo, rfl, hseq2⟩ := float_prefix_unique 8 hl hl' (by simpa [List.append_assoc] using hseq1)
    obtain ⟨hhi, rfl, hseq3⟩ := float_prefix_unique 8 hh hh' (by simpa [List.append_assoc] using hseq2)
    obtain rfl := UScalar.eq_of_val_eq hlo
    obtain rfl := UScalar.eq_of_val_eq hhi
    obtain rfl := (List.cons.inj hseq3).2
    exact ⟨rfl, rfl, rfl⟩

/-- Import descriptor encodings are prefix-unique. -/
theorem importDesc_prefix_unique : PrefixUnique ImportDescEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  case func.func x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case table.table x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := tableType_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case memory.memory x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := memType_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case global.global x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := globalType_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩

/-- Export descriptor encodings are prefix-unique. -/
theorem exportDesc_prefix_unique : PrefixUnique ExportDescEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  all_goals
    rename_i x a hx y b hy
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩

/-- Import encodings are prefix-unique. -/
theorem import_prefix_unique : PrefixUnique ImportEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xm, xn, xd, hm, hn, hd, rfl⟩ := hx
  obtain ⟨ym, yn, yd, hm', hn', hd', rfl⟩ := hy
  obtain ⟨hmv, rfl, hseq1⟩ := name_prefix_unique hm hm' (by simpa [List.append_assoc] using he)
  obtain ⟨hnv, rfl, hseq2⟩ := name_prefix_unique hn hn' (by simpa [List.append_assoc] using hseq1)
  obtain ⟨hdv, rfl, rfl⟩ := importDesc_prefix_unique hd hd' hseq2
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

/-- Export encodings are prefix-unique. -/
theorem export_prefix_unique : PrefixUnique ExportEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xn, xd, hn, hd, rfl⟩ := hx
  obtain ⟨yn, yd, hn', hd', rfl⟩ := hy
  obtain ⟨hnv, rfl, hseq1⟩ := name_prefix_unique hn hn' (by simpa [List.append_assoc] using he)
  obtain ⟨hdv, rfl, rfl⟩ := exportDesc_prefix_unique hd hd' hseq1
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

/-- Global encodings are prefix-unique. -/
theorem global_prefix_unique : PrefixUnique GlobalEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xt, xe, ht, he', rfl⟩ := hx
  obtain ⟨yt, ye, ht', he'', rfl⟩ := hy
  obtain ⟨htv, rfl, hseq1⟩ := globalType_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
  obtain ⟨hev, rfl, rfl⟩ := const_prefix_unique he' he'' hseq1
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

/-- Local declaration encodings are prefix-unique. -/
theorem local_prefix_unique : PrefixUnique LocalEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨hn, rfl, hseq1⟩ := index_prefix_unique ha hb (by simpa [List.append_assoc] using he)
  obtain ⟨ht, rfl⟩ := List.cons.inj hseq1
  have ht := valueByte_injective ht
  have hv : x = y := Prod.ext hn ht
  exact ⟨hv, by simp [ht], rfl⟩

/-- Start section payload encodings are prefix-unique. -/
theorem start_prefix_unique : PrefixUnique StartEncoding := by
  rintro x y a b rest tail ⟨xi, rfl, hx⟩ ⟨yi, rfl, hy⟩ he
  obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he
  exact ⟨rfl, rfl, rfl⟩

end Itasca.ModuleBinary

end

/-! ## ModuleUniqueSections -/

section

/-!
# Section framing

Defines the raw section framing
(`SectionDecode.Encoding`) that erases payload interpretation. `PaddedEncoding.frames` shows
that a field preceded by custom sections is a uniquely framed section list with at most one
payload for the field. `SectionDecode.Field.unique` lifts payload uniqueness to fields.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

namespace SectionDecode

/-- A raw section: id byte, LEB128 size and payload bytes, with the payload uninterpreted. -/
def Encoding (frame : U8 × List U8) (bytes : List U8) : Prop :=
  ∃ size, Leb128.Encoding size frame.2.length ∧ bytes = frame.1 :: (size ++ frame.2)

/-- Raw section frames are prefix-unique. -/
theorem prefix_unique : PrefixUnique Encoding := by
  rintro ⟨xt, xp⟩ ⟨yt, yp⟩ a b rest tail ⟨xn, hx, rfl⟩ ⟨yn, hy, rfl⟩ he
  obtain ⟨rfl, hbody⟩ := List.cons.inj he
  obtain ⟨hlen, rfl, hpayload⟩ := leb_prefix_unique hx hy
    (by simpa [List.append_assoc] using hbody)
  obtain ⟨rfl, rfl⟩ := split_of_length hpayload hlen
  exact ⟨rfl, rfl, rfl⟩

/-- A sequence of raw section frames is determined by its bytes. -/
theorem unique : Unique (Rep Encoding) :=
  prefix_unique.rep_unique (by rintro _ _ ⟨n, hn, rfl⟩; simp)

/-- The payloads of the sections with the given id, in order. -/
def payloads (id : U8) : List (U8 × List U8) → List (List U8)
  | [] => []
  | (tag, bytes) :: sections =>
      if id = tag then bytes :: payloads id sections else payloads id sections

theorem payloads_append (id : U8) (xs ys : List (U8 × List U8)) :
    payloads id (xs ++ ys) = payloads id xs ++ payloads id ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp only [List.cons_append, payloads]; split <;> simp_all

/-- A standard field is either omitted, giving `absent`, or encoded by exactly one payload. -/
inductive Field {α : Type} (R : α → List U8 → Prop) (absent : α) : α → List (List U8) → Prop where
  | absent : Field R absent absent []
  | present {value bytes} : R value bytes → Field R absent value [bytes]

/-- A field's value is determined by its payloads. -/
theorem Field.unique {α : Type} {R : α → List U8 → Prop} {absent x y payloads}
    (hu : Unique R) (hx : Field R absent x payloads) (hy : Field R absent y payloads) : x = y := by
  cases hx <;> cases hy
  · rfl
  · apply hu <;> assumption

end SectionDecode

/-- A section encoding gives a raw frame with the same payload. -/
theorem SectionEncoding.frame {α : Type} {R : α → List U8 → Prop} {id value bytes}
    (h : SectionEncoding id R value bytes) :
    ∃ payload, R value payload ∧ SectionDecode.Encoding (id, payload) bytes := by
  obtain ⟨size, payload, hn, hp, rfl⟩ := h
  exact ⟨payload, hp, size, hn, rfl⟩

/-- Custom sections frame into a section list with no payload for any other id. -/
theorem CustomsEncoding.frames {bytes} (h : CustomsEncoding bytes) :
    ∃ sections, Rep SectionDecode.Encoding sections bytes ∧
      ∀ id, id ≠ 0#u8 → SectionDecode.payloads id sections = [] := by
  induction h with
  | nil => exact ⟨[], .nil, by intros; rfl⟩
  | cons hc _ ih =>
    obtain ⟨nm, content, nameBytes, hn, hs⟩ := hc
    obtain ⟨payload, _, hf⟩ := hs.frame
    obtain ⟨sections, hp, hids⟩ := ih
    refine ⟨(0#u8, payload) :: sections, .cons hf hp, ?_⟩
    intro id hid
    simp [SectionDecode.payloads, hid, hids id hid]

/-- A field preceded by custom sections frames into a section list with the field's payload
under its own id and none under other ids. -/
theorem PaddedEncoding.frames {α : Type} {R : α → List U8 → Prop} {id absent value bytes}
    (h : PaddedEncoding id R absent value bytes) :
    ∃ sections payloads, Rep SectionDecode.Encoding sections bytes ∧
      SectionDecode.Field R absent value payloads ∧
      ∀ wanted, wanted ≠ 0#u8 → SectionDecode.payloads wanted sections =
        if wanted = id then payloads else [] := by
  obtain ⟨customs, sec, hc, hs, rfl⟩ := h
  obtain ⟨before, hp, hids⟩ := hc.frames
  cases hs with
  | absent => exact ⟨before, [], by simpa using hp, .absent, by intros; simp [*]⟩
  | present hs =>
    obtain ⟨payload, hv, hf⟩ := hs.frame
    refine ⟨before ++ [(id, payload)], [payload], hp.snoc hf, .present hv, ?_⟩
    intro wanted hw
    simp [SectionDecode.payloads_append, hids wanted hw, SectionDecode.payloads]

end Itasca.ModuleBinary

end

/-! ## ModuleUniqueSegments -/

section

/-!
# Prefix uniqueness of segments

Proves `PrefixUnique` for the Wasm 2.0 element and data segment encodings by splitting off the
flag and treating each flag's payload grammar separately. `elementFor_prefix_unique` and
`dataFor_prefix_unique` cover Wasm 2.0.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The grammar of an element segment payload after its flag. -/
private inductive ElementPayload : Nat → Element → List U8 → Prop where
  | activeIndices {offset initializers encodedOffset entries} :
      ConstEncoding offset encodedOffset → VecEncoding IndexEncoding initializers entries →
      ElementPayload 0 ⟨.FuncRef, .Active 0#u32 offset, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (encodedOffset ++ entries)
  | passiveIndices {initializers entries} : VecEncoding IndexEncoding initializers entries →
      ElementPayload 1 ⟨.FuncRef, .Passive, initializers.map wasm_types.ConstExpr.RefFunc⟩ (0#u8 :: entries)
  | explicitIndices {tableIndex offset initializers table encodedOffset entries} :
      IndexEncoding tableIndex table → ConstEncoding offset encodedOffset →
      VecEncoding IndexEncoding initializers entries →
      ElementPayload 2 ⟨.FuncRef, .Active tableIndex offset, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (table ++ encodedOffset ++ (0#u8 :: entries))
  | declarativeIndices {initializers entries} : VecEncoding IndexEncoding initializers entries →
      ElementPayload 3 ⟨.FuncRef, .Declarative, initializers.map wasm_types.ConstExpr.RefFunc⟩ (0#u8 :: entries)
  | activeExpressions {offset initializers encodedOffset entries} :
      ConstEncoding offset encodedOffset → VecEncoding ConstEncoding initializers entries →
      ElementPayload 4 ⟨.FuncRef, .Active 0#u32 offset, initializers⟩ (encodedOffset ++ entries)
  | passiveExpressions {elem initializers entries} : VecEncoding ConstEncoding initializers entries →
      ElementPayload 5 ⟨elem, .Passive, initializers⟩ (elemByte elem :: entries)
  | explicitExpressions {elem tableIndex offset initializers table encodedOffset entries} :
      IndexEncoding tableIndex table → ConstEncoding offset encodedOffset →
      VecEncoding ConstEncoding initializers entries →
      ElementPayload 6 ⟨elem, .Active tableIndex offset, initializers⟩
        (table ++ encodedOffset ++ (elemByte elem :: entries))
  | declarativeExpressions {elem initializers entries} : VecEncoding ConstEncoding initializers entries →
      ElementPayload 7 ⟨elem, .Declarative, initializers⟩ (elemByte elem :: entries)

private theorem element_parts {entry bytes} (h : Wasm2ElementEncoding entry bytes) :
    ∃ flag flags payload, IndexEncoding flag flags ∧ ElementPayload flag.val entry payload ∧
      bytes = flags ++ payload := by
  cases h with
  | activeIndices hf ho hi => exact ⟨0#u32, _, _, hf, .activeIndices ho hi, by simp [List.append_assoc]⟩
  | passiveIndices hf hi => exact ⟨1#u32, _, _, hf, .passiveIndices hi, by simp [List.append_assoc]⟩
  | explicitIndices hf ht ho hi => exact ⟨2#u32, _, _, hf, .explicitIndices ht ho hi, by simp [List.append_assoc]⟩
  | declarativeIndices hf hi => exact ⟨3#u32, _, _, hf, .declarativeIndices hi, by simp [List.append_assoc]⟩
  | activeExpressions hf ho hi => exact ⟨4#u32, _, _, hf, .activeExpressions ho hi, by simp [List.append_assoc]⟩
  | passiveExpressions hf hi => exact ⟨5#u32, _, _, hf, .passiveExpressions hi, by simp [List.append_assoc]⟩
  | explicitExpressions hf ht ho hi => exact ⟨6#u32, _, _, hf, .explicitExpressions ht ho hi, by simp [List.append_assoc]⟩
  | declarativeExpressions hf hi => exact ⟨7#u32, _, _, hf, .declarativeExpressions hi, by simp [List.append_assoc]⟩

private theorem elementPayload_prefix_unique (flag : Nat) : PrefixUnique (ElementPayload flag) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case activeIndices.activeIndices offset initializers encodedOffset entries ho hi offset' initializers' encodedOffset' entries' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩
  case passiveIndices.passiveIndices initializers entries hi initializers' entries' hi' =>
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique.vec hi hi' (List.cons.inj he).2
    exact ⟨rfl, rfl, rfl⟩
  case explicitIndices.explicitIndices table offset initializers tb ob ib ht ho hi table' offset' initializers' tb' ob' ib' ht' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, hs'⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using hs)
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique.vec hi hi' (List.cons.inj hs').2
    exact ⟨rfl, rfl, rfl⟩
  case declarativeIndices.declarativeIndices initializers entries hi initializers' entries' hi' =>
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique.vec hi hi' (List.cons.inj he).2
    exact ⟨rfl, rfl, rfl⟩
  case activeExpressions.activeExpressions offset initializers encodedOffset entries ho hi offset' initializers' encodedOffset' entries' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩
  case passiveExpressions.passiveExpressions elem initializers entries hi elem' initializers' entries' hi' =>
    obtain ⟨ht, hs⟩ := List.cons.inj he
    obtain rfl := elemByte_injective ht
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩
  case explicitExpressions.explicitExpressions elem table offset initializers tb ob ib ht ho hi elem' table' offset' initializers' tb' ob' ib' ht' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, hs'⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using hs)
    obtain ⟨hty, hs''⟩ := List.cons.inj hs'
    obtain rfl := elemByte_injective hty
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs''
    exact ⟨rfl, rfl, rfl⟩
  case declarativeExpressions.declarativeExpressions elem initializers entries hi elem' initializers' entries' hi' =>
    obtain ⟨ht, hs⟩ := List.cons.inj he
    obtain rfl := elemByte_injective ht
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩

/-- Wasm 2.0 element segment encodings are prefix-unique. -/
theorem wasm2Element_prefix_unique : PrefixUnique Wasm2ElementEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xf, xb, xp, hxf, hxp, rfl⟩ := element_parts hx
  obtain ⟨yf, yb, yp, hyf, hyp, rfl⟩ := element_parts hy
  obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique hxf hyf (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := elementPayload_prefix_unique _ hxp hyp hs
  exact ⟨rfl, rfl, rfl⟩

/-- The grammar of a data segment payload after its flag. -/
private inductive DataPayload : Nat → Data → List U8 → Prop where
  | implicit {offset init encodedOffset entries} :
      ConstEncoding offset encodedOffset → ByteVecEncoding init entries →
      DataPayload 0 ⟨.Active 0#u32 offset, init⟩ (encodedOffset ++ entries)
  | passive {init entries} : ByteVecEncoding init entries →
      DataPayload 1 ⟨.Passive, init⟩ entries
  | explicit {index offset init indexBytes encodedOffset entries} :
      IndexEncoding index indexBytes → ConstEncoding offset encodedOffset → ByteVecEncoding init entries →
      DataPayload 2 ⟨.Active index offset, init⟩ (indexBytes ++ encodedOffset ++ entries)

private theorem data_parts {entry bytes} (h : Wasm2DataEncoding entry bytes) :
    ∃ flag flags payload, IndexEncoding flag flags ∧ DataPayload flag.val entry payload ∧
      bytes = flags ++ payload := by
  cases h with
  | active hi ho hb =>
    cases hi with
    | implicit hf => exact ⟨0#u32, _, _, hf, .implicit ho hb, by simp [List.append_assoc]⟩
    | explicit hf hi => exact ⟨2#u32, _, _, hf, .explicit hi ho hb, by simp [List.append_assoc]⟩
  | passive hf hb => exact ⟨1#u32, _, _, hf, .passive hb, rfl⟩

private theorem dataPayload_prefix_unique (flag : Nat) : PrefixUnique (DataPayload flag) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case implicit.implicit offset init encodedOffset entries ho hi offset' init' encodedOffset' entries' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, rfl⟩ := byte_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩
  case passive.passive init hi init' hi' =>
    obtain ⟨rfl, rfl, rfl⟩ := byte_prefix_unique.vec hi hi' he
    exact ⟨rfl, rfl, rfl⟩
  case explicit.explicit index offset init indexBytes encodedOffset entries ht ho hi index' offset' init' indexBytes' encodedOffset' entries' ht' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, hs'⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using hs)
    obtain ⟨rfl, rfl, rfl⟩ := byte_prefix_unique.vec hi hi' hs'
    exact ⟨rfl, rfl, rfl⟩

/-- Wasm 2.0 data segment encodings are prefix-unique. -/
theorem wasm2Data_prefix_unique : PrefixUnique Wasm2DataEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xf, xb, xp, hxf, hxp, rfl⟩ := data_parts hx
  obtain ⟨yf, yb, yp, hyf, hyp, rfl⟩ := data_parts hy
  obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique hxf hyf (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := dataPayload_prefix_unique _ hxp hyp hs
  exact ⟨rfl, rfl, rfl⟩

/-- Wasm 2.0 element segment encodings are prefix-unique. -/
theorem elementFor_prefix_unique : PrefixUnique ElementEncodingFor := by
  exact wasm2Element_prefix_unique

/-- Wasm 2.0 data segment encodings are prefix-unique. -/
theorem dataFor_prefix_unique : PrefixUnique DataEncodingFor := by
  exact wasm2Data_prefix_unique

end Itasca.ModuleBinary

end

/-! ## ModuleUnique -/

section

/-!
# Uniqueness of module decoding

`ModuleEncodingWith.unique` shows that two raw modules with the same encoding are equal, for
Wasm 2.0 and any prefix-unique code entry grammar. Custom section placement and omitted
empty sections introduce no ambiguity. `Itasca/Results/Unique` specializes it to the validator’s code entry grammar.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The data count section frames like other optional fields. -/
theorem DataCountSectionEncoding.frames {value bytes}
    (h : DataCountSectionEncoding value bytes) :
    ∃ sections payloads, Rep SectionDecode.Encoding sections bytes ∧
      SectionDecode.Field StartEncoding none value payloads ∧
      ∀ wanted, wanted ≠ 0#u8 → SectionDecode.payloads wanted sections =
        if wanted = 12#u8 then payloads else [] := by
  exact PaddedEncoding.frames h

namespace SectionDecode

/-- The standard fields of a raw module as payloads of a raw section list. -/
structure Fields (raw : Module) (sections : List (U8 × List U8))
    (codeRel : Code → List U8 → Prop) : Prop where
  types : Field (VecEncoding FuncTypeEncoding) [] raw.types (payloads 1#u8 sections)
  imports : Field (VecEncoding ImportEncoding) [] raw.imports (payloads 2#u8 sections)
  functions : Field (VecEncoding IndexEncoding) [] raw.functions (payloads 3#u8 sections)
  tables : Field (VecEncoding TableTypeEncoding) [] raw.tables (payloads 4#u8 sections)
  memories : Field (VecEncoding MemTypeEncoding) [] raw.memories (payloads 5#u8 sections)
  globals : Field (VecEncoding GlobalEncoding) [] raw.globals (payloads 6#u8 sections)
  exports : Field (VecEncoding ExportEncoding) [] raw.exports (payloads 7#u8 sections)
  start : Field StartEncoding none raw.start (payloads 8#u8 sections)
  elements : Field (VecEncoding ElementEncodingFor) [] raw.elements (payloads 9#u8 sections)
  dataCount : Field StartEncoding none raw.dataCount (payloads 12#u8 sections)
  codes : Field (VecEncoding codeRel) [] raw.codes (payloads 10#u8 sections)
  data : Field (VecEncoding DataEncodingFor) [] raw.data (payloads 11#u8 sections)

end SectionDecode

/-- A module encoding gives a raw section list that carries every standard field. -/
theorem ModuleEncodingWith.sections {codeRel raw bytes}
    (h : ModuleEncodingWith codeRel raw bytes) :
    ∃ sections, Rep SectionDecode.Encoding sections (bytes.drop magicVersion.length) ∧
      SectionDecode.Fields raw sections codeRel := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, bc, b10, b11, b12,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, hc, h10, h11, h12, hb, _⟩ := h
  obtain ⟨s1, p1, hr1, hf1, hl1⟩ := h1.frames
  obtain ⟨s2, p2, hr2, hf2, hl2⟩ := h2.frames
  obtain ⟨s3, p3, hr3, hf3, hl3⟩ := h3.frames
  obtain ⟨s4, p4, hr4, hf4, hl4⟩ := h4.frames
  obtain ⟨s5, p5, hr5, hf5, hl5⟩ := h5.frames
  obtain ⟨s6, p6, hr6, hf6, hl6⟩ := h6.frames
  obtain ⟨s7, p7, hr7, hf7, hl7⟩ := h7.frames
  obtain ⟨s8, p8, hr8, hf8, hl8⟩ := h8.frames
  obtain ⟨s9, p9, hr9, hf9, hl9⟩ := h9.frames
  obtain ⟨sCount, pCount, hrCount, hfCount, hlCount⟩ := hc.frames
  obtain ⟨s10, p10, hr10, hf10, hl10⟩ := h10.frames
  obtain ⟨s11, p11, hr11, hf11, hl11⟩ := h11.frames
  obtain ⟨sc, hrc, hlc⟩ := h12.frames
  let sections := s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9 ++ sCount ++ s10 ++ s11 ++ sc
  have hr : Rep SectionDecode.Encoding sections
      (b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9 ++ bc ++ b10 ++ b11 ++ b12) :=
    ((((((((((((hr1.append hr2).append hr3).append hr4).append hr5).append hr6).append hr7).append hr8).append hr9).append hrCount).append hr10).append hr11).append hrc)
  have lookup (id : U8) (hid : id ≠ 0#u8) :
      SectionDecode.payloads id sections =
        (if id = 1#u8 then p1 else []) ++
        (if id = 2#u8 then p2 else []) ++
        (if id = 3#u8 then p3 else []) ++
        (if id = 4#u8 then p4 else []) ++
        (if id = 5#u8 then p5 else []) ++
        (if id = 6#u8 then p6 else []) ++
        (if id = 7#u8 then p7 else []) ++
        (if id = 8#u8 then p8 else []) ++
        (if id = 9#u8 then p9 else []) ++
        (if id = 12#u8 then pCount else []) ++
        (if id = 10#u8 then p10 else []) ++
        (if id = 11#u8 then p11 else []) := by
    simp only [sections, SectionDecode.payloads_append, hl1 id hid, hl2 id hid, hl3 id hid,
      hl4 id hid, hl5 id hid, hl6 id hid, hl7 id hid, hl8 id hid, hl9 id hid, hlCount id hid, hl10 id hid,
      hl11 id hid, hlc id hid, List.append_nil]
  refine ⟨sections, ?_, ?_⟩
  · simpa only [hb, List.append_assoc, List.drop_left] using hr
  · constructor
    · simpa [lookup 1#u8 (by decide)] using hf1
    · simpa [lookup 2#u8 (by decide)] using hf2
    · simpa [lookup 3#u8 (by decide)] using hf3
    · simpa [lookup 4#u8 (by decide)] using hf4
    · simpa [lookup 5#u8 (by decide)] using hf5
    · simpa [lookup 6#u8 (by decide)] using hf6
    · simpa [lookup 7#u8 (by decide)] using hf7
    · simpa [lookup 8#u8 (by decide)] using hf8
    · simpa [lookup 9#u8 (by decide)] using hf9
    · simpa [lookup 12#u8 (by decide)] using hfCount
    · simpa [lookup 10#u8 (by decide)] using hf10
    · simpa [lookup 11#u8 (by decide)] using hf11

/-- A byte string encodes at most one raw module, with no typing or implementation limit premise. -/
theorem ModuleEncodingWith.unique {codeRel x y bytes}
    (hcode : PrefixUnique codeRel)
    (hx : ModuleEncodingWith codeRel x bytes)
    (hy : ModuleEncodingWith codeRel y bytes) : x = y := by
  obtain ⟨xs, hxs, hxf⟩ := hx.sections
  obtain ⟨ys, hys, hyf⟩ := hy.sections
  have he := SectionDecode.unique hxs hys
  subst ys
  have h_types := SectionDecode.Field.unique funcType_prefix_unique.vec.unique hxf.types hyf.types
  have h_imports := SectionDecode.Field.unique import_prefix_unique.vec.unique hxf.imports hyf.imports
  have h_functions := SectionDecode.Field.unique index_prefix_unique.vec.unique hxf.functions hyf.functions
  have h_tables := SectionDecode.Field.unique tableType_prefix_unique.vec.unique hxf.tables hyf.tables
  have h_memories := SectionDecode.Field.unique memType_prefix_unique.vec.unique hxf.memories hyf.memories
  have h_globals := SectionDecode.Field.unique global_prefix_unique.vec.unique hxf.globals hyf.globals
  have h_exports := SectionDecode.Field.unique export_prefix_unique.vec.unique hxf.exports hyf.exports
  have h_start := SectionDecode.Field.unique start_prefix_unique.unique hxf.start hyf.start
  have h_elements := SectionDecode.Field.unique elementFor_prefix_unique.vec.unique hxf.elements hyf.elements
  have h_count := SectionDecode.Field.unique start_prefix_unique.unique hxf.dataCount hyf.dataCount
  have h_codes := SectionDecode.Field.unique hcode.vec.unique hxf.codes hyf.codes
  have h_data := SectionDecode.Field.unique dataFor_prefix_unique.vec.unique hxf.data hyf.data
  cases x; cases y; simp_all

end Itasca.ModuleBinary

end
