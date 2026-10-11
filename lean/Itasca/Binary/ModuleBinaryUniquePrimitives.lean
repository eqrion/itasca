import Itasca.Binary.BinaryPrefix

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem valueByte_injective : Function.Injective valueByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [valueByte]

theorem elemByte_injective : Function.Injective elemByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [elemByte]

theorem elemType_prefix_unique : PrefixUnique ElemTypeEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨hv, rfl⟩ := List.cons.inj he
  obtain rfl := elemByte_injective hv
  exact ⟨rfl, rfl, rfl⟩

theorem mutByte_injective : Function.Injective mutByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [mutByte]

theorem valueType_prefix_unique : PrefixUnique ValueTypeEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨hv, rfl⟩ := List.cons.inj he
  obtain rfl := valueByte_injective hv
  exact ⟨rfl, rfl, rfl⟩

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

theorem tableType_prefix_unique : PrefixUnique TableTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨a, hx, rfl⟩ := hx
  obtain ⟨b, hy, rfl⟩ := hy
  obtain ⟨helem, hrest⟩ := List.cons.inj he
  have helem := elemByte_injective helem
  obtain ⟨hv, rfl, rfl⟩ := limits_prefix_unique hx hy hrest
  have hxy : x = y := by cases x; cases y; simp_all
  exact ⟨hxy, by simp [helem], rfl⟩

theorem memType_prefix_unique : PrefixUnique MemTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨hv, rfl, rfl⟩ := limits_prefix_unique hx hy he
  have hxy : x = y := by cases x; cases y; cases hv; rfl
  exact ⟨hxy, rfl, rfl⟩

theorem globalType_prefix_unique : PrefixUnique GlobalTypeEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨hv, hseq1⟩ := List.cons.inj he
  obtain ⟨hm, rfl⟩ := List.cons.inj hseq1
  have hv := valueByte_injective hv
  have hm := mutByte_injective hm
  have hxy : x = y := by cases x; cases y; simp_all
  exact ⟨hxy, by simp [hv, hm], rfl⟩

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

theorem exportDesc_prefix_unique : PrefixUnique ExportDescEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  all_goals
    rename_i x a hx y b hy
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩

theorem import_prefix_unique : PrefixUnique ImportEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xm, xn, xd, hm, hn, hd, rfl⟩ := hx
  obtain ⟨ym, yn, yd, hm', hn', hd', rfl⟩ := hy
  obtain ⟨hmv, rfl, hseq1⟩ := name_prefix_unique hm hm' (by simpa [List.append_assoc] using he)
  obtain ⟨hnv, rfl, hseq2⟩ := name_prefix_unique hn hn' (by simpa [List.append_assoc] using hseq1)
  obtain ⟨hdv, rfl, rfl⟩ := importDesc_prefix_unique hd hd' hseq2
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

theorem export_prefix_unique : PrefixUnique ExportEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xn, xd, hn, hd, rfl⟩ := hx
  obtain ⟨yn, yd, hn', hd', rfl⟩ := hy
  obtain ⟨hnv, rfl, hseq1⟩ := name_prefix_unique hn hn' (by simpa [List.append_assoc] using he)
  obtain ⟨hdv, rfl, rfl⟩ := exportDesc_prefix_unique hd hd' hseq1
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

theorem global_prefix_unique : PrefixUnique GlobalEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xt, xe, ht, he', rfl⟩ := hx
  obtain ⟨yt, ye, ht', he'', rfl⟩ := hy
  obtain ⟨htv, rfl, hseq1⟩ := globalType_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
  obtain ⟨hev, rfl, rfl⟩ := const_prefix_unique he' he'' hseq1
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

theorem local_prefix_unique : PrefixUnique LocalEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨hn, rfl, hseq1⟩ := index_prefix_unique ha hb (by simpa [List.append_assoc] using he)
  obtain ⟨ht, rfl⟩ := List.cons.inj hseq1
  have ht := valueByte_injective ht
  have hv : x = y := Prod.ext hn ht
  exact ⟨hv, by simp [ht], rfl⟩

theorem element_prefix_unique : PrefixUnique ElementEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xti, xof, xin, xt, xo, xi, rfl, ht, ho, hi, rfl⟩ := hx
  obtain ⟨yti, yof, yin, yt, yo, yi, rfl, ht', ho', hi', rfl⟩ := hy
  obtain ⟨rfl, rfl, hseq1⟩ := index_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, hseq2⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using hseq1)
  obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique.vec hi hi' hseq2
  exact ⟨rfl, rfl, rfl⟩

theorem data_prefix_unique : PrefixUnique DataEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xti, xof, xt, xo, xi, hxm, ht, ho, hi, rfl⟩ := hx
  obtain ⟨yti, yof, yt, yo, yi, hym, ht', ho', hi', rfl⟩ := hy
  obtain ⟨htv, rfl, hseq1⟩ := index_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
  obtain ⟨hov, rfl, hseq2⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using hseq1)
  obtain ⟨hiv, rfl, rfl⟩ := byte_prefix_unique.vec hi hi' hseq2
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

theorem start_prefix_unique : PrefixUnique StartEncoding := by
  rintro x y a b rest tail ⟨xi, rfl, hx⟩ ⟨yi, rfl, hy⟩ he
  obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he
  exact ⟨rfl, rfl, rfl⟩

end Itasca.ModuleBinary
