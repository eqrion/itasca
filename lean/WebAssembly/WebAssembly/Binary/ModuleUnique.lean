import WebAssembly.Binary.Module
import WebAssembly.Binary.LebUnique

namespace WebAssembly.Binary

def PrefixUnique {α : Type} (R : α → List UInt8 → Prop) : Prop :=
  ∀ ⦃x y a b rest tail⦄, R x a → R y b → a ++ rest = b ++ tail →
    x = y ∧ a = b ∧ rest = tail

theorem IndexEncoding.prefix_unique : PrefixUnique IndexEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := Leb128.UnsignedForm.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

theorem LocalEncoding.prefix_unique : PrefixUnique LocalEncoding := by
  rintro ⟨m, x⟩ ⟨n, y⟩ a b rest tail ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ eq
  obtain ⟨rfl, rfl, suffix⟩ := IndexEncoding.prefix_unique hu hv (by simpa [List.append_assoc] using eq)
  obtain ⟨ht, rfl⟩ := List.cons.inj suffix
  have same : x = y := by cases x <;> cases y <;> first | rfl | contradiction
  subst y
  exact ⟨rfl, rfl, rfl⟩

theorem ReferencesBinary.Immediate.prefix_unique (opcode : UInt8) :
    PrefixUnique (ReferencesBinary.Immediate opcode) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case refNull.refNull =>
    rename_i x y
    obtain ⟨hv, rfl⟩ := List.cons.inj he
    have heq : x = y := by cases x <;> cases y <;> first | rfl | contradiction
    subst y
    exact ⟨rfl, rfl, rfl⟩
  case refIsNull.refIsNull => exact ⟨rfl, rfl, he⟩
  case refFunc.refFunc | tableGet.tableGet | tableSet.tableSet =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := IndexEncoding.prefix_unique hx hy he
    obtain rfl := hv
    exact ⟨rfl, rfl, rfl⟩
  case selectTyped.selectTyped =>
    rename_i x count hx y count' hy
    obtain ⟨_, rfl, hrest⟩ := IndexEncoding.prefix_unique hx hy (by simpa [List.append_assoc] using he)
    obtain ⟨hv, rfl⟩ := List.cons.inj hrest
    have same : x = y := by cases x <;> cases y <;> first | rfl | contradiction
    subst y
    exact ⟨rfl, rfl, rfl⟩
  case callIndirect.callIndirect =>
    rename_i tx ix tbs ibs ht hi ty iy tbs' ibs' ht' hi'
    obtain ⟨hv, rfl, hrest⟩ := IndexEncoding.prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨hv', rfl, rfl⟩ := IndexEncoding.prefix_unique hi hi' hrest
    obtain rfl := hv
    obtain rfl := hv'
    exact ⟨rfl, rfl, rfl⟩

theorem BulkBinary.Immediate.prefix_unique (opcode : Nat) :
    PrefixUnique (BulkBinary.Immediate opcode) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case memoryInit.memoryInit =>
    rename_i x bs hx y bs' hy
    obtain ⟨hv, rfl, hrest⟩ := IndexEncoding.prefix_unique hx hy (by simpa [List.append_assoc] using he)
    obtain rfl := hv
    exact ⟨rfl, rfl, (List.cons.inj hrest).2⟩
  case dataDrop.dataDrop | elemDrop.elemDrop | tableGrow.tableGrow |
      tableSize.tableSize | tableFill.tableFill =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := IndexEncoding.prefix_unique hx hy he
    obtain rfl := hv
    exact ⟨rfl, rfl, rfl⟩
  case memoryCopy.memoryCopy => exact ⟨rfl, rfl, (List.cons.inj (List.cons.inj he).2).2⟩
  case memoryFill.memoryFill => exact ⟨rfl, rfl, (List.cons.inj he).2⟩
  case tableInit.tableInit | tableCopy.tableCopy =>
    rename_i ax bx abs bbs ha hb ay by_ abs' bbs' ha' hb'
    obtain ⟨hv, rfl, hrest⟩ := IndexEncoding.prefix_unique ha ha' (by simpa [List.append_assoc] using he)
    obtain ⟨hv', rfl, rfl⟩ := IndexEncoding.prefix_unique hb hb' hrest
    obtain rfl := hv
    obtain rfl := hv'
    exact ⟨rfl, rfl, rfl⟩

theorem LimitsEncoding.nonempty {ty bs} (h : LimitsEncoding ty bs) : bs ≠ [] := by
  cases h <;> simp

theorem LimitsEncoding.prefix_unique : PrefixUnique LimitsEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  case noMax.noMax x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := IndexEncoding.prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case max.max x xmax a b hx hm y ymax c d hy hn =>
    obtain ⟨rfl, rfl, ht⟩ := IndexEncoding.prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain ⟨rfl, rfl, rfl⟩ := IndexEncoding.prefix_unique hm hn ht
    exact ⟨rfl, rfl, rfl⟩
  all_goals have := he.1; contradiction

theorem split_of_length {α : Type} {xs ys rest tail : List α}
    (he : xs ++ rest = ys ++ tail) (hl : xs.length = ys.length) :
    xs = ys ∧ rest = tail := by
  have h := congrArg (List.take xs.length) he
  have hx : xs = ys := by simpa [List.take_append, hl] using h
  subst ys
  exact ⟨rfl, List.append_cancel_left he⟩

theorem float_prefix_unique (n : Nat) :
    PrefixUnique (fun bits bs => FloatBits.Encoding n bs bits) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := split_of_length he (hx.1.trans hy.1.symm)
  exact ⟨hx.2.trans hy.2.symm, rfl, rfl⟩

private theorem signed_prefix_unique (n : Nat) (lo hi : Int) :
    PrefixUnique (fun v bs => Leb128.SignedWith UInt8.toNat n lo hi bs v) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := Leb128.SignedForm.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

private theorem reference_byte_injective {a b : reftype}
    (h : ReferencesBinary.referenceByte a = ReferencesBinary.referenceByte b) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

theorem TableTypeEncoding.prefix_unique : PrefixUnique TableTypeEncoding := by
  intro ⟨x, rx⟩ ⟨y, ry⟩ a b rest tail hx hy he
  obtain ⟨_, hx, rfl⟩ := hx
  obtain ⟨_, hy, rfl⟩ := hy
  obtain ⟨hr, hs⟩ := List.cons.inj he
  obtain rfl := reference_byte_injective hr
  obtain ⟨rfl, rfl, rfl⟩ := LimitsEncoding.prefix_unique hx hy hs
  exact ⟨rfl, rfl, rfl⟩

theorem MemTypeEncoding.prefix_unique : PrefixUnique MemTypeEncoding := by
  intro ⟨x⟩ ⟨y⟩ a b rest tail hx hy he
  obtain ⟨rfl, rfl, rfl⟩ := LimitsEncoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, rfl⟩

theorem ConstEncoding.nonempty {e bs} (h : ConstEncoding e bs) : bs ≠ [] := by
  cases h <;> simp

theorem ConstEncoding.prefix_unique : PrefixUnique ConstEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  case i32.i32 x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := signed_prefix_unique _ _ _ hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case i64.i64 x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := signed_prefix_unique _ _ _ hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case f32.f32 x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := float_prefix_unique 4 hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case f64.f64 x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := float_prefix_unique 8 hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case globalGet.globalGet x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := IndexEncoding.prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case refFunc.refFunc x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := IndexEncoding.prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case refNull.refNull x y =>
    obtain rfl := reference_byte_injective he.2.1
    exact ⟨rfl, rfl, he.2.2.2⟩
  case v128.v128 low high sub first second hs hl hh low' high' sub' first' second' hs' hl' hh' =>
    obtain ⟨_, rfl, hseq1⟩ := IndexEncoding.prefix_unique hs hs' (by simpa [List.append_assoc] using he.2)
    obtain ⟨rfl, rfl, hseq2⟩ := float_prefix_unique 8 hl hl' (by simpa [List.append_assoc] using hseq1)
    obtain ⟨rfl, rfl, hseq3⟩ := float_prefix_unique 8 hh hh' (by simpa [List.append_assoc] using hseq2)
    obtain rfl := (List.cons.inj hseq3).2
    exact ⟨rfl, rfl, rfl⟩

theorem GlobalTypeEncoding.prefix_unique : PrefixUnique GlobalTypeEncoding := by
  intro ⟨mx, tx⟩ ⟨my, ty⟩ a b rest tail hx hy he
  obtain ⟨vx, rfl, rfl⟩ := hx
  obtain ⟨vy, rfl, rfl⟩ := hy
  obtain ⟨hv, h⟩ := List.cons.inj he
  obtain ⟨hm, rfl⟩ := List.cons.inj h
  have hv' : vx = vy := by cases vx <;> cases vy <;> first | rfl | contradiction
  subst vy
  cases mx <;> cases my <;> simp_all [mutabilityByte]

/-- Import descriptor encodings are prefix-unique. -/
theorem ImportDescEncoding.prefix_unique : PrefixUnique ImportDescEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  case func.func x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := IndexEncoding.prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case table.table x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := TableTypeEncoding.prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case memory.memory x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := MemTypeEncoding.prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case global.global x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := GlobalTypeEncoding.prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩

/-- Export descriptor encodings are prefix-unique. -/
theorem ExportDescEncoding.prefix_unique : PrefixUnique ExportDescEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  all_goals
    rename_i x a hx y b hy
    obtain ⟨rfl, rfl, rfl⟩ := IndexEncoding.prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩

/-- Prefix uniqueness extends to sequences of the same length. -/
theorem PrefixUnique.rep {α : Type} {R : α → List UInt8 → Prop} (h : PrefixUnique R)
    {xs ys first second rest tail} (hx : Rep R xs first) (hy : Rep R ys second)
    (hl : xs.length = ys.length) (he : first ++ rest = second ++ tail) :
    xs = ys ∧ first = second ∧ rest = tail := by
  induction hx generalizing ys second with
  | nil =>
    cases hy with
    | nil => exact ⟨rfl, rfl, he⟩
    | cons => simp at hl
  | @cons x xs a b ha hb ih =>
    cases hy with
    | nil => simp at hl
    | @cons y ys c d hc hd =>
      obtain ⟨rfl, rfl, ht⟩ := h ha hc (by simpa [List.append_assoc] using he)
      obtain ⟨rfl, rfl, rfl⟩ := ih hd (by simpa using hl) ht
      exact ⟨rfl, rfl, rfl⟩

/-- Vector encodings of a prefix-unique relation are prefix-unique. -/
theorem PrefixUnique.vec {α : Type} {R : α → List UInt8 → Prop}
    (h : PrefixUnique R) : PrefixUnique (VecEncoding R) := by
  intro xs ys a b rest tail hx hy he
  obtain ⟨n, entries, hn, hx, rfl⟩ := hx
  obtain ⟨m, entries', hm, hy, rfl⟩ := hy
  obtain ⟨hl, rfl, ht⟩ := IndexEncoding.prefix_unique hn hm (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := h.rep hx hy hl ht
  exact ⟨rfl, rfl, rfl⟩

/-- Raw byte encodings are prefix-unique. -/
theorem byte_prefix_unique : PrefixUnique (@ByteEncoding UInt8) := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨rfl, rfl⟩ := List.cons.inj he
  exact ⟨rfl, rfl, rfl⟩

/-- Name encodings are prefix-unique. -/
theorem NameEncoding.prefix_unique : PrefixUnique NameEncoding := by
  intro x y a b rest tail hx hy he
  exact byte_prefix_unique.vec hx.1 hy.1 he

/-- Import encodings are prefix-unique. -/
theorem ImportEncoding.prefix_unique : PrefixUnique ImportEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xm, xn, xd, hm, hn, hd, rfl⟩ := hx
  obtain ⟨ym, yn, yd, hm', hn', hd', rfl⟩ := hy
  obtain ⟨hmv, rfl, hseq1⟩ := NameEncoding.prefix_unique hm hm' (by simpa [List.append_assoc] using he)
  obtain ⟨hnv, rfl, hseq2⟩ := NameEncoding.prefix_unique hn hn' (by simpa [List.append_assoc] using hseq1)
  obtain ⟨hdv, rfl, rfl⟩ := ImportDescEncoding.prefix_unique hd hd' hseq2
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

/-- Export encodings are prefix-unique. -/
theorem ExportEncoding.prefix_unique : PrefixUnique ExportEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xn, xd, hn, hd, rfl⟩ := hx
  obtain ⟨yn, yd, hn', hd', rfl⟩ := hy
  obtain ⟨hnv, rfl, hseq1⟩ := NameEncoding.prefix_unique hn hn' (by simpa [List.append_assoc] using he)
  obtain ⟨hdv, rfl, rfl⟩ := ExportDescEncoding.prefix_unique hd hd' hseq1
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

/-- Global encodings are prefix-unique. -/
theorem GlobalEncoding.prefix_unique : PrefixUnique GlobalEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xt, xe, ht, he', rfl⟩ := hx
  obtain ⟨yt, ye, ht', he'', rfl⟩ := hy
  obtain ⟨htv, rfl, hseq1⟩ := GlobalTypeEncoding.prefix_unique ht ht' (by simpa [List.append_assoc] using he)
  obtain ⟨hev, rfl, rfl⟩ := ConstEncoding.prefix_unique he' he'' hseq1
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

theorem InitializerEncoding.prefix_unique (expressions : Bool) : PrefixUnique (InitializerEncoding expressions) := by
  cases expressions with
  | true => exact ConstEncoding.prefix_unique
  | false =>
    rintro x y a b rest tail ⟨i, rfl, hi⟩ ⟨j, rfl, hj⟩ eq
    obtain ⟨rfl, rfl, rfl⟩ := IndexEncoding.prefix_unique hi hj eq
    exact ⟨rfl, rfl, rfl⟩

theorem ElementHeaderEncoding.prefix_unique :
    PrefixUnique (fun (p : ElementMode × reftype × Bool) => ElementHeaderEncoding p.1 p.2.1 p.2.2) := by
  rintro ⟨mx, rx, ex⟩ ⟨my, ry, ey⟩ a b rest tail hx hy eq
  cases hx
  case' activeIndices hf ho => skip
  case' passiveIndices hf => skip
  case' explicitIndices hf hi ho => skip
  case' declarativeIndices hf => skip
  case' activeExpressions hf ho => skip
  case' passiveExpressions hf => skip
  case' explicitExpressions hf hi ho => skip
  case' declarativeExpressions hf => skip
  all_goals
    cases hy
    case' activeIndices hf' ho' => skip
    case' passiveIndices hf' => skip
    case' explicitIndices hf' hi' ho' => skip
    case' declarativeIndices hf' => skip
    case' activeExpressions hf' ho' => skip
    case' passiveExpressions hf' => skip
    case' explicitExpressions hf' hi' ho' => skip
    case' declarativeExpressions hf' => skip
  all_goals simp only [List.append_assoc, List.singleton_append] at eq
  all_goals obtain ⟨flagEq, rfl, suffix⟩ := IndexEncoding.prefix_unique hf hf' eq
  all_goals try contradiction
  all_goals try
    have next := IndexEncoding.prefix_unique hi hi' suffix
    clear suffix
    obtain ⟨rfl, rfl, suffix⟩ := next
  all_goals try
    have next := ConstEncoding.prefix_unique ho ho' suffix
    clear suffix
    obtain ⟨rfl, rfl, suffix⟩ := next
  all_goals first
    | exact ⟨rfl, rfl, suffix⟩
    | exact ⟨rfl, rfl, (List.cons.inj suffix).2⟩
    | obtain ⟨href, ht⟩ := List.cons.inj suffix
      have inj {x y} (h : ReferencesBinary.referenceByte x = ReferencesBinary.referenceByte y) : x = y := by
        cases x <;> cases y <;> first | rfl | contradiction
      obtain rfl := inj href
      exact ⟨rfl, rfl, ht⟩

theorem ElementEncoding.prefix_unique : PrefixUnique ElementEncoding := by
  rintro ⟨rx, mx, xs⟩ ⟨ry, my, ys⟩ a b rest tail ⟨ex, h, i, hh, hi, rfl⟩ ⟨ey, k, j, hk, hj, rfl⟩ eq
  obtain ⟨hp, rfl, suffix⟩ := ElementHeaderEncoding.prefix_unique (x := (mx,rx,ex))
    (y := (my,ry,ey)) hh hk (by simpa only [List.append_assoc] using eq)
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj hp |>.imp_right Prod.mk.inj
  obtain ⟨rfl, rfl, rfl⟩ := (InitializerEncoding.prefix_unique _).vec hi hj suffix
  exact ⟨rfl, rfl, rfl⟩

theorem ElementHeaderEncoding.nonempty {m t ex bs} (h : ElementHeaderEncoding m t ex bs) :
    0 < bs.length := by
  have leb {n bs} (h : IndexEncoding n bs) : 0 < bs.length := by
    obtain ⟨pre, last, rfl, _⟩ := h
    simp
  cases h with
  | activeIndices hf _ | explicitIndices hf _ _ | activeExpressions hf _ | explicitExpressions hf _ _
  | passiveIndices hf | declarativeIndices hf | passiveExpressions hf | declarativeExpressions hf =>
    have := leb hf
    simp only [List.length_append]
    omega

theorem DataEncoding.prefix_unique : PrefixUnique DataEncoding := by
  intro x y a b rest tail hx hy eq
  cases hx
  case' active ix ho hv =>
    cases ix
    case' implicit hf => skip
    case' explicit hf hi => skip
  case' passive hf hv => skip
  all_goals
    cases hy
    case' active iy ho' hv' =>
      cases iy
      case' implicit hf' => skip
      case' explicit hf' hi' => skip
    case' passive hf' hv' => skip
  all_goals simp only [List.append_assoc] at eq
  all_goals obtain ⟨flagEq, rfl, suffix⟩ := IndexEncoding.prefix_unique hf hf' eq
  all_goals try contradiction
  all_goals try
    have hn := IndexEncoding.prefix_unique hi hi' suffix
    clear suffix
    obtain ⟨rfl, rfl, suffix⟩ := hn
  all_goals try
    have hn := ConstEncoding.prefix_unique ho ho' suffix
    clear suffix
    obtain ⟨rfl, rfl, suffix⟩ := hn
  all_goals obtain ⟨rfl, rfl, rfl⟩ := byte_prefix_unique.vec hv hv' suffix
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem DataEncoding.length_ge_two {d raw} (h : DataEncoding d raw) : 2 ≤ raw.length := by
  have leb {n bs} (h : WebAssembly.Binary.IndexEncoding n bs) : 1 ≤ bs.length := by
    obtain ⟨pre, last, rfl, _⟩ := h
    simp
  have vec {xs bs} (h : WebAssembly.Binary.ByteVecEncoding xs bs) : 1 ≤ bs.length := by
    obtain ⟨count, entries, hc, _, rfl⟩ := h
    have := leb hc
    simp only [List.length_append]
    omega
  cases h with
  | active hi _ he =>
    have vh := vec he
    cases hi with
    | implicit hf | explicit hf _ =>
      have := leb hf
      simp only [List.length_append]
      omega
  | passive hf he =>
    have := leb hf
    have := vec he
    simp only [List.length_append]
    omega

theorem DataEncoding.init_vector {d raw} (h : DataEncoding d raw) :
    ∃ bs, ByteVecEncoding d.init bs := by
  cases h with
  | active _ _ hi | passive _ hi => exact ⟨_, hi⟩

end WebAssembly.Binary

