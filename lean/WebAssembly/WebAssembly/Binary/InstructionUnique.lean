import WebAssembly.Binary.ModuleFraming

namespace WebAssembly.Binary.Scalar
/-- An index vector is a sequence of `IndexEncoding`s. -/
theorem IndicesEncoding.rep {indices bytes} (h : IndicesEncoding indices bytes) :
    Rep IndexEncoding indices bytes := by
  induction h with
  | nil => exact .nil
  | cons hn _ ih => exact .cons hn ih

private theorem signedPrefix32 : PrefixUnique (fun i bs => Leb128.S32Encoding bs i) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := Leb128.SignedForm.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

private theorem signedPrefix64 : PrefixUnique (fun i bs => Leb128.S64Encoding bs i) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := Leb128.SignedForm.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

private theorem numeric_bounds {opcode op} (h : Numeric.opcodeInstruction opcode = some op) :
    0x45 ≤ opcode.toNat ∧ opcode.toNat < 0xc0 := by
  unfold Numeric.opcodeInstruction at h
  split at h <;> first | contradiction | omega

private theorem memory_bounds {opcode op} (h : MemoryMeaning.opcodeMeaning opcode = some op) :
    0x28 ≤ opcode.toNat ∧ opcode.toNat ≤ 0x3e := by
  unfold MemoryMeaning.opcodeMeaning MemoryMeaning.opcodeTable at h
  split at h <;> first | contradiction | omega

set_option maxHeartbeats 1200000 in
/-- The immediate bytes of a token are determined by its opcode and leading bytes. -/
theorem Immediate.prefix_unique (opcode : UInt8) : PrefixUnique (Immediate opcode) := by
  intro t u bs cs rest tail ht hu heq
  unfold Immediate at ht hu
  cases ht <;> cases hu
  all_goals try { contradiction }
  all_goals try { exact ⟨rfl, rfl, heq⟩ }
  case br.br | brIf.brIf | call.call | localGet.localGet | localSet.localSet |
      localTee.localTee | globalGet.globalGet | globalSet.globalSet =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := IndexEncoding.prefix_unique hx hy heq
    obtain rfl := hv
    exact ⟨rfl, rfl, rfl⟩
  case brTable.brTable =>
    rename_i xs x count entries final hn he hf ys y count' entries' final' hn' he' hf'
    obtain ⟨hl, rfl, hrest⟩ := IndexEncoding.prefix_unique hn hn' (by simpa [List.append_assoc] using heq)
    obtain ⟨rfl, rfl, hentries⟩ := IndexEncoding.prefix_unique.rep (IndicesEncoding.rep he) (IndicesEncoding.rep he') hl
      (by simpa [List.append_assoc] using hrest)
    obtain ⟨rfl, rfl, rfl⟩ := IndexEncoding.prefix_unique hf hf' hentries
    exact ⟨rfl, rfl, rfl⟩
  case callIndirect.callIndirect =>
    rename_i x bytes hx y bytes' hy
    obtain ⟨rfl, rfl, hrest⟩ := IndexEncoding.prefix_unique hx hy (by simpa [List.append_assoc] using heq)
    obtain rfl := (List.cons.inj hrest).2
    exact ⟨rfl, rfl, rfl⟩
  case memory.memory =>
    rename_i m arg align offset ha ho hm n arg' align' offset' ha' ho' hn
    obtain ⟨a,b⟩ := arg
    obtain ⟨c,d⟩ := arg'
    change Leb128.U32Encoding _ a at ha
    change Leb128.U32Encoding _ c at ha'
    change Leb128.U32Encoding _ b at ho
    change Leb128.U32Encoding _ d at ho'
    obtain rfl := Option.some.inj (hm.symm.trans hn)
    obtain ⟨rfl, rfl, hrest⟩ := IndexEncoding.prefix_unique ha ha' (by simpa [List.append_assoc] using heq)
    obtain ⟨rfl, rfl, rfl⟩ := IndexEncoding.prefix_unique ho ho' hrest
    exact ⟨rfl, rfl, rfl⟩
  case memory.numericInstruction | numericInstruction.memory =>
    have := numeric_bounds (by assumption : Numeric.opcodeInstruction opcode = some _)
    have := memory_bounds (by assumption : MemoryMeaning.opcodeMeaning opcode = some _)
    omega
  case numericInstruction.numericInstruction =>
    rename_i hm hn
    obtain rfl := Option.some.inj (hm.symm.trans hn)
    exact ⟨rfl, rfl, heq⟩
  case memorySize.memorySize | memoryGrow.memoryGrow =>
    exact ⟨rfl, rfl, (List.cons.inj heq).2⟩
  case i32Const.i32Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := signedPrefix32 hx hy heq
    obtain rfl := hv
    exact ⟨rfl, rfl, rfl⟩
  case i64Const.i64Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := signedPrefix64 hx hy heq
    obtain rfl := hv
    exact ⟨rfl, rfl, rfl⟩
  case f32Const.f32Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := float_prefix_unique 4 hx hy heq
    obtain rfl := hv
    exact ⟨rfl, rfl, rfl⟩
  case f64Const.f64Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := float_prefix_unique 8 hx hy heq
    obtain rfl := hv
    exact ⟨rfl, rfl, rfl⟩

end WebAssembly.Binary.Scalar

namespace WebAssembly.Binary.Simd
private theorem pure_lane_disjoint {n op lane} (hp : pureInstruction n = some op)
    (hl : laneMeaning n = some lane) : False := by
  unfold laneMeaning at hl
  split at hl <;> contradiction

private theorem pure_memory_disjoint {n op mem} (hp : pureInstruction n = some op)
    (hm : memoryMeaning n = some mem) : False := by
  unfold memoryMeaning at hm
  split at hm <;> contradiction

private theorem lane_memory_disjoint {n lane mem} (hl : laneMeaning n = some lane)
    (hm : memoryMeaning n = some mem) : False := by
  unfold memoryMeaning at hm
  split at hm <;> contradiction

/-- SIMD immediates are prefix-unique. -/
theorem Immediate.prefix_unique (subopcode : Nat) : PrefixUnique (Immediate subopcode) := by
  intro t u bs cs rest tail ht hu heq
  cases ht <;> cases hu
  all_goals try { contradiction }
  all_goals try { exact False.elim (pure_lane_disjoint ‹_› ‹_›) }
  all_goals try { exact False.elim (pure_memory_disjoint ‹_› ‹_›) }
  all_goals try { exact False.elim (lane_memory_disjoint ‹_› ‹_›) }
  case pure.pure =>
    rename_i hp hp'
    exact ⟨Option.some.inj (hp.symm.trans hp'), rfl, heq⟩
  case lane.lane =>
    rename_i op lane hp op' lane' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    exact ⟨rfl, rfl, rfl⟩
  case memory.memory =>
    rename_i op arg align offset hc ha ho hp op' arg' align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    obtain ⟨haeq, rfl, hrest⟩ := IndexEncoding.prefix_unique ha ha' (by simpa [List.append_assoc] using heq)
    obtain ⟨hoeq, rfl, rfl⟩ := IndexEncoding.prefix_unique ho ho' hrest
    have same : arg = arg' := Prod.ext haeq hoeq
    subst arg'
    exact ⟨rfl, rfl, rfl⟩
  case memory.memoryLane =>
    rename_i op arg align offset hc ha ho hp op' arg' lane align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact False.elim (hc' hc)
  case memoryLane.memory =>
    rename_i op arg lane align offset hc ha ho hp op' arg' align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact False.elim (hc hc')
  case memoryLane.memoryLane =>
    rename_i op arg lane align offset hc ha ho hp op' arg' lane' align' offset' hc' ha' ho' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    obtain ⟨haeq, rfl, hrest⟩ := IndexEncoding.prefix_unique ha ha' (by simpa [List.append_assoc] using heq)
    obtain ⟨hoeq, rfl, htail⟩ := IndexEncoding.prefix_unique ho ho' (by simpa [List.append_assoc] using hrest)
    obtain ⟨rfl, rfl⟩ := List.cons.inj htail
    have same : arg = arg' := Prod.ext haeq hoeq
    subst arg'
    exact ⟨rfl, rfl, rfl⟩
  case constant.constant | shuffle.shuffle =>
    rename_i low high lower upper hlo hhi low' high' lower' upper' hlo' hhi'
    obtain ⟨hloeq, rfl, hrest⟩ := float_prefix_unique 8 hlo hlo' (by simpa [List.append_assoc] using heq)
    obtain ⟨hhieq, rfl, rfl⟩ := float_prefix_unique 8 hhi hhi' hrest
    obtain rfl := hloeq
    obtain rfl := hhieq
    exact ⟨rfl, rfl, rfl⟩


end WebAssembly.Binary.Simd

namespace WebAssembly.Binary

private theorem index_tag_disjoint {n : Nat} {bytes rest tail : List UInt8} {tag : UInt8}
    (h : Leb128.S33Encoding bytes n) (eq : bytes ++ rest = tag :: tail)
    (lo : 64 ≤ tag.toNat) (hi : tag.toNat < 128) : False := by
  obtain ⟨before, last, rfl, _, hb, _, hv, _⟩ := h
  cases before with
  | nil =>
    obtain rfl := (List.cons.inj eq).1
    simp [Leb128.signedFinal, Leb128.payloadWith, *] at hv
    omega
  | cons b bs =>
    have := hb b (by simp)
    obtain rfl := (List.cons.inj eq).1
    omega

theorem BlockEncoding.prefix_unique : PrefixUnique BlockEncoding := by
  have range (t : ValueType) : 64 ≤ (valueByte t).toNat ∧ (valueByte t).toNat < 128 := by cases t <;> decide
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case empty.empty => exact ⟨rfl, rfl, (List.cons.inj he).2⟩
  case empty.result t | result.empty t =>
    have eq := (List.cons.inj he).1
    cases t <;> contradiction
  case result.result x y =>
    obtain ⟨eq, rfl⟩ := List.cons.inj he
    have h : x = y := by cases x <;> cases y <;> first | rfl | contradiction
    subst y
    exact ⟨rfl, rfl, rfl⟩
  case empty.index i hi => exact False.elim (index_tag_disjoint hi he.symm (by decide) (by decide))
  case index.empty i hi => exact False.elim (index_tag_disjoint hi he (by decide) (by decide))
  case result.index t i hi => exact False.elim (index_tag_disjoint hi he.symm (range t).1 (range t).2)
  case index.result i hi t => exact False.elim (index_tag_disjoint hi he (range t).1 (range t).2)
  case index.index i hi j hj =>
    obtain ⟨rfl, hv⟩ := Leb128.SignedForm.prefix_unique hi hj he
    have eq : i = j := by omega
    subst j
    exact ⟨rfl, rfl, List.append_cancel_left he⟩

end WebAssembly.Binary

namespace WebAssembly.Binary
private theorem plain_opcode {opcode op bytes} (h : Scalar.Immediate opcode op bytes) :
    opcode.toNat < 192 ∧ opcode.toNat ∉ [2, 3, 4, 5, 11, 28, 37, 38, 208, 209, 210, 252, 253] := by
  unfold Scalar.Immediate at h
  cases h with
  | numericInstruction opcode source hmap =>
    have := Scalar.numeric_bounds hmap
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  | memory opcode op arg hmap ha ho =>
    have := Scalar.memory_bounds hmap
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  | _ => decide

private theorem sign_range {opcode op} (h : NumericExtensions.signInstruction opcode = some op) :
    192 ≤ opcode.toNat ∧ opcode.toNat ≤ 196 := by
  unfold NumericExtensions.signInstruction at h
  split at h <;> simp_all

private theorem saturating_range {opcode op} (h : NumericExtensions.saturatingInstruction opcode = some op) :
    opcode < 8 := by
  unfold NumericExtensions.saturatingInstruction at h
  split at h <;> simp_all

private theorem reference_opcodes {opcode op bytes} (h : ReferencesBinary.Immediate opcode op bytes) :
    opcode.toNat ∈ [17, 28, 37, 38, 208, 209, 210] := by
  cases h <;> decide

private theorem bulk_range {n op bs} (h : BulkBinary.Immediate n op bs) : 8 ≤ n := by
  cases h <;> decide

private theorem plain_reference_prefix {opcode x y a b rest tail}
    (hx : Scalar.Immediate opcode x a) (hy : ReferencesBinary.Immediate opcode y b)
    (he : a ++ rest = b ++ tail) : x = y ∧ a = b ∧ rest = tail := by
  have hop := plain_opcode hx
  have hyr := reference_opcodes hy
  have ho : opcode = 17 := by
    apply UInt8.toNat_inj.mp
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hop hyr
    change opcode.toNat = 17
    omega
  subst opcode
  unfold Scalar.Immediate at hx
  cases hx <;> cases hy
  all_goals try contradiction
  case callIndirect.callIndirect =>
    rename_i idx ibs hi tid tab tbs tabs ht htab
    obtain ⟨hv, rfl, hrest⟩ := IndexEncoding.prefix_unique hi ht (by simpa [List.append_assoc] using he)
    have hz : Leb128.U32Encoding [0] 0 :=
      ⟨[], 0, rfl, by decide, by simp, by decide, by simp, rfl⟩
    obtain ⟨hv', hbs, htail⟩ := IndexEncoding.prefix_unique hz htab hrest
    have htid : idx = tid := hv
    subst tid
    refine ⟨?_, congrArg (ibs ++ ·) hbs, htail⟩
    change 0 = tab at hv'
    subst tab
    rfl

set_option maxHeartbeats 2000000 in
/-- The immediate bytes of a Wasm 2.0 token are determined by its opcode and leading bytes. -/
theorem Immediate.prefix_unique (opcode : UInt8) : PrefixUnique (Immediate opcode) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals try dsimp only [nativeInstructionOperands, id_eq] at *
  all_goals try { exact ⟨rfl, rfl, he⟩ }
  all_goals try { have hb := plain_opcode (by assumption); exact False.elim ((by decide : ¬ _) hb) }
  all_goals try { have hb := sign_range (by assumption); exact False.elim ((by decide : ¬ _) hb) }
  all_goals try { have hb := reference_opcodes (by assumption); exact False.elim ((by decide : ¬ _) hb) }
  case plain.plain =>
    rename_i op hp op' hp'
    obtain ⟨hh, rfl, rfl⟩ := Scalar.Immediate.prefix_unique opcode hp hp' he
    exact ⟨congrArg TokenWith.plain hh, rfl, rfl⟩
  case plain.reference =>
    rename_i op hp op' hp'
    obtain ⟨rfl, rfl, rfl⟩ := plain_reference_prefix hp hp' he
    exact ⟨rfl, rfl, rfl⟩
  case reference.plain =>
    rename_i op hp op' hp'
    obtain ⟨rfl, rfl, rfl⟩ := plain_reference_prefix hp' hp he.symm
    exact ⟨rfl, rfl, rfl⟩
  case signExtensionInstruction.signExtensionInstruction =>
    rename_i op hp op' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact ⟨rfl, rfl, he⟩
  case reference.reference =>
    rename_i op hp op' hp'
    obtain ⟨rfl, rfl, rfl⟩ := ReferencesBinary.Immediate.prefix_unique opcode hp hp' he
    exact ⟨rfl, rfl, rfl⟩
  case saturatingInstruction.saturatingInstruction =>
    rename_i sub op hmap hb sub' op' hmap' hb'
    obtain ⟨hv, rfl, rfl⟩ := IndexEncoding.prefix_unique hb hb' he
    obtain rfl := hv
    obtain rfl := Option.some.inj (hmap.symm.trans hmap')
    exact ⟨rfl, rfl, rfl⟩
  case saturatingInstruction.bulk =>
    rename_i sub op hmap hb sub' pbs op' bs hb' hi
    have hr := saturating_range hmap
    have hr' := bulk_range hi
    obtain ⟨hv, _, _⟩ := IndexEncoding.prefix_unique hb hb' (by simpa [List.append_assoc] using he)
    omega
  case bulk.saturatingInstruction =>
    rename_i sub pbs op bs hb hi sub' op' hmap hb'
    have hr := saturating_range hmap
    have hr' := bulk_range hi
    obtain ⟨hv, _, _⟩ := IndexEncoding.prefix_unique hb hb' (by simpa [List.append_assoc] using he)
    omega
  case bulk.bulk | simd.simd =>
    rename_i sub pbs op bs hb hi sub' pbs' op' bs' hb' hi'
    obtain ⟨hv, rfl, hrest⟩ := IndexEncoding.prefix_unique hb hb' (by simpa [List.append_assoc] using he)
    obtain rfl := hv
    obtain ⟨rfl, rfl, rfl⟩ := (by first
      | exact BulkBinary.Immediate.prefix_unique sub hi hi' hrest
      | exact Simd.Immediate.prefix_unique sub hi hi' hrest)
    exact ⟨rfl, rfl, rfl⟩
  case block.block | loop.loop | if_.if_ =>
    rename_i bt hb bt' hb'
    obtain ⟨rfl, rfl, rfl⟩ := BlockEncoding.prefix_unique hb hb' he
    exact ⟨rfl, rfl, rfl⟩
  all_goals
    first
      | (have hp := plain_opcode (by assumption); have hs := sign_range (by assumption); omega)
      | (have hr := reference_opcodes (by assumption); have hs := sign_range (by assumption)
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega)

/-- Token encodings are prefix-unique. -/
theorem token_prefix_unique : PrefixUnique TokenEncoding := by
  rintro x y a b rest tail ⟨op, ai, rfl, hx⟩ ⟨op', bi, rfl, hy⟩ he
  obtain ⟨rfl, htail⟩ := List.cons.inj he
  obtain ⟨rfl, rfl, rfl⟩ := Immediate.prefix_unique op hx hy htail
  exact ⟨rfl, rfl, rfl⟩

/-- A byte string is the encoding of at most one token sequence. -/
theorem tokens_unique : EncodingUnique (Rep TokenEncoding) :=
  token_prefix_unique.rep_unique (by rintro _ _ ⟨op, immediate, rfl, _⟩; simp)


end WebAssembly.Binary
