import Itasca.Binary.ModuleUnique
import Itasca.Binary.Body.Encoding
import Itasca.Binary.Scalar.Encoding
import Itasca.Support.Translation

/-!
Proofs for Binary / Scalar.

This module collects EncodingUnique, MemoryMeaning.
Each section documents its contracts and consumers.
-/

/-! ## EncodingUnique -/

section

/-! ## PrefixUnique -/

section

/-!
# Prefix uniqueness of scalar tokens

`Immediate.prefix_unique` and `token_prefix_unique` show that a scalar token and its encoding
are determined by the leading bytes, and `tokens_unique` extends this to token sequences,
independent of typing and implementation limits.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Scalar

open Binary

/-- An index vector is a sequence of `IndexEncoding`s. -/
theorem IndicesEncoding.rep {indices bytes} (h : IndicesEncoding indices bytes) :
    Rep IndexEncoding indices bytes := by
  induction h with
  | nil => exact .nil
  | cons hn _ ih => exact .cons hn ih

private theorem memory_numeric_disjoint (opcode : U8) (m : Body.MemoryMeaning.Operation)
    (n : instr) (hm : Body.MemoryMeaning.opcodeMeaning opcode = some m)
    (hn : Body.Numeric.opcodeInstruction opcode = some n) : False := by
  rw [Body.Numeric.opcodeInstruction_eq] at hn
  obtain ⟨op, decoded, rfl⟩ := Option.map_eq_some_iff.mp hn
  have hb := Body.Numeric.NumericOp.bounds decoded
  unfold Body.MemoryMeaning.opcodeMeaning at hm
  split at hm <;> (first | contradiction | omega)

set_option maxHeartbeats 1200000 in
/-- The immediate bytes of a token are determined by its opcode and leading bytes. -/
theorem Immediate.prefix_unique (opcode : U8) : PrefixUnique (Immediate opcode) := by
  intro t u bs cs rest tail ht hu heq
  cases ht <;> cases hu
  all_goals try { contradiction }
  all_goals try { exact ⟨rfl, rfl, heq⟩ }
  case block.block | loop.loop | if_.if_ =>
    rename_i _ _ hx _ _ hy
    obtain ⟨hbt, rfl⟩ := List.cons.inj heq
    obtain ⟨rfl, rfl⟩ := hx.unique hy (.inl hbt)
    exact ⟨rfl, rfl, rfl⟩
  case br.br | brIf.brIf | call.call | localGet.localGet | localSet.localSet |
      localTee.localTee | globalGet.globalGet | globalSet.globalSet =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := leb_prefix_unique hx hy heq
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case brTable.brTable =>
    rename_i xs x count entries final hn he hf ys y count' entries' final' hn' he' hf'
    obtain ⟨hl, rfl, hrest⟩ := leb_prefix_unique hn hn' (by simpa [List.append_assoc] using heq)
    obtain ⟨rfl, rfl, hentries⟩ := index_prefix_unique.rep he.rep he'.rep hl
      (by simpa [List.append_assoc] using hrest)
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hf hf' hentries
    exact ⟨rfl, rfl, rfl⟩
  case callIndirect.callIndirect =>
    rename_i x bytes hx y bytes' hy
    obtain ⟨rfl, rfl, hrest⟩ := index_prefix_unique hx hy (by simpa [List.append_assoc] using heq)
    obtain rfl := (List.cons.inj hrest).2
    exact ⟨rfl, rfl, rfl⟩
  case memory.memory =>
    rename_i m a align offset ha ho hm n b align' offset' ha' ho' hn
    obtain rfl := Option.some.inj (hm.symm.trans hn)
    obtain ⟨haeq, rfl, hrest⟩ := leb_prefix_unique ha ha' (by simpa [List.append_assoc] using heq)
    obtain ⟨hoeq, rfl, rfl⟩ := leb_prefix_unique ho ho' hrest
    have haeq := UScalar.eq_of_val_eq haeq
    have hoeq := UScalar.eq_of_val_eq hoeq
    have hab : a = b := by cases a; cases b; simp_all
    subst b
    exact ⟨rfl, rfl, rfl⟩
  case memory.numericInstruction =>
    rename_i m a align offset ha ho hm n hn
    exact False.elim (memory_numeric_disjoint opcode m n hm hn)
  case numericInstruction.memory =>
    rename_i n hn m a align offset ha ho hm
    exact False.elim (memory_numeric_disjoint opcode m n hm hn)
  case numericInstruction.numericInstruction =>
    rename_i m hm n hn
    obtain rfl := Option.some.inj (hm.symm.trans hn)
    exact ⟨rfl, rfl, heq⟩
  case memorySize.memorySize | memoryGrow.memoryGrow =>
    exact ⟨rfl, rfl, (List.cons.inj heq).2⟩
  case i32Const.i32Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := signed32_prefix_unique hx hy heq
    obtain rfl := IScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case i64Const.i64Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := signed64_prefix_unique hx hy heq
    obtain rfl := IScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case f32Const.f32Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := float_prefix_unique 4 hx hy heq
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case f64Const.f64Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := float_prefix_unique 8 hx hy heq
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩

/-- Token encodings are prefix-unique. -/
theorem token_prefix_unique : PrefixUnique TokenEncoding := by
  rintro x y a b rest tail ⟨op, ai, rfl, hx⟩ ⟨op', bi, rfl, hy⟩ he
  obtain ⟨rfl, htail⟩ := List.cons.inj he
  obtain ⟨rfl, rfl, rfl⟩ := Immediate.prefix_unique op hx hy htail
  exact ⟨rfl, rfl, rfl⟩

/-- A byte string is the encoding of at most one token sequence. -/
theorem tokens_unique : Unique (Rep TokenEncoding) :=
  token_prefix_unique.rep_unique (by rintro _ _ ⟨op, immediate, rfl, _⟩; simp)

end Itasca.Body.Scalar

end

/-! ## EncodingUnique -/

section

/-!
# Uniqueness of scalar decoding at a cursor

Shows that LEB128 indices and `br_table` label vectors determine their decoded values
(`Binary.Leb128.Decoded.unique`, `Body.BrTable.LabelsDecoded.unique`, `Body.BrTable.Decoded.unique`).
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A decoded unsigned LEB128 value and cursor are determined by the start. -/
theorem Binary.Leb128.Decoded.unique {data start x y next last}
    (hx : Binary.Leb128.Decoded data start x next) (hy : Binary.Leb128.Decoded data start y last) :
    x = y ∧ next = last :=
  Binary.Leb128.Decoded.deterministic data start x y next last hx hy

/-- A label run of known length is determined by the start. -/
theorem Body.BrTable.LabelsDecoded.unique {data start xs ys next last}
    (hx : Body.BrTable.LabelsDecoded data start xs next)
    (hy : Body.BrTable.LabelsDecoded data start ys last) (hlen : xs.length = ys.length) :
    xs = ys ∧ next = last := by
  have empty : ∀ {p q}, Body.BrTable.LabelsDecoded data p [] q → q = p := by
    intro p q h
    generalize he : [] = zs at h
    cases h with
    | nil => rfl
    | snoc => simp at he
  induction xs generalizing start ys with
  | nil =>
      have he : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst ys
      exact ⟨rfl, (empty hx).trans (empty hy).symm⟩
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          obtain ⟨p, hxp, hxs⟩ := Body.BrTable.LabelsDecoded.cons_iff.mp hx
          obtain ⟨q, hyq, hys⟩ := Body.BrTable.LabelsDecoded.cons_iff.mp hy
          obtain ⟨rfl, rfl⟩ := hxp.unique hyq
          obtain ⟨rfl, rfl⟩ := ih hxs hys (by simpa using hlen)
          exact ⟨rfl, rfl⟩

/-- A decoded `br_table` immediate is determined by the start. -/
theorem Body.BrTable.Decoded.unique {data start xs ys x y next last}
    (hx : Body.BrTable.Decoded data start xs x next) (hy : Body.BrTable.Decoded data start ys y last) :
    xs = ys ∧ x = y ∧ next = last := by
  obtain ⟨n, p, q, hn, hlen, hs, ht⟩ := hx
  obtain ⟨m, r, s, hm, hlen', hs', ht'⟩ := hy
  obtain ⟨rfl, rfl⟩ := hn.unique hm
  obtain ⟨rfl, rfl⟩ := hs.unique hs' (hlen.trans hlen'.symm)
  exact ⟨rfl, ht.unique ht'⟩

end Itasca

end

end

/-! ## MemoryMeaning -/

section

/-!
# Scalar memory instruction meaning

Load/store opcode typing, inverse stack effects and declared-reference facts connect the
independent memory grammar to generated judgments. These proofs use the literal opcode
table rather than assuming validator acceptance.
-/

/-! ## MemoryTyping -/

section

/-!
# Typing of scalar memory opcodes

Shows that each row of `Body.MemoryMeaning.opcodeMeaning` is typed by the generated `Instr_ok` rule
once the memory exists and the alignment is within its natural bound (`opcode_meaning_typed`,
`Translation.Environment.Matches.memory_operation`), and conversely that a generated typing of a row
recovers those preconditions (`opcode_meaning_inverse`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.MemoryMeaning

/-- The operand types of a load or store: the address, and the value for a store. -/
def Operation.inputs (op : Operation) : List wasm_types.ValueType :=
  if op.store then [.I32, op.ty] else [.I32]

/-- The result types of a load or store: the loaded value, or none for a store. -/
def Operation.outputs (op : Operation) : List wasm_types.ValueType :=
  if op.store then [] else [op.ty]

/-- The SpecTec memory argument of a Rust `MemArg` is well formed. -/
theorem mem_arg_wf (arg : code.MemArg) : wf_memarg (memArg arg) :=
  .memarg_case_ _ _ (Translation.Environment.index_wf _) (Translation.Environment.index_wf _)

theorem alignment_mono (a b : Nat) (h : a ≤ b) : (2 : Rat) ^ a ≤ 2 ^ b := by
  exact pow_le_pow_right₀ (by norm_num) h

/-- The row's stack effect is an instance of the generated memory rule, once memory zero exists and
the alignment is within the natural alignment. -/
def Operation.Typed (op : Operation) : Prop :=
  ∀ (arg : code.MemArg) (C : context) (mt : memtype),
    wf_context C → 0 < C.MEMS.length → C.MEMS[0]! = mt → wf_memtype mt →
    arg.align.val ≤ op.naturalAlign.val →
    wf_instr (op.op arg) ∧ Instr_ok C (op.op arg)
      (.mk_functype (.mk_list (op.inputs.map Translation.valueType))
        (.mk_list (op.outputs.map Translation.valueType)))

theorem full_load_typed (ty : wasm_types.ValueType) (nt : numtype) (alignment : U32)
    (bits : Nat) (hty : valtype_numtype nt = Translation.valueType ty)
    (hbits : size (valtype_numtype nt) = some bits)
    (halign : (2 : Rat) ^ alignment.val ≤ (bits : Rat) / 8) :
    (fullLoad ty nt alignment).Typed := by
  intro arg C mt hC hm he hmt ha
  have hw : wf_instr (.LOAD nt none (memArg arg)) :=
    .instr_case_56 _ _ _ (by simp [Forall]) (mem_arg_wf _)
  refine ⟨hw, ?_⟩
  have hp : (2 : Rat) ^ (proj_uN_0 (memArg arg).ALIGN) ≤
      (Option.get! (size (valtype_numtype nt)) : Rat) / 8 := by
    simpa [memArg, proj_uN_0, hbits] using (alignment_mono _ _ ha).trans halign
  simpa [Operation.inputs, Operation.outputs, fullLoad, hty, Translation.valueType] using
    Instr_ok.load_val C nt (memArg arg) mt hm he (by simp [hbits]) hp hC hmt hw

theorem full_store_typed (ty : wasm_types.ValueType) (nt : numtype) (alignment : U32)
    (bits : Nat) (hty : valtype_numtype nt = Translation.valueType ty)
    (hbits : size (valtype_numtype nt) = some bits)
    (halign : (2 : Rat) ^ alignment.val ≤ (bits : Rat) / 8) :
    (fullStore ty nt alignment).Typed := by
  intro arg C mt hC hm he hmt ha
  have hw : wf_instr (.STORE nt none (memArg arg)) :=
    .instr_case_57 none _ _ _ (by simp [Forall]) (mem_arg_wf _)
      (by simp) (by simp [Forall₂])
  refine ⟨hw, ?_⟩
  have hp : (2 : Rat) ^ (proj_uN_0 (memArg arg).ALIGN) ≤
      (Option.get! (size (valtype_numtype nt)) : Rat) / 8 := by
    simpa [memArg, proj_uN_0, hbits] using (alignment_mono _ _ ha).trans halign
  simpa [Operation.inputs, Operation.outputs, fullStore, hty, Translation.valueType] using
    Instr_ok.store_val C nt (memArg arg) mt hm he (by simp [hbits]) hp hC hmt hw

theorem packed_load_typed (ty : wasm_types.ValueType) (it : Inn) (width : Nat)
    (extension : sx) (alignment : U32)
    (hty : valtype_Inn it = Translation.valueType ty)
    (hw : wf_sz (.mk_sz width)) (hfit : width < sizenn (numtype_Inn it))
    (halign : (2 : Rat) ^ alignment.val ≤ (width : Rat) / 8) :
    (packedLoad ty it width extension alignment).Typed := by
  intro arg C mt hC hm he hmt ha
  have hwf : wf_instr ((packedLoad ty it width extension alignment).op arg) := by
    apply wf_instr.instr_case_56
    · simp only [Option.toList_some, Forall, List.mem_singleton, forall_eq]
      exact .loadop__case_0 _ _ _ (.loadop_Inn_case_0 _ _ _ hw hfit) rfl
    · exact mem_arg_wf _
  refine ⟨hwf, ?_⟩
  have hp : (2 : Rat) ^ (proj_uN_0 (memArg arg).ALIGN) ≤ (width : Rat) / 8 :=
    (alignment_mono _ _ ha).trans halign
  simpa [Operation.inputs, Operation.outputs, packedLoad, hty, Translation.valueType] using
    Instr_ok.load_pack C it width extension (memArg arg) mt hm he hp hC hmt hwf

theorem packed_store_typed (ty : wasm_types.ValueType) (it : Inn) (width : Nat) (alignment : U32)
    (hty : valtype_Inn it = Translation.valueType ty)
    (hw : wf_sz (.mk_sz width)) (hfit : width < sizenn (numtype_Inn it))
    (halign : (2 : Rat) ^ alignment.val ≤ (width : Rat) / 8) :
    (packedStore ty it width alignment).Typed := by
  intro arg C mt hC hm he hmt ha
  have hwf : wf_instr ((packedStore ty it width alignment).op arg) := by
    apply wf_instr.instr_case_57 (some it)
    · simpa [Forall] using hw
    · exact mem_arg_wf _
    · simp
    · simpa [Forall₂, proj_sz_0] using hfit
  refine ⟨hwf, ?_⟩
  have hp : (2 : Rat) ^ (proj_uN_0 (memArg arg).ALIGN) ≤ (width : Rat) / 8 :=
    (alignment_mono _ _ ha).trans halign
  simpa [Operation.inputs, Operation.outputs, packedStore, hty, Translation.valueType] using
    Instr_ok.store_pack C it width (memArg arg) mt hm he hp hC hmt hwf

/-- Every row of the memory opcode table is typed by the generated rule. -/
theorem opcode_meaning_typed (opcode : U8) (op : Operation)
    (h : opcodeMeaning opcode = some op) : op.Typed := by
  unfold opcodeMeaning at h
  split at h <;> cases h
  all_goals first
    | exact full_load_typed _ _ _ 32 rfl rfl (by norm_num)
    | exact full_load_typed _ _ _ 64 rfl rfl (by norm_num)
    | exact full_store_typed _ _ _ 32 rfl rfl (by norm_num)
    | exact full_store_typed _ _ _ 64 rfl rfl (by norm_num)
    | apply packed_load_typed
    | apply packed_store_typed
  all_goals try (apply wf_sz.sz_case_0; norm_num)
  all_goals norm_num [valtype_numtype, valtype_Inn, Translation.valueType, size, sizenn, numtype_Inn]

end Itasca.Body.MemoryMeaning

namespace Itasca.Translation.Environment

/-- Under a matching environment, a memory row with an in-bound alignment is well formed and typed
in the SpecTec context. -/
theorem Matches.memory_operation {env ctx C} (h : Matches env ctx C)
    (opcode : U8) (op : Body.MemoryMeaning.Operation) (hrow : Body.MemoryMeaning.opcodeMeaning opcode = some op)
    (arg : code.MemArg) (hm : 0 < env.mem_types.val.length)
    (ha : arg.align.val ≤ op.naturalAlign.val) :
    wf_instr (op.op arg) ∧ Instr_ok C (op.op arg)
      (.mk_functype (.mk_list (op.inputs.map Translation.valueType))
        (.mk_list (op.outputs.map Translation.valueType))) := by
  apply Body.MemoryMeaning.opcode_meaning_typed opcode op hrow arg C (memType (env.mem_types.val[0]))
    h.wf _ _ (mem_type_wf _) ha
  · simpa [h.mems] using hm
  · simp only [h.mems]
    rw [getElem!_pos _ _ (by simpa using hm), List.getElem_map]

end Itasca.Translation.Environment

open Aeneas Aeneas.Std

namespace Itasca.Body.MemoryMeaning

private def Principal (C : context) (op : instr) (ins outs : List valtype) : Prop :=
  match op with
  | .LOAD nt none arg =>
      0 < C.MEMS.length ∧ (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤
        (Option.get! (size (valtype_numtype nt)) : Rat) / 8 ∧ ins = [.I32] ∧ outs = [valtype_numtype nt]
  | .LOAD _ (some (.mk_loadop__0 it (.mk_loadop_Inn width _))) arg =>
      0 < C.MEMS.length ∧ (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤
        (proj_sz_0 width : Rat) / 8 ∧ ins = [.I32] ∧ outs = [valtype_Inn it]
  | .STORE nt none arg =>
      0 < C.MEMS.length ∧ (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤
        (Option.get! (size (valtype_numtype nt)) : Rat) / 8 ∧ ins = [.I32, valtype_numtype nt] ∧ outs = []
  | .STORE nt (some width) arg =>
      0 < C.MEMS.length ∧ (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤
        (proj_sz_0 width : Rat) / 8 ∧ ins = [.I32, valtype_numtype nt] ∧ outs = []
  | _ => True

private theorem principal {C op ins outs}
    (h : Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs))) : Principal C op ins outs := by
  have hinn (i : Inn) : valtype_numtype (numtype_Inn i) = valtype_Inn i := by cases i <;> rfl
  cases h <;> simp_all [Principal, proj_sz_0]

/-- A generated typing of a memory row implies that memory zero exists, the alignment is within the
natural alignment, and the stack types are the row's. -/
theorem opcode_meaning_inverse (opcode : U8) (operation : Operation)
    (hrow : opcodeMeaning opcode = some operation) (C : context) (arg : code.MemArg)
    (ins outs : List valtype)
    (ht : Instr_ok C (operation.op arg) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    0 < C.MEMS.length ∧ arg.align.val ≤ operation.naturalAlign.val ∧
      ins = operation.inputs.map Translation.valueType ∧
      outs = operation.outputs.map Translation.valueType := by
  have hp := principal ht
  unfold opcodeMeaning at hrow
  split at hrow <;> cases hrow
  all_goals simp only [fullLoad, fullStore, packedLoad, packedStore, Principal] at hp
  all_goals obtain ⟨hm, ha, rfl, rfl⟩ := hp
  all_goals refine ⟨hm, ?_, rfl, rfl⟩
  all_goals apply (pow_le_pow_iff_right₀ (a := (2 : Rat)) (by norm_num)).mp
  all_goals norm_num [memArg, proj_uN_0, proj_sz_0, valtype_numtype, size] at *
  all_goals assumption

end Itasca.Body.MemoryMeaning

end

/-! ## DeclaredReferences -/

section

/-!
# Declared references in scalar syntax

Scalar immediates and tokens meet their declared-reference obligations for any
reference set, because this internal grammar contains no `ref.func`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Scalar

open Body (Token TokensDeclared tokens_declared_append tokens_declared_singleton Emits)

set_option maxHeartbeats 2000000 in
/-- Every scalar instruction token meets its obligation, since the grammar has no `ref.func`. -/
theorem Immediate.declared {opcode token bytes} (hi : Immediate opcode token bytes)
    (refs : List funcidx) : token.Declared refs := by
  cases hi with
  | numericInstruction opcode source hmap =>
    rw [Body.Numeric.opcodeInstruction_eq] at hmap
    obtain ⟨operation, decoded, rfl⟩ := Option.map_eq_some_iff.mp hmap
    unfold Body.Numeric.opcodeMeaning at decoded
    split at decoded <;> simp only [Option.some.injEq, reduceCtorEq] at decoded
    all_goals subst operation
    all_goals simp [Body.Token.Declared, Spec.DeclaredReferences.Instruction,
      Spec.DeclaredReferences.instructionIndices, Body.Numeric.unary, Body.Numeric.binary,
      Body.Numeric.test, Body.Numeric.relation, Body.Numeric.conversion]
  | memory opcode operation arg hmap _ _ =>
    unfold Body.MemoryMeaning.opcodeMeaning at hmap
    split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap
    all_goals subst operation
    all_goals simp [Body.Token.Declared, Spec.DeclaredReferences.Instruction,
      Spec.DeclaredReferences.instructionIndices, Body.MemoryMeaning.fullLoad, Body.MemoryMeaning.packedLoad,
      Body.MemoryMeaning.fullStore, Body.MemoryMeaning.packedStore]
  | _ => simp [Body.Token.Declared, Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices,
      Spec.i32Const, Spec.Constants.i64, Spec.Constants.f32, Spec.Constants.f64]

/-- A token read at a cursor meets its obligation. -/
theorem At.declared {data start token next} (h : At data start token next) (refs : List funcidx) :
    token.Declared refs := by
  obtain ⟨_, ⟨_, _, _, hi⟩, _⟩ := h
  exact hi.declared refs

end Itasca.Body.Scalar

end

end
