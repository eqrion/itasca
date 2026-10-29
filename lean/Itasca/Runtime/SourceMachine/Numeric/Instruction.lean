import Itasca.Runtime.SourceMachine.Numeric.OperandsCore
import Itasca.Runtime.SourceMachine.Sim.Int
import Itasca.Runtime.Spec.IntegerExtend
import SpecExt.Builtins.Counts
import Itasca.Runtime.Spec.IntegerBits
import Itasca.Runtime.Spec.IntegerRotate
import Itasca.Runtime.Spec.IntegerShift
import Itasca.Runtime.SourceMachine.Sim.Trap
import Itasca.Runtime.Spec.IntegerCompareSigned
import Itasca.Runtime.SourceMachine.Preservation

/-!
Integer instruction soundness from unary, binary, comparison and conversion operations. Establishes typed source reduction used by transition safety and interpreter simulation.
-/

/-! ## Unary -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec SpecExt.Builtins

theorem unary_relation (ty : Inn) (op : unop_Inn) (bits : BitVec (sizenn (numtype_Inn ty))) :
    fun_unop_ (numtype_Inn ty) (.mk_unop__0 ty op)
      (.mk_num__0 ty (.mk_uN bits.toNat))
      (some [.mk_num__0 ty (.mk_uN (unary ty op bits).toNat)]) := by
  have wf := unsigned_num_wf ty _ (unary ty op bits).isLt
  cases op with
  | EXTEND small => exact extend_unary_bitvec ty small bits
  | CLZ =>
    have bound : leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat) ≤ sizenn (numtype_Inn ty) := by
      simpa only [integerBits_length] using leadingZeros_le_length (integerBits (sizenn (numtype_Inn ty)) bits.toNat)
    have small : leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      exact lt_of_le_of_lt bound (by cases ty <;> decide)
    simp only [unary, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at wf ⊢
    cases ty
    · exact .fun_unop__case_0 _ wf
    · exact .fun_unop__case_1 _ wf
  | CTZ =>
    have bound : leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat).reverse ≤ sizenn (numtype_Inn ty) := by
      simpa only [List.length_reverse, integerBits_length] using leadingZeros_le_length (integerBits (sizenn (numtype_Inn ty)) bits.toNat).reverse
    have small : leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat).reverse < 2 ^ sizenn (numtype_Inn ty) := by
      exact lt_of_le_of_lt bound (by cases ty <;> decide)
    simp only [unary, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at wf ⊢
    cases ty
    · exact .fun_unop__case_2 _ wf
    · exact .fun_unop__case_3 _ wf
  | POPCNT =>
    have bound := population_bits_le (sizenn (numtype_Inn ty)) bits.toNat
    have small : population (integerBits (sizenn (numtype_Inn ty)) bits.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      exact lt_of_le_of_lt bound (by cases ty <;> decide)
    simp only [unary, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at wf ⊢
    cases ty
    · exact .fun_unop__case_4 _ wf
    · exact .fun_unop__case_5 _ wf

theorem unary_pure (ty : Inn) (op : unop_Inn) (bits : BitVec (sizenn (numtype_Inn ty))) :
    Step_pure [admininstr_val (integerVal ty bits.toNat),
      admininstr_instr (.UNOP (numtype_Inn ty) (.mk_unop__0 ty op))]
      [admininstr_val (integerVal ty (unary ty op bits).toNat)] := by
  apply Step_pure.unop_val (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits.toNat))
    (.mk_unop__0 ty op) (.mk_num__0 ty (.mk_uN (unary ty op bits).toNat))
    (some [.mk_num__0 ty (.mk_uN (unary ty op bits).toNat)])
  · exact unary_relation ty op bits
  · simp
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty bits))
  · exact wf_admininstr_instr (.instr_case_14 _ _ (.unop__case_0 _ _ _ rfl))
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty (unary ty op bits)))

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Binary -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec

theorem binary_relation (ty : Inn) (op : binop_Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op)
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (binaryNumbers ty (binary ty op a b))) := by
  have width : integerWidth ty = sizenn (numtype_Inn ty) := by cases ty <;> rfl
  cases op with
  | ADD =>
    simpa only [binary, binaryNumbers, BitVec.toNat_add, width] using integer_add_relation ty a.toNat b.toNat
  | SUB =>
    have reorder : 2 ^ sizenn (numtype_Inn ty) - b.toNat + a.toNat = a.toNat + 2 ^ sizenn (numtype_Inn ty) - b.toNat := by have := b.isLt; omega
    simpa only [binary, binaryNumbers, BitVec.toNat_sub, width, reorder] using integer_sub_relation ty a.toNat b.toNat (word_bound ty b)
  | MUL =>
    have wf := unsigned_num_wf ty (a * b).toNat (a * b).isLt
    simp only [binary, binaryNumbers, BitVec.toNat_mul] at wf ⊢
    cases ty
    · exact .fun_binop__case_4 _ _ _ (.fun_imul__case_0 _ _ _ (unsigned_wf_of_lt _ _ (a * b).isLt)) wf
    · exact .fun_binop__case_5 _ _ _ (.fun_imul__case_0 _ _ _ (unsigned_wf_of_lt _ _ (a * b).isLt)) wf
  | DIV sign =>
    cases sign with
    | U =>
      simp only [binary]
      split
      · rename_i zero; simp only [binaryNumbers]; simpa [zero] using integer_divu_zero_relation ty a.toNat
      · rename_i nonzero
        simpa [binaryNumbers, BitVec.toNat_udiv] using integer_divu_relation ty a.toNat b.toNat a.isLt nonzero
    | S =>
      simp only [binary]
      split
      · rename_i zero; simp only [binaryNumbers]; simpa [zero] using integer_divs_zero_relation ty a.toNat
      · split
        · rename_i overflow
          rcases overflow with ⟨rfl, rfl⟩
          cases ty
          · exact integer_divs_trap_relation .I32 _ _ signed_div_overflow32
          · exact integer_divs_trap_relation .I64 _ _ signed_div_overflow64
        · rename_i nonzero regular
          exact integer_divs_relation ty a b (a.sdiv b) nonzero
            (BitVec.toInt_sdiv_of_ne_or_ne a b (by tauto))
  | REM sign =>
    cases sign with
    | U =>
      simp only [binary]
      split
      · rename_i zero; simp only [binaryNumbers]; simpa [zero] using integer_remu_zero_relation ty a.toNat
      · rename_i nonzero
        simpa [binaryNumbers, BitVec.toNat_umod] using integer_remu_relation ty a.toNat b.toNat a.isLt nonzero
    | S =>
      simp only [binary]
      split
      · rename_i zero; simp only [binaryNumbers]; simpa [zero] using integer_rems_zero_relation ty a.toNat
      · rename_i nonzero
        exact integer_rems_relation ty a b (a.srem b) nonzero (BitVec.toInt_srem a b)
  | AND =>
    have bound : (a.toNat &&& b.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      simpa only [BitVec.toNat_and] using (a &&& b).isLt
    simpa only [binary, binaryNumbers, SpecExt.Builtins.iand_value, BitVec.toNat_and, Nat.mod_eq_of_lt bound] using integer_and_relation ty a.toNat b.toNat
  | OR =>
    have bound : (a.toNat ||| b.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      simpa only [BitVec.toNat_or] using (a ||| b).isLt
    simpa only [binary, binaryNumbers, SpecExt.Builtins.ior_value, BitVec.toNat_or, Nat.mod_eq_of_lt bound] using integer_or_relation ty a.toNat b.toNat
  | XOR =>
    have bound : (a.toNat ^^^ b.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      simpa only [BitVec.toNat_xor] using (a ^^^ b).isLt
    simpa only [binary, binaryNumbers, SpecExt.Builtins.ixor_value, BitVec.toNat_xor, Nat.mod_eq_of_lt bound] using integer_xor_relation ty a.toNat b.toNat
  | SHL => simpa [binary, binaryNumbers, Nat.shiftLeft_eq] using integer_shl_relation ty a.toNat b.toNat
  | SHR sign =>
    cases sign with
    | U => simpa [binary, binaryNumbers, Nat.shiftRight_eq_div_pow] using integer_shru_relation ty a.toNat b.toNat a.isLt
    | S => exact integer_shrs_relation ty a b.toNat
  | ROTL => exact integer_rotleft_relation ty a b.toNat
  | ROTR => exact integer_rotright_relation ty a b.toNat

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Binary Simulation -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec

theorem binary_pure (ty : Inn) (op : binop_Inn)
    (a b result : BitVec (sizenn (numtype_Inn ty)))
    (success : binary ty op a b = some result) :
    Step_pure [admininstr_val (integerVal ty a.toNat), admininstr_val (integerVal ty b.toNat),
      admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op))]
      [admininstr_val (integerVal ty result.toNat)] := by
  apply Step_pure.binop_val (numtype_Inn ty) (.mk_num__0 ty (.mk_uN a.toNat))
    (.mk_num__0 ty (.mk_uN b.toNat)) (.mk_binop__0 ty op)
    (.mk_num__0 ty (.mk_uN result.toNat)) (some [.mk_num__0 ty (.mk_uN result.toNat)])
  · simpa only [success, binaryNumbers] using binary_relation ty op a b
  · simp
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty a))
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty b))
  · exact wf_admininstr_instr (.instr_case_15 _ _ (.binop__case_0 _ _ _ rfl))
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty result))

theorem binary_trap_pure (ty : Inn) (op : binop_Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) (trap : binary ty op a b = none) :
    Step_pure [admininstr_val (integerVal ty a.toNat), admininstr_val (integerVal ty b.toNat),
      admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op))] [.TRAP] := by
  apply Step_pure.binop_trap (numtype_Inn ty) (.mk_num__0 ty (.mk_uN a.toNat))
    (.mk_num__0 ty (.mk_uN b.toNat)) (.mk_binop__0 ty op) (some [])
  · simpa only [trap, binaryNumbers] using binary_relation ty op a b
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty a))
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty b))
  · exact wf_admininstr_instr (.instr_case_15 _ _ (.binop__case_0 _ _ _ rfl))
  · exact .admininstr_case_73

/-- Numeric traps unwind all labels and suspended calls in finitely many real
source reductions. The operands remain bounded source words throughout. -/
theorem binary_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (ty : Inn) (op : binop_Inn) (a b : BitVec (sizenn (numtype_Inn ty)))
    (trap : binary ty op a b = none)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient,
        { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty op) :: after, vals := baseValues ++ [integerVal ty a.toNat, integerVal ty b.toNat] } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  let operands := [integerVal ty a.toNat, integerVal ty b.toNat]
  have operandsWf : Forall wf_val operands := by
    intro value h; simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact integer_val_wf ty _ (word_bound ty a)
    · exact integer_val_wf ty _ (word_bound ty b)
  have instructionWf : wf_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op)) :=
    .instr_case_15 _ _ (.binop__case_0 _ _ _ rfl)
  have before : wf_config ⟨⟨s, f.toFrame⟩, vals operands ++ [admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op))]⟩ := wf_config_make hs hf (forall_append (wf_vals operandsWf)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact wf_admininstr_instr instructionWf))
  have step : StepH ⟨⟨s, f.toFrame⟩, vals operands ++
      [admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty op))]⟩ []
      ⟨⟨s, f.toFrame⟩, [.TRAP]⟩ :=
    .step (.pure _ _ _ (binary_trap_pure ty op a b trap) before (wf_config_make hs hf wf_trap))
  have lifted := step_h_active ambient rest f.arity
    (step_h_decode_labels (step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
      f.labels baseValues hl hv) ha hr
  have frameWf : Forall FrameWf ({ f with code := after, vals := baseValues } :: rest) := by
    intro frame hm; simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨hf, hl, hv, hc⟩
    · exact hr frame hm
  obtain ⟨n, tail⟩ := trap_frames s ambient ({ f with code := after, vals := baseValues } :: rest) hs ha frameWf
  refine ⟨n + 1, by omega, ?_⟩
  have all := StepsHN.cons lifted tail
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [decodeFrames, operands, vals, instrContext, AFrame.toFrame, AFrame.arity, List.append_assoc] using all
end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Compare -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec

theorem compare_bound (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    compare ty op a b < 2 ^ integerWidth .I32 := by
  unfold compare
  split <;> split <;> decide

theorem compare_relation (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op)
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (compare ty op a b)))) := by
  cases op with
  | EQ => exact integer_eq_relation ty _ _
  | NE => exact integer_ne_relation ty _ _
  | LT sign => cases sign with
    | U => exact integer_ltu_relation ty _ _
    | S => exact integer_lts_relation ty a b
  | GT sign => cases sign with
    | U => exact integer_gtu_relation ty _ _
    | S => exact integer_gts_relation ty a b
  | LE sign => cases sign with
    | U => exact integer_leu_relation ty _ _
    | S => exact integer_les_relation ty a b
  | GE sign => cases sign with
    | U => exact integer_geu_relation ty _ _
    | S => exact integer_ges_relation ty a b

theorem compare_pure (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    Step_pure [admininstr_val (integerVal ty a.toNat), admininstr_val (integerVal ty b.toNat),
      admininstr_instr (.RELOP (numtype_Inn ty) (.mk_relop__0 ty op))]
      [admininstr_val (integerVal .I32 (compare ty op a b))] :=
  integer_relop_pure ty op a.toNat b.toNat _ (word_bound ty a) (word_bound ty b)
    (compare_bound ty op a b) (compare_relation ty op a b)

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Conversion -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec

theorem Conversion.source_wf (op : Conversion) : wf_instr op.source := by
  cases op
  · exact .instr_case_18 _ _ _ (.cvtop___case_0 _ _ _ _ _ (.cvtop__Inn_1_Inn_2_case_1 _ _ (by decide)) rfl rfl) (by decide)
  · exact .instr_case_18 _ _ _ (.cvtop___case_0 _ _ _ _ _ (.cvtop__Inn_1_Inn_2_case_0 _ _ _ (by decide)) rfl rfl) (by decide)
  · exact .instr_case_18 _ _ _ (.cvtop___case_0 _ _ _ _ _ (.cvtop__Inn_1_Inn_2_case_0 _ _ _ (by decide)) rfl rfl) (by decide)

theorem Conversion.relation (op : Conversion) (bits : BitVec (sizenn (numtype_Inn op.input))) :
    fun_cvtop__ (numtype_Inn op.input) (numtype_Inn op.output) op.operator
      (.mk_num__0 op.input (.mk_uN bits.toNat))
      (some [.mk_num__0 op.output (.mk_uN (op.apply bits).toNat)]) := by
  cases op with
  | wrap => exact integer_wrap_relation bits
  | extendSigned => exact integer_extends_relation bits
  | extendUnsigned =>
    have bound : bits.toNat < 2^64 := by have := bits.isLt; change bits.toNat < 2^32 at this; omega
    change fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U)) _ (some [.mk_num__0 .I64 (.mk_uN (bits.setWidth 64).toNat)])
    rw [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt bound]
    exact integer_extendu_relation bits

theorem Conversion.pure (op : Conversion) (bits : BitVec (sizenn (numtype_Inn op.input))) :
    Step_pure [admininstr_val (integerVal op.input bits.toNat), admininstr_instr op.source]
      [admininstr_val (integerVal op.output (op.apply bits).toNat)] := by
  apply Step_pure.cvtop_val (numtype_Inn op.input) (.mk_num__0 op.input (.mk_uN bits.toNat))
    (numtype_Inn op.output) op.operator (.mk_num__0 op.output (.mk_uN (op.apply bits).toNat))
    (some [.mk_num__0 op.output (.mk_uN (op.apply bits).toNat)])
  · exact op.relation bits
  · simp
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf op.input _ (word_bound op.input bits))
  · exact wf_admininstr_instr op.source_wf
  · exact wf_admininstr_val (integer_val_wf op.output _ (word_bound op.output (op.apply bits)))

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Typing -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec

theorem unary_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {ty : Inn} {op : unop_Inn} {bits result : Nat}
    (hs : wf_store s) (hr : result < 2 ^ integerWidth ty)
    (h : FrameTyped s
      { f with code := .UNOP (numtype_Inn ty) (.mk_unop__0 ty op) :: code, vals := baseValues ++ [integerVal ty bits] } []) :
    FrameTyped s { f with code := code, vals := baseValues ++ [integerVal ty result] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      code_stack_after (value_types_concrete (baseValues ++ [integerVal ty bits])) hc
    cases hop
    simp only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
      List.append_cancel_right_eq] at hstack
    have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
      simpa using results_typed_take baseValues.length values
    have hresult := integer_val_typed hs ty result hr
    apply FrameTyped.mk (f := { f with code := code, vals := baseValues ++ [integerVal ty result] }) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
        numtype_Inn, valtype_numtype] using List.rel_append hvalues (List.Forall₂.cons hresult List.Forall₂.nil)
    · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil,
        integerVal, valueType, numtype_Inn, valtype_numtype, hstack] using hafter

theorem conversion_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {ty target : Inn} {op : cvtop__} {bits result : Nat}
    (hs : wf_store s) (hr : result < 2 ^ integerWidth target)
    (h : FrameTyped s
      { f with code := .CVTOP (numtype_Inn target) (numtype_Inn ty) op :: code, vals := baseValues ++ [integerVal ty bits] } []) :
    FrameTyped s { f with code := code, vals := baseValues ++ [integerVal target result] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      code_stack_after (value_types_concrete (baseValues ++ [integerVal ty bits])) hc
    cases hop
    simp only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
      List.append_cancel_right_eq] at hstack
    have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
      simpa using results_typed_take baseValues.length values
    have hresult := integer_val_typed hs target result hr
    apply FrameTyped.mk (f := { f with code := code, vals := baseValues ++ [integerVal target result] }) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
        numtype_Inn, valtype_numtype] using List.rel_append hvalues (List.Forall₂.cons hresult List.Forall₂.nil)
    · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil,
        integerVal, valueType, numtype_Inn, valtype_numtype, hstack] using hafter


end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Unary Operators -/

section

namespace Itasca.Runtime.SourceMachine.Numeric

theorem UnaryOperator.opcode_bound {ty : Inn} (op : UnaryOperator ty) : op.opcode < 65536 := by
  cases ty <;> cases op <;> decide

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Instruction -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec

theorem Instruction.source_wf (op : Instruction) : wf_instr op.source := by
  cases op with
  | binary ty op => exact .instr_case_15 _ _ (.binop__case_0 _ _ _ rfl)
  | unary ty op => exact .instr_case_14 _ _ (.unop__case_0 _ _ _ rfl)
  | compare ty op => exact .instr_case_17 _ _ (.relop__case_0 _ _ _ rfl)
  | eqz ty => exact .instr_case_16 _ _ (.testop__case_0 _ _ _ rfl)
  | conversion op => exact op.source_wf

theorem Instruction.operands_wf (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) : Forall wf_val (op.operands a b) := by
  unfold operands
  split
  · intro v h; simp only [List.mem_singleton] at h; subst v
    exact integer_val_wf _ _ (word_bound _ _)
  · intro v h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact integer_val_wf _ _ (word_bound _ _)

theorem Instruction.pure_success (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output)))
    (success : op.apply a b = some result) :
    Step_pure (vals (op.operands a b) ++ [admininstr_instr op.source])
      [admininstr_val (integerVal op.output result.toNat)] := by
  cases op with
  | binary ty binop => exact binary_pure ty binop a b result success
  | unary ty unop =>
    simp only [apply, Option.some.injEq] at success
    subst result
    exact unary_pure ty unop.operation a
  | compare ty relop =>
    simp only [apply, Option.some.injEq] at success
    subst result
    have bound : Numeric.compare ty relop a b < 2^32 := compare_bound ty relop a b
    change Step_pure _ [admininstr_val (integerVal .I32 (BitVec.ofNat 32 (Numeric.compare ty relop a b)).toNat)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    exact compare_pure ty relop a b
  | eqz ty =>
    simp only [apply, Option.some.injEq] at success
    subst result
    have bound : (if a.toNat = 0 then 1 else 0) < 2^32 := by split <;> decide
    change Step_pure _ [admininstr_val (integerVal .I32 (BitVec.ofNat 32 (if a.toNat = 0 then 1 else 0)).toNat)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    exact integer_eqz_pure ty a.toNat (word_bound ty a)
  | conversion conv =>
    simp only [apply, Option.some.injEq] at success
    subst result
    exact conv.pure a

end Itasca.Runtime.SourceMachine.Numeric

end

/-! ## Instruction Safety -/

section

namespace Itasca.Runtime.SourceMachine.Numeric
open SpecExt Itasca.Runtime.Spec

theorem Instruction.frame_preservation (op : Instruction)
    {s : store} {f : AFrame} {after : List instr} {front : List val}
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output))) (hs : wf_store s)
    (typed : FrameTyped s { f with code := op.source :: after, vals := front ++ op.operands a b } []) :
    FrameTyped s { f with code := after, vals := front ++ [integerVal op.output result.toNat] } [] := by
  cases op with
  | binary ty binop => exact integer_binop_frame_preservation hs (word_bound _ _) typed
  | unary ty unop => exact unary_frame_preservation hs (word_bound _ _) typed
  | compare ty relop => exact integer_relop_frame_preservation hs (word_bound _ _) typed
  | eqz ty => exact integer_testop_frame_preservation hs (word_bound _ _) typed
  | conversion conv => exact conversion_frame_preservation hs (word_bound _ _) typed

theorem Instruction.simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (front : List val)
    (op : Instruction) (a b : BitVec (sizenn (numtype_Inn op.input)))
    (result : BitVec (sizenn (numtype_Inn op.output)))
    (success : op.apply a b = some result)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length) :
    StepH (decode ⟨s, ambient,
      { f with code := op.source :: after, vals := front ++ op.operands a b } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := front ++ [integerVal op.output result.toNat] } :: rest, []⟩) := by
  apply pure_stack_simulation s ambient f rest _ after front _ _ hs ha hf hl hv hc hr heights
  · exact op.operands_wf a b
  · intro value h; simp only [List.mem_singleton] at h; subst value
    exact integer_val_wf _ _ (word_bound _ _)
  · exact op.source_wf
  · exact op.pure_success a b result success

theorem Instruction.trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (front : List val)
    (op : Instruction) (a b : BitVec (sizenn (numtype_Inn op.input)))
    (trap : op.apply a b = none)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient,
        { f with code := op.source :: after, vals := front ++ op.operands a b } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  cases op with
  | binary ty binop => exact binary_trap_simulation s ambient f rest after front ty binop a b trap hs ha hf hl hv hc hr heights
  | unary | compare | eqz | conversion => simp only [apply, Option.some_ne_none] at trap
end Itasca.Runtime.SourceMachine.Numeric

end
