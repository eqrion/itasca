import «wasm2.0»

namespace Itasca.SpecChecks

-- The source workaround quantifies over `mut`, preserving both mutabilities.
theorem mutable_global_supported (t : valtype) :
    Globaltype_ok (globaltype.mk_globaltype (some r_MUT.MUT) t) :=
  .mk_Globaltype_ok _ t

theorem immutable_global_supported (t : valtype) :
    Globaltype_ok (globaltype.mk_globaltype none t) :=
  .mk_Globaltype_ok _ t

-- A nonempty example ensures the instruction typing relation is usable.
theorem nop_typed (C : context) (hC : wf_context C) :
    Instr_ok C instr.NOP (functype.mk_functype (.mk_list []) (.mk_list [])) := by
  apply Instr_ok.nop C hC
  constructor

-- The four-byte source rule must include all Unicode scalar values, not just
-- U+10000 through U+10FFF. These witnesses use the actual UTF-8 bytes.
theorem utf8_first_four_byte :
    fun_utf8 [.mk_char 0x10000]
      [.mk_byte 0xF0, .mk_byte 0x90, .mk_byte 0x80, .mk_byte 0x80] := by
  apply fun_utf8.fun_utf8_case_3
  · decide
  all_goals constructor; decide

theorem utf8_emoji :
    fun_utf8 [.mk_char 0x1F600]
      [.mk_byte 0xF0, .mk_byte 0x9F, .mk_byte 0x98, .mk_byte 0x80] := by
  apply fun_utf8.fun_utf8_case_3
  · decide
  all_goals constructor; decide

theorem utf8_last_scalar :
    fun_utf8 [.mk_char 0x10FFFF]
      [.mk_byte 0xF4, .mk_byte 0x8F, .mk_byte 0xBF, .mk_byte 0xBF] := by
  apply fun_utf8.fun_utf8_case_3
  · decide
  all_goals constructor; decide

theorem emoji_name_well_formed : wf_name (.mk_name [.mk_char 0x1F600]) := by
  apply wf_name.name_case_0 _ _ utf8_emoji
  · intro c hc
    have : c = .mk_char 0x1F600 := List.mem_singleton.mp hc
    subst c
    constructor
    decide
  · decide

-- Explicit source cases prevent the generated fallback from dropping an
-- import of the very kind being projected.
theorem function_import_not_discarded (ft : functype) :
    ¬ fun_funcsxt [.FUNC ft] [] := by
  intro h
  cases h

theorem global_import_not_discarded (gt : globaltype) :
    ¬ fun_globalsxt [.GLOBAL gt] [] := by
  intro h
  cases h

theorem table_import_not_discarded (tt : tabletype) :
    ¬ fun_tablesxt [.TABLE tt] [] := by
  intro h
  cases h

theorem memory_import_not_discarded (mt : memtype) :
    ¬ fun_memsxt [.MEM mt] [] := by
  intro h
  cases h

#print axioms mutable_global_supported
#print axioms immutable_global_supported
#print axioms nop_typed

end Itasca.SpecChecks
