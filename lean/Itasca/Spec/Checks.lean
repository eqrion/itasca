import «wasm2.0»

/-!
# Sanity checks of the generated specification

Small theorems that check the generated `wasm2.0.lean` is usable and covers the intended cases:
mutable and immutable globals, a nonempty `Instr_ok` instance, UTF-8 witnesses for four-byte
scalars, and import projections that must not drop an import of the projected kind.
-/

namespace Itasca.SpecChecks

/-- Mutable globals satisfy `Globaltype_ok`. -/
theorem mutable_global_supported (t : valtype) :
    Globaltype_ok (globaltype.mk_globaltype (some r_MUT.MUT) t) :=
  .mk_Globaltype_ok _ t

/-- Immutable globals satisfy `Globaltype_ok`. -/
theorem immutable_global_supported (t : valtype) :
    Globaltype_ok (globaltype.mk_globaltype none t) :=
  .mk_Globaltype_ok _ t

/-- `nop` is typed, so `Instr_ok` has inhabited instances. -/
theorem nop_typed (C : context) (hC : wf_context C) :
    Instr_ok C instr.NOP (functype.mk_functype (.mk_list []) (.mk_list [])) := by
  apply Instr_ok.nop C hC
  constructor

/-- The four-byte UTF-8 rule covers the first four-byte scalar value, U+10000. -/
theorem utf8_first_four_byte :
    fun_utf8 [.mk_char 0x10000]
      [.mk_byte 0xF0, .mk_byte 0x90, .mk_byte 0x80, .mk_byte 0x80] := by
  apply fun_utf8.fun_utf8_case_3
  · decide
  all_goals constructor; decide

/-- The four-byte UTF-8 rule covers U+1F600. -/
theorem utf8_emoji :
    fun_utf8 [.mk_char 0x1F600]
      [.mk_byte 0xF0, .mk_byte 0x9F, .mk_byte 0x98, .mk_byte 0x80] := by
  apply fun_utf8.fun_utf8_case_3
  · decide
  all_goals constructor; decide

/-- The four-byte UTF-8 rule covers the last scalar value, U+10FFFF. -/
theorem utf8_last_scalar :
    fun_utf8 [.mk_char 0x10FFFF]
      [.mk_byte 0xF4, .mk_byte 0x8F, .mk_byte 0xBF, .mk_byte 0xBF] := by
  apply fun_utf8.fun_utf8_case_3
  · decide
  all_goals constructor; decide

/-- A name containing a four-byte scalar value is well-formed. -/
theorem emoji_name_well_formed : wf_name (.mk_name [.mk_char 0x1F600]) := by
  apply wf_name.name_case_0 _ _ utf8_emoji
  · intro c hc
    have : c = .mk_char 0x1F600 := List.mem_singleton.mp hc
    subst c
    constructor
    decide
  · decide

/-- The `funcs` import projection does not discard a function import. -/
theorem function_import_not_discarded (ft : functype) :
    ¬ fun_funcsxt [.FUNC ft] [] := by
  intro h
  cases h

/-- The `globals` import projection does not discard a global import. -/
theorem global_import_not_discarded (gt : globaltype) :
    ¬ fun_globalsxt [.GLOBAL gt] [] := by
  intro h
  cases h

/-- The `tables` import projection does not discard a table import. -/
theorem table_import_not_discarded (tt : tabletype) :
    ¬ fun_tablesxt [.TABLE tt] [] := by
  intro h
  cases h

/-- The `mems` import projection does not discard a memory import. -/
theorem memory_import_not_discarded (mt : memtype) :
    ¬ fun_memsxt [.MEM mt] [] := by
  intro h
  cases h

#print axioms mutable_global_supported
#print axioms immutable_global_supported
#print axioms nop_typed

end Itasca.SpecChecks
