import Itasca.Main

/-!
# The Wasm 1.0 profile boundary

A body that the generated Wasm 2.0 typing rules accept but Wasm 1.0 forbids: a `br_table` after
`unreachable` whose targets have different types (`i64` and `i32`), which the Wasm 2.0 rule
allows by giving the operands the bottom type. `wasm2_accepted` shows the body meets
`Profile.Body .Wasm2` and `Profile.run .Wasm2` accepts it. `ops_not_wasm1` shows the Wasm 1.0
restriction fails for its only instruction tree, so `wasm1_rejected` follows from soundness:
`Profile.run .Wasm1` does not accept the body.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Wasm1ProfileBoundary

open Wasm2 (blockType blockType_wf blockType_ok FunctionTyped functionContext)

/-- The body bytes `02 7e 00 0e 01 00 01 0b 1a 00 0b`:
`block (result i64); unreachable; br_table [0] 1; end; drop; unreachable; end`. Label 0 expects
`i64` and label 1 expects `i32`. -/
def bytes : Slice U8 := alloc.vec.Vec.deref (alloc.vec.Vec.from
  [0x02#u8, 0x7E#u8, 0x00#u8, 0x0E#u8, 0x01#u8, 0x00#u8,
   0x01#u8, 0x0B#u8, 0x1A#u8, 0x00#u8, 0x0B#u8] (by scalar_tac))

/-- The function type `[] -> [i32]`. -/
def resultI32 : types.FuncType := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.I32] (by scalar_tac)⟩

/-- An environment whose only type is `resultI32`. -/
def env : module.Env where
  types := alloc.vec.Vec.from [resultI32] (by scalar_tac)
  imports := alloc.vec.Vec.new _
  globals := alloc.vec.Vec.new _
  exports := alloc.vec.Vec.new _
  elements := alloc.vec.Vec.new _
  start := none
  data_count := none
  declared_funcs := alloc.vec.Vec.new _
  func_type_indices := alloc.vec.Vec.new _
  func_types := alloc.vec.Vec.new _
  table_types := alloc.vec.Vec.new _
  mem_types := alloc.vec.Vec.new _
  global_types := alloc.vec.Vec.new _
  num_imported_funcs := 0#usize
  num_imported_globals := 0#usize

/-- A context with no locals and the results of `resultI32`. -/
def ctx : code.Context := ⟨alloc.vec.Vec.new _, resultI32.results⟩

/-- A `br_table` with targets `[0]` and default `1`. -/
def table : instr := BrTable.instruction [0#u32] 1#u32

/-- The body of the block: `unreachable; table`. -/
def inner : List instr := [.UNREACHABLE, table]

/-- The instruction list for `bytes`. -/
def ops : List instr := [.BLOCK (blockType (.Value .I64)) inner, .DROP, .UNREACHABLE]

private theorem lookup : env.types.val[(0#u32).val]? = some resultI32 := rfl

private theorem table_wf : wf_instr table := BrTable.instruction_wf _ _

private theorem inner_wf : Forall wf_instr inner := by
  simp only [inner, Forall, List.mem_cons, List.not_mem_nil, or_false]
  rintro op (rfl | rfl)
  · exact .instr_case_1
  · exact table_wf

private theorem block_wf : wf_instr (.BLOCK (blockType (.Value .I64)) inner) :=
  .instr_case_4 _ _ (blockType_wf _) inner_wf

private theorem bottom_sub (t : valtype) : Resulttype_sub (.mk_list [.BOT]) (.mk_list [t]) :=
  .mk_Resulttype_sub _ _ rfl (by simpa [Forall₂] using Valtype_sub.bot t)

/-- The generated `br_table` rule types `table` with a bottom operand for labels of unlike types
`[i64]` and `[i32]`. -/
theorem table_typed (C : context) (hC : wf_context C)
    (hlabels : C.LABELS = [.mk_list [.I64], .mk_list [.I32]]) :
    Instr_ok C table (.mk_functype (.mk_list [.BOT, .I32]) (.mk_list [.I64])) := by
  apply Instr_ok.br_table C [.mk_uN 0] (.mk_uN 1) [] [.BOT] [.I64]
  · simp [Forall, hlabels, proj_uN_0]
  · simpa [Forall, hlabels, proj_uN_0] using bottom_sub .I64
  · simp [hlabels, proj_uN_0]
  · simpa [hlabels, proj_uN_0] using bottom_sub .I32
  · exact hC
  · exact table_wf

/-- The generated typing rules accept the body `ops`. -/
theorem typed : FunctionTyped env ctx.locals resultI32 ops := by
  let C := functionContext env ctx.locals resultI32
  have hC : wf_context C :=
    Control.enter_context_wf _ (EnvTranslation.context_wf env ⟨ctx.locals, resultI32.results⟩) _
  let D := Control.labelContext [.I64] ++ C
  have hD : wf_context D := Control.enter_context_wf C hC _
  have hlabels : D.LABELS = [.mk_list [.I64], .mk_list [.I32]] := rfl
  have hi : Instrs_ok D inner (.mk_functype (.mk_list []) (.mk_list [.I64])) :=
    Instrs_ok.seq D [.UNREACHABLE] [table] [] [.I64] [.BOT, .I32]
      (.instr D _ _ _ (.unreachable D [] [.BOT, .I32] hD .instr_case_1) hD .instr_case_1)
      (.instr D _ _ _ (table_typed D hD hlabels) hD table_wf) hD
      (by simp [Forall, wf_instr.instr_case_1]) (by simpa [Forall] using table_wf)
  have hbt := blockType_ok env C hC rfl (.Value .I64) [] [.I64] rfl rfl
  have hb : Instr_ok C (.BLOCK (blockType (.Value .I64)) inner)
      (.mk_functype (.mk_list []) (.mk_list [.I64])) :=
    .block C _ inner _ _ hbt hi hC block_wf (Control.labelContext_wf _)
  have hbd := Instrs_ok.seq C [.BLOCK (blockType (.Value .I64)) inner] [.DROP]
      [] [] [.I64] (.instr C _ _ _ hb hC block_wf)
      (.instr C _ _ _ (.drop C .I64 hC .instr_case_2) hC .instr_case_2) hC
      (by simpa [Forall] using block_wf) (by simp [Forall, wf_instr.instr_case_2])
  exact Instrs_ok.seq C _ [.UNREACHABLE] [] [.I32] [] hbd
    (.instr C _ _ _ (.unreachable C [] [.I32] hC .instr_case_1) hC .instr_case_1) hC
    (by simpa [Forall] using And.intro block_wf wf_instr.instr_case_2)
    (by simp [Forall, wf_instr.instr_case_1])

private theorem single_encoding (b : U8) (h : b.val < 128) : Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

/-- `bytes` is a well-formed Wasm 1.0 encoding of `ops`. -/
theorem encoded : Wasm1.BodyEncoding bytes ops := by
  have h0 : Wasm1.At bytes 0#usize (.block (.Value .I64)) 2#usize :=
    ⟨[0x02#u8, 0x7E#u8], ⟨0x02#u8, [0x7E#u8], rfl, .block .i64⟩, ⟨rfl, rfl, by decide⟩⟩
  have h2 : Wasm1.At bytes 2#usize (.plain .UNREACHABLE) 3#usize :=
    ⟨[0x00#u8], ⟨0x00#u8, [], rfl, .unreachable⟩, ⟨rfl, rfl, by decide⟩⟩
  have h3 : Wasm1.At bytes 3#usize (.plain table) 7#usize :=
    ⟨[0x0E#u8, 1#u8, 0#u8, 1#u8], ⟨0x0E#u8, [1#u8, 0#u8, 1#u8], rfl,
      .brTable [0#u32] 1#u32 (single_encoding 1#u8 (by decide))
        (.cons (single_encoding 0#u8 (by decide)) .nil) (single_encoding 1#u8 (by decide))⟩,
      ⟨rfl, rfl, by decide⟩⟩
  have h7 : Wasm1.At bytes 7#usize .end_ 8#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have h8 : Wasm1.At bytes 8#usize (.plain .DROP) 9#usize :=
    ⟨[0x1A#u8], ⟨0x1A#u8, [], rfl, .drop⟩, ⟨rfl, rfl, by decide⟩⟩
  have h9 : Wasm1.At bytes 9#usize (.plain .UNREACHABLE) 10#usize :=
    ⟨[0x00#u8], ⟨0x00#u8, [], rfl, .unreachable⟩, ⟨rfl, rfl, by decide⟩⟩
  have h10 : Wasm1.At bytes 10#usize .end_ 11#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have hi := Wasm2.Emits.simple (Wasm2.Emits.simple .nil (.plain .UNREACHABLE .instr_case_1))
    (.plain table table_wf)
  have ho := Wasm2.Emits.simple (Wasm2.Emits.simple
    (Wasm2.Emits.block (.Value .I64) .nil hi) (.plain .DROP .instr_case_2))
    (.plain .UNREACHABLE .instr_case_1)
  refine ⟨_, 11#usize,
    ((((((Wasm1.Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h3).snoc h7).snoc h8).snoc h9 |>.snoc h10,
    rfl, ?_⟩
  exact ⟨_, rfl, ho⟩

/-- `bytes` is a valid Wasm 2.0 body for type 0, and `Profile.run .Wasm2` accepts it. -/
theorem wasm2_accepted :
    Profile.Body .Wasm2 bytes env ctx.locals 0#u32 ∧
      Profile.run .Wasm2 bytes env ctx 0#u32 = .ok (.Ok ()) := by
  have body : Profile.Body .Wasm2 bytes env ctx.locals 0#u32 :=
    ⟨resultI32, ops, lookup, trivial, Wasm1.BodyEncoding.to_wasm2 encoded, typed, trivial,
      by simp [ops, inner, table, BrTable.instruction, DeclaredReferences.Instructions,
        DeclaredReferences.instructionIndices]⟩
  refine ⟨body, Profile.run.complete .Wasm2 bytes env ctx 0#u32 ?_ ?_ body⟩
  · constructor <;> intro ft hft <;>
      simp [env, resultI32, Profile.FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS,
        limits.MAX_MULTI_VALUE_RESULTS] at hft ⊢
    subst hft
    simp
  · simp [bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]

/-- The Wasm 1.0 `br_table` restriction (all targets have the same type) fails for `table` when
the labels are `[i64]` and `[i32]`. -/
theorem table_not_wasm1 (C : context)
    (hlabels : C.LABELS = [.mk_list [.I64], .mk_list [.I32]]) :
    ¬ Wasm1.Instruction C table := by
  intro h
  have hs := Wasm1.Instruction.br_table_iff.mp h
  have heq := hs (.mk_uN 0) (by simp)
  simp [hlabels, proj_uN_0] at heq

/-- The instruction tree `ops` fails the recursive Wasm 1.0 profile `Wasm1.Instructions`. -/
theorem ops_not_wasm1 : ¬ Wasm1.Instructions (functionContext env ctx.locals resultI32) ops := by
  intro h
  cases h with
  | cons hb _ =>
    generalize heq : instr.BLOCK (blockType (.Value .I64)) inner = op at hb
    cases hb with
    | leaf _ op hleaf => simp [← heq, Wasm1.Leaf] at hleaf
    | block _ result body hi =>
      have hresult : result = some .I64 := by
        have h := (instr.BLOCK.inj heq).1
        simp [blockType, Translate.valueType] at h
        exact h.symm
      subst result
      have hbody := (instr.BLOCK.inj heq).2
      subst body
      cases hi with
      | cons _ htail =>
        cases htail with
        | cons ht _ => exact table_not_wasm1 _ rfl ht
    | loop _ _ _ _ => cases heq
    | ifElse _ _ _ _ _ _ => cases heq

/-- `bytes` is not a valid Wasm 1.0 body, so `Profile.run .Wasm1` does not accept it. -/
theorem wasm1_rejected :
    ¬ Profile.Body .Wasm1 bytes env ctx.locals 0#u32 ∧
      Profile.run .Wasm1 bytes env ctx 0#u32 ≠ .ok (.Ok ()) := by
  have invalid : ¬ Profile.Body .Wasm1 bytes env ctx.locals 0#u32 := by
    rintro ⟨ft, ops', hi, _, he, _, hp, _⟩
    have hft : ft = resultI32 := Option.some.inj (hi.symm.trans lookup)
    subst ft
    have hops : ops' = ops :=
      Wasm2.BodyEncoding.unique (Wasm1.BodyEncoding.to_wasm2 he) (Wasm1.BodyEncoding.to_wasm2 encoded)
    subst ops'
    exact ops_not_wasm1 hp
  refine ⟨invalid, fun haccepted => invalid ?_⟩
  exact Profile.run.sound .Wasm1 bytes env ctx 0#u32 resultI32 lookup
    (by simp [Profile.FuncType, resultI32]) haccepted

end Itasca.Examples.Wasm1ProfileBoundary
