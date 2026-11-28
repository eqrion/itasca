import Itasca
import Itasca.Examples.Module.Basic
import Itasca.Examples.Module.SliceLayout

open WebAssembly

/-!
Proofs for Examples.

This module collects Module, DeclaredReferences, Body.
Each section documents its contracts and consumers.
-/

/-! ## Module -/

section

/-!
# A two-result module under Wasm 2.0

A module with one function of type `[] -> [i32, i64]` whose body is `i32.const 0; i64.const 0`.
`accepted` and `validated` show that `metadata.validate_module` accepts its bytes under Wasm 2.0 via
the shared completeness and soundness theorems. `typed` builds `Module_ok` directly from
declarative pieces, without running the validator.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Module

open Itasca.Examples.Module.Support (leb one padded omitted)

open Itasca.Binary Module.Elaboration

/-- The function type `[] -> [i32, i64]`. -/
def functionType : wasm_types.FuncType :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.I32, .I64] (by scalar_tac)⟩

/-- The code entry with no locals and body `i32.const 0; i64.const 0`. -/
def entry : Code := ⟨[], [Spec.i32Const 0#i32, Spec.Constants.i64 0#i64]⟩

/-- The environment holding `functionType` and one function of that type. -/
def env : metadata.ModuleMetadata metadata.CodeMetadata :=
  { Examples.Module.Basic.emptyEnv with code := { Examples.Module.Basic.emptyEnv.code with
      types := alloc.vec.Vec.from [functionType] (by scalar_tac)
      funcs := alloc.vec.Vec.from [⟨0#u32, false, false⟩] (by scalar_tac) } }

private def declarations : Module.Environment.Declarations := { types := [functionType], functions := [0#u32] }

/-- The decoded module that `env` and `entry` elaborate to. -/
def raw : Binary.Module := fromEnv env declarations [entry] []

/-- The module bytes: header, type section, function section and code section. -/
def input : Slice U8 := Examples.Module.Support.bytes
  (magicVersion ++ [1#u8, 6#u8, 1#u8, 0x60#u8, 0#u8, 2#u8, 0x7F#u8, 0x7E#u8,
    3#u8, 2#u8, 1#u8, 0#u8,
    10#u8, 8#u8, 1#u8, 6#u8, 0#u8, 0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x0B#u8])
  (by simp [magicVersion]; scalar_tac)

private theorem represented : Module.Environment.Represents env declarations := by
  constructor <;> first | rfl | (constructor <;> rfl)

private theorem environment_valid : Module.Environment.Valid env := by
  constructor <;> simp [env, Examples.Module.Basic.emptyEnv, Itasca.CodeEntry.FuncTypeWithinLimits,
    functionType, limits.MAX_MULTI_VALUE_PARAMS, limits.MAX_MULTI_VALUE_RESULTS,
    Module.References.Coherent, Module.References.collected, Translation.Environment.declaredReferences]

private theorem entry_typed : CodeEntry.Typed env.code 0#u32 entry := by
  refine ⟨by simp [env], ?_, ?_⟩
  · let C := CodeEntry.bodyContext env.code [] [] [.I32, .I64]
    have hC : wf_context C := by
      constructor <;> simp [env, Examples.Module.Basic.emptyEnv, Forall]
    have hp := ((Body.Stack.TypedPrefix.empty C hC).i32_const hC 0#i32).i64_const hC 0#i64
    simpa [env, functionType, entry, Code.declared, CodeEntry.instructionType, C,
      Body.Stack.stackTypes, Translation.valueType] using hp.typed _
        (Body.Stack.realizes_default false [.Val .I32, .Val .I64])
  · simp [entry, Spec.DeclaredReferences.Instructions, Spec.DeclaredReferences.instructionsIndices,
      Spec.DeclaredReferences.instructionIndices, Spec.i32Const, Spec.Constants.i64]

private theorem codes_typed : List.Forall₂
    (fun idx code => CodeEntry.Typed env.code idx code ) declarations.functions [entry] :=
  .cons entry_typed .nil

/-- The generated `Module_ok` holds for `raw`, assembled from declarative body typing and
environment caches without a successful validator call. -/
theorem typed : Module_ok (moduleOf raw) := by
  exact Module.Elaboration.typed represented environment_valid
    (by simp [declarations]) (by simp [env, Examples.Module.Basic.emptyEnv])
    codes_typed (by simp) (by simp [env, Examples.Module.Basic.emptyEnv]) (List.Forall₂.nil : List.Forall₂ (Module.Externals.ExportResolves env.code) [] [])

private theorem module_zero32 : Binary.SignedLeb32.Encoding [0#u8] (0#i32).val := by
  refine ⟨[], 0#u8, rfl, by decide, by simp, by decide, ?_, by decide, by decide⟩
  norm_num [Binary.SignedLeb.finalValue, Binary.Leb128.payload_nil, Binary.Leb128.payload_cons]

private theorem module_zero64 : Binary.SignedLeb64.Encoding [0#u8] (0#i64).val := by
  refine ⟨[], 0#u8, rfl, by decide, by simp, by decide, ?_, by decide, by decide⟩
  norm_num [Binary.SignedLeb.finalValue, Binary.Leb128.payload_nil, Binary.Leb128.payload_cons]

private theorem body_encoding : Itasca.CodeEntry.BodyBytes entry.body
    [0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x0B#u8] := by
  refine ⟨[.plain (Spec.i32Const 0#i32), .plain (Spec.Constants.i64 0#i64), .end_], ?_, ?_⟩
  · exact WebAssembly.Binary.Rep.cons
      (show Body.TokenEncoding (.plain (Spec.i32Const 0#i32)) [0x41#u8,0#u8] from
        ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 module_zero32)⟩)
      (WebAssembly.Binary.Rep.cons
        (show Body.TokenEncoding (.plain (Spec.Constants.i64 0#i64)) [0x42#u8,0#u8] from
          ⟨0x42#u8, [0#u8], rfl, .plain (.i64Const 0#i64 module_zero64)⟩)
        (WebAssembly.Binary.Rep.cons (show Body.TokenEncoding .end_ [0x0B#u8] from
          ⟨0x0B#u8, [], rfl, .end_⟩) .nil))
  · exact ⟨_, rfl, .simple (.simple .nil (.plain _ (Spec.i32_const_wf _)))
      (.plain _ (Spec.Constants.i64_wf _))⟩

/-- `input` encodes `raw` within the module and function size limits, stated directly on the byte
lists for Wasm 2.0. No parser execution or canonical re-encoding is assumed. -/
theorem encoded : ModuleEncodingWithinLimits raw input.val := by
  constructor
  · simp [input, Examples.Module.Support.bytes, alloc.vec.Vec.deref, magicVersion, limits.MAX_MODULE_BYTES]
  · apply Itasca.Binary.Source.moduleEncodingWith @Itasca.Binary.Source.codeWithinLimits
    refine ⟨[1#u8,6#u8,1#u8,0x60#u8,0#u8,2#u8,0x7F#u8,0x7E#u8], [],
      [3#u8,2#u8,1#u8,0#u8], [], [], [], [], [], [], [],
      [10#u8,8#u8,1#u8,6#u8,0#u8,0x41#u8,0#u8,0x42#u8,0#u8,0x0B#u8], [], [],
      ?_, omitted _ _ _, ?_, omitted _ _ _, omitted _ _ _, omitted _ _ _,
      omitted _ _ _, omitted _ _ _, omitted _ _ _, ?_, ?_, omitted _ _ _, .nil, rfl, ?_⟩
    · apply padded _ 6#u8 _ (one (x := functionType) ?_) rfl
      apply FuncTypeEncoding.reader_parts.mpr
      refine ⟨[0#u8], [2#u8,0x7F#u8,0x7E#u8], ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩, ?_, rfl⟩
      exact ⟨[2#u8], [0x7F#u8,0x7E#u8], leb 2#u8,
        WebAssembly.Binary.Rep.cons (show ValueTypeEncoding .I32 [0x7F#u8] from ValueTypeEncoding.reader_bytes.mpr rfl)
          (WebAssembly.Binary.Rep.cons (show ValueTypeEncoding .I64 [0x7E#u8] from ValueTypeEncoding.reader_bytes.mpr rfl) .nil), rfl⟩
    · exact padded _ 2#u8 _ (one (leb 0#u8)) rfl
    · exact omitted _ _ _
    · apply padded _ 8#u8 _ (one (x := entry) ?_) rfl
      exact ⟨by simp [entry, Code.declared, limits.MAX_LOCALS], [6#u8], [0#u8],
        [0x41#u8,0#u8,0x42#u8,0#u8,0x0B#u8], leb 6#u8,
        ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩,
        ⟨body_encoding, by simp [limits.MAX_FUNCTION_BYTES]⟩, rfl⟩
    · simp [DataCountValid, WebAssembly.Binary.DataCountValidWith, raw, fromEnv, declarations, env, Examples.Module.Basic.emptyEnv, entry,
        instructionsUseData, instructionUsesData, Spec.i32Const, Spec.Constants.i64]

/-- `metadata.validate_module` accepts `input` under Wasm 2.0, and the decoded metadata matches
`raw`, by the shared completeness theorem. -/
theorem accepted : ∃ decoded, metadata.validate_module input = .ok (.Ok decoded) ∧
    Matches decoded raw ∧ AccessorTypes decoded raw := by
  exact metadata.validate_module.complete_with_metadata input raw encoded
    (by simp [ModuleSignaturesWithinLimits, raw, fromEnv, declarations, env, functionType,
      Itasca.CodeEntry.FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS, limits.MAX_MULTI_VALUE_RESULTS])
    (Module.Elaboration.elaborates represented environment_valid codes_typed) typed
    (Module.Elaboration.restrictions represented environment_valid codes_typed)

/-- The accepted bytes also satisfy the shared module soundness theorem under Wasm 2.0. -/
theorem validated : ∃ decoded, metadata.validate_module input = .ok (.Ok decoded) ∧
    Module.Sound.Validated input decoded := by
  obtain ⟨decoded, ha, _, _⟩ := accepted
  exact ⟨decoded, ha, metadata.validate_module.sound input decoded ha⟩

end Itasca.Examples.Module

end

/-! ## DeclaredReferences -/

section

/-!
# The `ref.func` declaration condition

Wasm 2.0 requires every function index used by `ref.func` inside a function body to occur
elsewhere in the module, outside the functions and the start declaration (for example in an
element segment, an export or a global initializer). The generated `Module_ok` omits this
condition. `generated_typing_missing_premise` exhibits a module accepted by `Module_ok` and
rejected by the `Spec.DeclaredReferences.Module` supplement; the remaining examples show which
declaration sites satisfy it.
-/

namespace Itasca.Examples.DeclaredReferences

open Itasca.Spec.DeclaredReferences

/-- The function type `[] -> [funcref]`. -/
def referenceType : functype := .mk_functype (.mk_list []) (.mk_list [.FUNCREF])

/-- A function whose body is `ref.func 0`, returning its own reference. -/
def selfReference : func := .FUNC (.mk_uN 0) [] [.REF_FUNC (.mk_uN 0)]

/-- A module containing only `selfReference`, so function 0 is referenced but never declared. -/
def undeclared : WebAssembly.module :=
  .MODULE [.TYPE referenceType] [] [selfReference] [] [] [] [] [] none []

private def moduleContext : context :=
  ⟨[referenceType], [referenceType], [], [], [], [], [], [], [], none⟩

private theorem zero_wf : wf_uN 32 (.mk_uN 0) := by
  constructor
  decide

private theorem reference_wf : wf_instr (.REF_FUNC (.mk_uN 0)) :=
  .instr_case_41 _ zero_wf

private theorem function_wf : wf_func selfReference := by
  apply wf_func.func_case_0
  · exact zero_wf
  · simpa [Forall] using reference_wf

private theorem no_memory_context_wf (C : context)
    (ht : C.TABLES = []) (hm : C.MEMS = []) : wf_context C := by
  cases C
  constructor <;> simp_all [Forall]

/-- The generated `ref.func` rule types `ref.func 0` once function 0 exists, and requires no
declaration. -/
theorem generated_instruction_typed (C : context) (hC : wf_context C)
    (hf : C.FUNCS = [referenceType]) :
    Instr_ok C (.REF_FUNC (.mk_uN 0)) referenceType := by
  apply Instr_ok.ref_func C (.mk_uN 0) referenceType
  · simp [hf, proj_uN_0]
  · simp [hf, proj_uN_0]
  · exact hC
  · exact reference_wf

private theorem generated_function_typed : Func_ok moduleContext selfReference referenceType := by
  apply Func_ok.mk_Func_ok moduleContext (.mk_uN 0) [] [.REF_FUNC (.mk_uN 0)] [] [.FUNCREF]
  · simp [moduleContext, proj_uN_0, referenceType]
  · simp [moduleContext, proj_uN_0, referenceType]
  · simp [Forall]
  · apply Expr_ok.mk_Expr_ok
    · apply Instrs_ok.instr
      · exact generated_instruction_typed _ (no_memory_context_wf _ rfl rfl) rfl
      · exact no_memory_context_wf _ rfl rfl
      · exact reference_wf
    · exact no_memory_context_wf _ rfl rfl
    · simpa [Forall] using reference_wf
  · exact no_memory_context_wf _ rfl rfl
  · exact function_wf
  · exact no_memory_context_wf _ rfl rfl

/-- The generated `Module_ok` accepts `undeclared`. -/
theorem generated_module_typed : Module_ok undeclared := by
  unfold undeclared
  apply Module_ok.mk_Module_ok
    (ft'_lst := [referenceType]) (ixt_lst := []) (C' := moduleContext)
    (gt_lst := []) (tt_lst := []) (mt_lst := []) (rt_lst := []) (C := moduleContext)
    (ft_lst := [referenceType]) (xt_lst := [])
    (ift_lst := []) (igt_lst := []) (itt_lst := []) (imt_lst := [])
    (var_0 := []) (var_1 := []) (var_2 := []) (var_3 := []) (v_n := 0)
  · constructor
  · constructor
  · constructor
  · constructor
  · rfl
  · simpa [Forall₂] using Type_ok.mk_Type_ok referenceType (.mk_Functype_ok [] [.FUNCREF])
  · rfl
  · simp [Forall₂]
  · rfl
  · simp [Forall₂]
  · rfl
  · simp [Forall₂]
  · rfl
  · simp [Forall₂]
  · rfl
  · simp [Forall₂]
  · simp [Forall]
  · rfl
  · simpa [Forall₂] using generated_function_typed
  · simp [Forall]
  · rfl
  · simp [Forall₂]
  · decide
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Forall]
  · exact no_memory_context_wf _ rfl rfl
  · exact no_memory_context_wf _ rfl rfl
  · simp [Forall]
  · simp [Forall]
  · simp [Forall]
  · constructor
    · simp [Forall]
    · simpa [Forall] using function_wf
    all_goals simp [Forall]
  · exact no_memory_context_wf _ rfl rfl
  · exact no_memory_context_wf _ rfl rfl
  · exact no_memory_context_wf _ rfl rfl
  · rfl

/-- The `Spec.DeclaredReferences.Module` supplement rejects `undeclared`. -/
theorem undeclared_rejected : ¬ Spec.DeclaredReferences.Module undeclared := by
  simp [Spec.DeclaredReferences.Module, undeclared, declarations, Function, selfReference,
    Instructions, instructionsIndices, instructionIndices]

/-- `undeclared` is accepted by `Module_ok` and rejected by the supplement, so the generated rules
need it. -/
theorem generated_typing_missing_premise :
    Module_ok undeclared ∧ ¬ Spec.DeclaredReferences.Module undeclared :=
  ⟨generated_module_typed, undeclared_rejected⟩

/-- `undeclared` plus a declarative element segment listing `ref.func 0`. -/
def declarative : WebAssembly.module :=
  .MODULE [.TYPE referenceType] [] [selfReference] [] [] []
    [.ELEM .FUNCREF [[.REF_FUNC (.mk_uN 0)]] .DECLARE] [] none []

/-- A declarative element segment declares function 0. -/
theorem declarative_declares : Spec.DeclaredReferences.Module declarative := by
  simp [Spec.DeclaredReferences.Module, declarative, declarations, Function, selfReference,
    Instructions, instructionsIndices, instructionIndices, elementIndices, elementModeIndices]

/-- `undeclared` plus an export of function 0. -/
def exported : WebAssembly.module :=
  .MODULE [.TYPE referenceType] [] [selfReference] [] [] [] [] [] none
    [.EXPORT (.mk_name []) (.FUNC (.mk_uN 0))]

/-- Exporting function 0 declares it. -/
theorem export_declares : Spec.DeclaredReferences.Module exported := by
  simp [Spec.DeclaredReferences.Module, exported, declarations, Function, selfReference,
    Instructions, instructionsIndices, instructionIndices, exportIndices]

/-- `undeclared` plus a global whose initializer is `ref.func 0`. -/
def globalReference : WebAssembly.module :=
  .MODULE [.TYPE referenceType] [] [selfReference]
    [.GLOBAL (.mk_globaltype none .FUNCREF) [.REF_FUNC (.mk_uN 0)]] [] [] [] [] none []

/-- A global initializer using `ref.func 0` declares function 0. -/
theorem global_declares : Spec.DeclaredReferences.Module globalReference := by
  simp [Spec.DeclaredReferences.Module, globalReference, declarations, Function, selfReference,
    Instructions, instructionsIndices, instructionIndices, globalIndices]

/-- Making function 0 the start function does not declare it. The example concerns the
declaration condition only, not the start function's type. -/
theorem start_does_not_declare :
    ¬ Spec.DeclaredReferences.Module
      (.MODULE [.TYPE referenceType] [] [selfReference] [] [] [] [] []
        (some (.START (.mk_uN 0))) []) := by
  simp [Spec.DeclaredReferences.Module, declarations, Function, selfReference,
    Instructions, instructionsIndices, instructionIndices]

/-- A `ref.func 0` nested in `block`, `loop` and `if` is still checked for declaration. -/
theorem nested_reference_checked :
    ¬ Instructions []
      [.BLOCK (._RESULT none) [.LOOP (._RESULT none)
        [.IFELSE (._RESULT none) [] [.REF_FUNC (.mk_uN 0)]]]] := by
  simp

/-- A `call 0` needs no declaration. -/
theorem ordinary_call_needs_no_declaration : Instructions [] [.CALL (.mk_uN 0)] := by
  simp

end Itasca.Examples.DeclaredReferences

end

/-! ## Body -/

section

/-!
# Wasm 2.0 function bodies

Block types given by a type index, a missing `else` arm, `loop` branches, and `br_table` with
differently typed targets, all with multiple parameters or results. `Examples.Grammar` checks
the block-type grammar and the identity `if` rule. `Examples.Body` gives four function bodies,
each with a byte string, a declarative typing derivation (`block_typed`, `if_typed`, `loop_typed`,
`table_typed`) and an encoding derivation. `block_accepted` and its siblings combine them with
`code.bodyCore.complete` to show the body validator accepts
the bytes, and `block_validated` and its siblings derive soundness certificates from the same runs.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Grammar

open Itasca.Body

/-- A type index uses signed LEB, including nonminimal positive encodings. -/
theorem padded_index : BlockEncoding (.TypeIndex 0#u32) [128#u8, 0#u8] := by
  apply BlockEncoding.reader_form.mpr
  refine ⟨[128#u8], 0#u8, rfl, by decide, ?_, by decide, ?_, by decide, by decide⟩
  · simp
  · norm_num [Binary.SignedLeb.finalValue, Binary.Leb128.payload_nil, Binary.Leb128.payload_cons]

/-- Padded negative s33 encodings are not inline value-type tags. -/
theorem padded_negative_not_inline (t : wasm_types.ValueType) :
    ¬ BlockEncoding (.Value t) [255#u8, 127#u8] := by
  simp [BlockEncoding.reader_form]

/-- The body `block (type 0x80 0x00) end end`, with type index 0 in a padded two-byte encoding. -/
def bytes : Slice U8 := alloc.vec.Vec.deref (alloc.vec.Vec.from
  [0x02#u8, 0x80#u8, 0x00#u8, 0x0B#u8, 0x0B#u8] (by scalar_tac))

/-- `bytes` decodes to a `block` with type index 0, whether or not type 0 exists in any
environment. -/
theorem indexed_body : BodyEncoding bytes [.BLOCK (blockType (.TypeIndex 0#u32)) []] := by
  have hb : At bytes 0#usize (.block (.TypeIndex 0#u32)) 3#usize :=
    ⟨_, ⟨0x02#u8, [0x80#u8, 0x00#u8], rfl, .block padded_index⟩, rfl, rfl, by decide⟩
  have he : At bytes 3#usize .end_ 4#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have hf : At bytes 4#usize .end_ 5#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  exact ⟨_, 5#usize, (((Consumed.nil 0#usize (by decide)).snoc hb).snoc he).snoc hf,
    rfl, _, rfl, WebAssembly.Binary.EmitsWith.block (toSpec := Itasca.Body.blockType) _ .nil .nil⟩

/-- An `if` without an `else` arm has type `[i32, i64, i32] -> [i32, i64]` when its block type is
the identity on `[i32, i64]`. scalar frames have no counterpart for this rule. -/
theorem identity_if (env : metadata.CodeMetadata) (C : context) (hC : wf_context C)
    (htypes : C.TYPES = env.types.val.map Translation.Environment.funcType) (index : U32)
    (hin : resolve env (inputs (.TypeIndex index)) = some [.I32, .I64])
    (hout : resolve env (outputs (.TypeIndex index)) = some [.I32, .I64]) :
    Instr_ok C (.IFELSE (blockType (.TypeIndex index)) [] [])
      (.mk_functype (.mk_list [.I32, .I64, .I32]) (.mk_list [.I32, .I64])) := by
  let f := Body.Frames.Saved.fresh 0#usize .then_ (.TypeIndex index) [.I32, .I64] [.I32, .I64]
  have hh : Body.Frames.Header env C f := ⟨rfl, hin, hout, trivial, .nil⟩
  have ht := TypedPrefix.start (Body.Frames.enter C .then_ [.I32, .I64] [.I32, .I64])
    (Body.Frames.enter_wf C hC _ _ _) [.I32, .I64]
  exact (Body.Frames.Closed.then_ _ _).typed (f := f) hC htypes hh ht
    (Body.Stack.realizes_default false [.Val .I32, .Val .I64]) (fun _ => rfl)

end Itasca.Examples.Grammar

open Aeneas Aeneas.Std

namespace Itasca.Examples.Body

open Itasca.Body

/-- A byte slice built from a list. -/
def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

/-- The empty local list. -/
def locals : alloc.vec.Vec wasm_types.ValueType := alloc.vec.Vec.new _
/-- The function type `[] -> [i32, i64]`. -/
def pairResult : wasm_types.FuncType :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.I32, .I64] (by scalar_tac)⟩
/-- The function type `[i32, i64] -> [i32, i64]`. -/
def pairIdentity : wasm_types.FuncType :=
  ⟨alloc.vec.Vec.from [.I32, .I64] (by scalar_tac), alloc.vec.Vec.from [.I32, .I64] (by scalar_tac)⟩
/-- The function type `[i32, i64] -> []`. -/
def pairLoop : wasm_types.FuncType :=
  ⟨alloc.vec.Vec.from [.I32, .I64] (by scalar_tac), alloc.vec.Vec.new _⟩
/-- The function type `[] -> []`. -/
def emptyResult : wasm_types.FuncType := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩
/-- The function type `[] -> [f32, f64]`. -/
def floatResult : wasm_types.FuncType :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.F32, .F64] (by scalar_tac)⟩

/-- An environment whose type section is `pairResult`, `pairIdentity`, `pairLoop`, `emptyResult`
and `floatResult` (indices 0 to 4), with no functions or other entities. -/
def env : metadata.CodeMetadata :=
  { Examples.Module.Basic.emptyEnv.code with types := alloc.vec.Vec.from [pairResult, pairIdentity, pairLoop, emptyResult, floatResult] (by scalar_tac) }

/-- `env` is within the implementation limits. -/
theorem environment_limits : CodeEntry.EnvironmentWithinLimits env := by
  constructor
  · intro ft hf
    simp [env] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
      simp [pairResult, pairIdentity, pairLoop, emptyResult, floatResult,
        CodeEntry.FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS, limits.MAX_MULTI_VALUE_RESULTS]
  · simp [env, Examples.Module.Basic.emptyEnv]

private theorem unsigned (b : U8) (h : b.val < 128) : Binary.Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Binary.Leb128.payload_nil, Binary.Leb128.payload_cons, Nat.mod_eq_of_lt h]⟩

private theorem index_encoding (b : U8) (idx : U32) (hb : b.val < 64) (hi : idx.val = b.val) :
    BlockEncoding (.TypeIndex idx) [b] := by
  apply BlockEncoding.reader_form.mpr
  refine ⟨[], b, rfl, by simp, by simp, by omega, ?_, ?_, ?_⟩
  · simp [Binary.SignedLeb.finalValue, Binary.Leb128.payload_nil, Binary.Leb128.payload_cons, Nat.not_le.mpr hb, hi]
  · simp [Binary.SignedLeb33.format]
  · have := idx.hmax; simp [Binary.SignedLeb33.format]; scalar_tac

private theorem body_zero32 : Binary.SignedLeb32.Encoding [0#u8] (0#i32).val := by
  refine ⟨[], 0#u8, rfl, by decide, by simp, by decide, ?_, by decide, by decide⟩
  norm_num [Binary.SignedLeb.finalValue, Binary.Leb128.payload_nil, Binary.Leb128.payload_cons]

private theorem body_zero64 : Binary.SignedLeb64.Encoding [0#u8] (0#i64).val := by
  refine ⟨[], 0#u8, rfl, by decide, by simp, by decide, ?_, by decide, by decide⟩
  norm_num [Binary.SignedLeb.finalValue, Binary.Leb128.payload_nil, Binary.Leb128.payload_cons]

/-- The instructions `i32.const 0; i64.const 0`. -/
def pairOps : List instr := [Spec.i32Const 0#i32, Spec.Constants.i64 0#i64]

private theorem pair_wf : Forall wf_instr pairOps := by
  simpa [pairOps, Forall] using And.intro (Spec.i32_const_wf 0#i32) (Spec.Constants.i64_wf 0#i64)

private theorem pair_typed (C : context) (hC : wf_context C) :
    Instrs_ok C pairOps (.mk_functype (.mk_list []) (.mk_list [.I32, .I64])) := by
  have hp := ((TypedPrefix.start C hC []).i32_const hC 0#i32).i64_const hC 0#i64
  simpa [pairOps, Body.Stack.stackTypes, Translation.valueType] using hp.typed _
    (Body.Stack.realizes_default false [.Val .I32, .Val .I64])

private theorem identity_typed (C : context) (hC : wf_context C) (ts : List valtype) :
    Instrs_ok C [] (.mk_functype (.mk_list ts) (.mk_list ts)) := by
  simpa using Instrs_ok.frame C [] ts [] [] (.empty C hC) hC (by simp [Forall])

private def rootContext (ft : wasm_types.FuncType) : context :=
  Body.Control.labelContext (ft.results.val.map Translation.valueType) ++ bodyContext env locals ft

private theorem root_wf (ft : wasm_types.FuncType) : wf_context (rootContext ft) :=
  Body.Control.enter_context_wf _ (Translation.Environment.context_wf env ⟨locals, ft.results⟩) _

/-- A `block` of type index 1 with an empty body. -/
def identityBlock : instr := .BLOCK (blockType (.TypeIndex 1#u32)) []
/-- `pairOps` followed by `identityBlock`. -/
def blockOps : List instr := pairOps ++ [identityBlock]
/-- The body bytes `i32.const 0; i64.const 0; block (type 1) end; end`. -/
def blockBytes : Slice U8 := bytes [0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x02#u8, 1#u8, 0x0B#u8, 0x0B#u8]

private theorem block_wf : wf_instr identityBlock :=
  .instr_case_4 _ _ (block_type_wf _) (by simp [Forall])

/-- A `block` with type index 1 consumes and returns `[i32, i64]` in order, so `blockOps` has type
`[] -> [i32, i64]`. -/
theorem block_typed : FunctionTyped env locals pairResult blockOps := by
  let C := rootContext pairResult
  have hC := root_wf pairResult
  have hbt := block_type_ok env C hC rfl (.TypeIndex 1#u32) [.I32, .I64] [.I32, .I64] rfl rfl
  have hi : Instr_ok C identityBlock (.mk_functype (.mk_list [.I32, .I64]) (.mk_list [.I32, .I64])) :=
    .block C _ [] _ _ hbt (identity_typed _ (Body.Control.enter_context_wf C hC _) _)
      hC block_wf (Body.Control.label_context_wf _)
  exact .seq C pairOps [identityBlock] [] [.I32, .I64] [.I32, .I64] (pair_typed C hC)
    (.instr C _ _ _ hi hC block_wf) hC pair_wf (by simpa [Forall] using block_wf)

/-- An `if` of type index 1 with empty arms and no `else`. -/
def identityIf : instr := .IFELSE (blockType (.TypeIndex 1#u32)) [] []
/-- `pairOps; i32.const 0; identityIf`. -/
def ifOps : List instr := pairOps ++ [Spec.i32Const 0#i32, identityIf]
/-- The body bytes `i32.const 0; i64.const 0; i32.const 0; if (type 1) end; end`. -/
def ifBytes : Slice U8 := bytes
  [0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x41#u8, 0#u8, 0x04#u8, 1#u8, 0x0B#u8, 0x0B#u8]

/-- The missing `else` arm passes both parameters through because the block type is the identity,
so `ifOps` has type `[] -> [i32, i64]`. -/
theorem if_typed : FunctionTyped env locals pairResult ifOps := by
  let C := rootContext pairResult
  have hC := root_wf pairResult
  have hp := (((TypedPrefix.start C hC []).i32_const hC 0#i32).i64_const hC 0#i64).i32_const hC 0#i32
  have hprefix : Instrs_ok C (pairOps ++ [Spec.i32Const 0#i32])
      (.mk_functype (.mk_list []) (.mk_list [.I32, .I64, .I32])) := by
    simpa [pairOps, Body.Stack.stackTypes, Translation.valueType] using hp.typed _
      (Body.Stack.realizes_default false [.Val .I32, .Val .I64, .Val .I32])
  have hwf : wf_instr identityIf :=
    .instr_case_6 _ _ _ (block_type_wf _) (by simp [Forall]) (by simp [Forall])
  have hi := Examples.Grammar.identity_if env C hC rfl 1#u32 rfl rfl
  change Instrs_ok C ifOps (.mk_functype (.mk_list []) (.mk_list [.I32, .I64]))
  simpa [ifOps, pairOps, List.append_assoc] using
    Instrs_ok.seq C (pairOps ++ [Spec.i32Const 0#i32]) [identityIf] [] [.I32, .I64] [.I32, .I64, .I32]
      hprefix (.instr C _ _ _ hi hC hwf) hC hp.wellFormed (by simpa [Forall] using hwf)

/-- A `loop` of type index 2 whose body is `br 0`. -/
def loopInstr : instr := .LOOP (blockType (.TypeIndex 2#u32)) [.BR (.mk_uN 0)]
/-- `pairOps` followed by `loopInstr`. -/
def loopOps : List instr := pairOps ++ [loopInstr]
/-- The body bytes `i32.const 0; i64.const 0; loop (type 2) br 0 end; end`. -/
def loopBytes : Slice U8 := bytes
  [0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x03#u8, 2#u8, 0x0C#u8, 0#u8, 0x0B#u8, 0x0B#u8]

/-- A `br 0` inside a `loop` takes the loop's two parameter types `[i32, i64]`, although the loop
has no results, so `loopOps` has type `[] -> []`. -/
theorem loop_typed : FunctionTyped env locals emptyResult loopOps := by
  let C := rootContext emptyResult
  let D := Body.Control.labelContext [.I32, .I64] ++ C
  have hC := root_wf emptyResult
  have hD : wf_context D := Body.Control.enter_context_wf C hC _
  have hbr : wf_instr (.BR (.mk_uN 0)) := .instr_case_7 _ (Translation.Environment.index_wf 0#u32)
  have hi : Instr_ok D (.BR (.mk_uN 0)) (.mk_functype (.mk_list [.I32, .I64]) (.mk_list [])) :=
    .br D (.mk_uN 0) [] [.I32, .I64] [] (by simp [D, Body.Control.label_context_labels, proj_uN_0])
      rfl hD hbr
  have hwf : wf_instr loopInstr := .instr_case_5 _ _ (block_type_wf _) (by simpa [Forall] using hbr)
  have hloop : Instr_ok C loopInstr (.mk_functype (.mk_list [.I32, .I64]) (.mk_list [])) :=
    .loop C _ _ _ _ (block_type_ok env C hC rfl (.TypeIndex 2#u32) [.I32, .I64] [] rfl rfl)
      (.instr D _ _ _ hi hD hbr) hC hwf (Body.Control.label_context_wf _)
  exact .seq C pairOps [loopInstr] [] [] [.I32, .I64] (pair_typed C hC)
    (.instr C _ _ _ hloop hC hwf) hC pair_wf (by simpa [Forall] using hwf)

private theorem pair_emits : Emits [.plain (Spec.i32Const 0#i32), .plain (Spec.Constants.i64 0#i64)] pairOps :=
  .simple (.simple .nil (.plain _ (Spec.i32_const_wf 0#i32))) (.plain _ (Spec.Constants.i64_wf 0#i64))

/-- `blockBytes` decodes to `blockOps`. -/
theorem block_encoded : BodyEncoding blockBytes blockOps := by
  have h0 : At blockBytes 0#usize (.plain (Spec.i32Const 0#i32)) 2#usize :=
    ⟨_, ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 body_zero32)⟩, rfl, rfl, by decide⟩
  have h2 : At blockBytes 2#usize (.plain (Spec.Constants.i64 0#i64)) 4#usize :=
    ⟨_, ⟨0x42#u8, [0#u8], rfl, .plain (.i64Const 0#i64 body_zero64)⟩, rfl, rfl, by decide⟩
  have h4 : At blockBytes 4#usize (.block (.TypeIndex 1#u32)) 6#usize :=
    ⟨_, ⟨0x02#u8, [1#u8], rfl, .block (index_encoding 1#u8 1#u32 (by decide) rfl)⟩, rfl, rfl, by decide⟩
  have h6 : At blockBytes 6#usize (.end_) 7#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have h7 : At blockBytes 7#usize (.end_) 8#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  exact ⟨_, 8#usize, ((((((Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h4).snoc h6).snoc h7), rfl, _, rfl, WebAssembly.Binary.EmitsWith.block (toSpec := Itasca.Body.blockType) (.TypeIndex 1#u32) pair_emits .nil⟩

/-- `ifBytes` decodes to `ifOps`. -/
theorem if_encoded : BodyEncoding ifBytes ifOps := by
  have h0 : At ifBytes 0#usize (.plain (Spec.i32Const 0#i32)) 2#usize :=
    ⟨_, ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 body_zero32)⟩, rfl, rfl, by decide⟩
  have h2 : At ifBytes 2#usize (.plain (Spec.Constants.i64 0#i64)) 4#usize :=
    ⟨_, ⟨0x42#u8, [0#u8], rfl, .plain (.i64Const 0#i64 body_zero64)⟩, rfl, rfl, by decide⟩
  have h4 : At ifBytes 4#usize (.plain (Spec.i32Const 0#i32)) 6#usize :=
    ⟨_, ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 body_zero32)⟩, rfl, rfl, by decide⟩
  have h6 : At ifBytes 6#usize (.if_ (.TypeIndex 1#u32)) 8#usize :=
    ⟨_, ⟨0x04#u8, [1#u8], rfl, .if_ (index_encoding 1#u8 1#u32 (by decide) rfl)⟩, rfl, rfl, by decide⟩
  have h8 : At ifBytes 8#usize (.end_) 9#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have h9 : At ifBytes 9#usize (.end_) 10#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  exact ⟨_, 10#usize, (((((((Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h4).snoc h6).snoc h8).snoc h9), rfl, _, rfl, WebAssembly.Binary.EmitsWith.ifEnd (toSpec := Itasca.Body.blockType) (.TypeIndex 1#u32) (WebAssembly.Binary.EmitsWith.simple (toSpec := Itasca.Body.blockType) pair_emits (.plain _ (Spec.i32_const_wf 0#i32))) .nil⟩

/-- `loopBytes` decodes to `loopOps`. -/
theorem loop_encoded : BodyEncoding loopBytes loopOps := by
  have h0 : At loopBytes 0#usize (.plain (Spec.i32Const 0#i32)) 2#usize :=
    ⟨_, ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 body_zero32)⟩, rfl, rfl, by decide⟩
  have h2 : At loopBytes 2#usize (.plain (Spec.Constants.i64 0#i64)) 4#usize :=
    ⟨_, ⟨0x42#u8, [0#u8], rfl, .plain (.i64Const 0#i64 body_zero64)⟩, rfl, rfl, by decide⟩
  have h4 : At loopBytes 4#usize (.loop (.TypeIndex 2#u32)) 6#usize :=
    ⟨_, ⟨0x03#u8, [2#u8], rfl, .loop (index_encoding 2#u8 2#u32 (by decide) rfl)⟩, rfl, rfl, by decide⟩
  have h6 : At loopBytes 6#usize (.plain (.BR (.mk_uN 0))) 8#usize :=
    ⟨_, ⟨0x0C#u8, [0#u8], rfl, .plain (.br 0#u32 (unsigned 0#u8 (by decide)))⟩, rfl, rfl, by decide⟩
  have h8 : At loopBytes 8#usize (.end_) 9#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have h9 : At loopBytes 9#usize (.end_) 10#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  exact ⟨_, 10#usize, (((((((Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h4).snoc h6).snoc h8).snoc h9), rfl, _, rfl, WebAssembly.Binary.EmitsWith.loop (toSpec := Itasca.Body.blockType) (.TypeIndex 2#u32) pair_emits (WebAssembly.Binary.EmitsWith.simple (toSpec := Itasca.Body.blockType) .nil (.plain _ (.instr_case_7 _ (Translation.Environment.index_wf 0#u32))))⟩

/-- A `br_table` with targets `[0]` and default `1`. -/
def heterogeneousTable : instr := Body.BrTable.instruction [0#u32] 1#u32
/-- The body `unreachable; br_table [0] 1` of the block. -/
def tableInner : List instr := [.UNREACHABLE, heterogeneousTable]
/-- A `block` of type index 4 (`[] -> [f32, f64]`) around `tableInner`. -/
def tableBlock : instr := .BLOCK (blockType (.TypeIndex 4#u32)) tableInner
/-- `tableBlock; unreachable`. -/
def tableOps : List instr := [tableBlock, .UNREACHABLE]
/-- The body bytes `block (type 4) unreachable; br_table [0] 1; end; unreachable; end`. -/
def tableBytes : Slice U8 := bytes
  [0x02#u8, 4#u8, 0#u8, 0x0E#u8, 1#u8, 0#u8, 1#u8, 0x0B#u8, 0#u8, 0x0B#u8]

private theorem table_wf : wf_instr heterogeneousTable := Body.BrTable.instruction_wf _ _
private theorem table_inner_wf : Forall wf_instr tableInner := by
  simpa [tableInner, Forall] using And.intro wf_instr.instr_case_1 table_wf

/-- A `br_table` whose targets have types `[f32, f64]` and `[i32, i64]` is typed after
`unreachable`: two bottom operands are a subtype of both, which the generated Wasm 2.0 rule
permits. -/
theorem table_typed : FunctionTyped env locals pairResult tableOps := by
  let C := rootContext pairResult
  let D := Body.Control.labelContext [.F32, .F64] ++ C
  have hC := root_wf pairResult
  have hD : wf_context D := Body.Control.enter_context_wf C hC _
  have hlabels : D.LABELS = [.mk_list [.F32, .F64], .mk_list [.I32, .I64]] := rfl
  have hfloat : Resulttype_sub (.mk_list [.BOT, .BOT]) (.mk_list [.F32, .F64]) :=
    .mk_Resulttype_sub _ _ rfl (by simp [Forall₂, Valtype_sub.bot])
  have hint : Resulttype_sub (.mk_list [.BOT, .BOT]) (.mk_list [.I32, .I64]) :=
    .mk_Resulttype_sub _ _ rfl (by simp [Forall₂, Valtype_sub.bot])
  have ht : Instr_ok D heterogeneousTable
      (.mk_functype (.mk_list [.BOT, .BOT, .I32]) (.mk_list [.F32, .F64])) := by
    apply Instr_ok.br_table D [.mk_uN 0] (.mk_uN 1) [] [.BOT, .BOT] [.F32, .F64]
    · simp [Forall, hlabels, proj_uN_0]
    · simpa [Forall, hlabels, proj_uN_0] using hfloat
    · simp [hlabels, proj_uN_0]
    · simpa [hlabels, proj_uN_0] using hint
    · exact hD
    · exact table_wf
  have hi : Instrs_ok D tableInner (.mk_functype (.mk_list []) (.mk_list [.F32, .F64])) :=
    .seq D [.UNREACHABLE] [heterogeneousTable] [] [.F32, .F64] [.BOT, .BOT, .I32]
      (.instr D _ _ _ (.unreachable D _ _ hD .instr_case_1) hD .instr_case_1)
      (.instr D _ _ _ ht hD table_wf) hD
      (by simp [Forall, wf_instr.instr_case_1]) (by simpa [Forall] using table_wf)
  have hwf : wf_instr tableBlock := .instr_case_4 _ _ (block_type_wf _) table_inner_wf
  have hb : Instr_ok C tableBlock (.mk_functype (.mk_list []) (.mk_list [.F32, .F64])) :=
    .block C _ _ _ _ (block_type_ok env C hC rfl (.TypeIndex 4#u32) [] [.F32, .F64] rfl rfl)
      hi hC hwf (Body.Control.label_context_wf _)
  exact .seq C [tableBlock] [.UNREACHABLE] [] [.I32, .I64] [.F32, .F64]
    (.instr C _ _ _ hb hC hwf)
    (.instr C _ _ _ (.unreachable C _ _ hC .instr_case_1) hC .instr_case_1)
    hC (by simpa [Forall] using hwf) (by simp [Forall, wf_instr.instr_case_1])

/-- `tableBytes` decodes to `tableOps`. -/
theorem table_encoded : BodyEncoding tableBytes tableOps := by
  have h0 : At tableBytes 0#usize (.block (.TypeIndex 4#u32)) 2#usize :=
    ⟨_, ⟨0x02#u8, [4#u8], rfl, .block (index_encoding 4#u8 4#u32 (by decide) rfl)⟩, rfl, rfl, by decide⟩
  have h2 : At tableBytes 2#usize (.plain .UNREACHABLE) 3#usize :=
    ⟨_, ⟨0#u8, [], rfl, .plain .unreachable⟩, rfl, rfl, by decide⟩
  have h3 : At tableBytes 3#usize (.plain heterogeneousTable) 7#usize :=
    ⟨_, ⟨0x0E#u8, [1#u8, 0#u8, 1#u8], rfl,
      .plain (.brTable (r := Body.Scalar.operands) [0#u32] 1#u32 (unsigned 1#u8 (by decide))
        (.cons (unsigned 0#u8 (by decide)) .nil) (unsigned 1#u8 (by decide)))⟩, rfl, rfl, by decide⟩
  have h7 : At tableBytes 7#usize .end_ 8#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have h8 : At tableBytes 8#usize (.plain .UNREACHABLE) 9#usize :=
    ⟨_, ⟨0#u8, [], rfl, .plain .unreachable⟩, rfl, rfl, by decide⟩
  have h9 : At tableBytes 9#usize .end_ 10#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have hi := WebAssembly.Binary.EmitsWith.simple (toSpec := Itasca.Body.blockType) (WebAssembly.Binary.EmitsWith.simple (toSpec := Itasca.Body.blockType) .nil (.plain _ .instr_case_1)) (.plain _ table_wf)
  have ho := WebAssembly.Binary.EmitsWith.simple (toSpec := Itasca.Body.blockType) (WebAssembly.Binary.EmitsWith.block (toSpec := Itasca.Body.blockType) (.TypeIndex 4#u32) .nil hi) (.plain _ .instr_case_1)
  exact ⟨_, 10#usize, ((((((Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h3).snoc h7).snoc h8).snoc h9,
    rfl, _, rfl, ho⟩

/-- `code.bodyCore` accepts `blockBytes` as a function of type 0. The theorem
combines the decoding and typing derivations, without evaluating any handler. -/
theorem block_accepted : code.bodyCore blockBytes env locals (alloc.vec.Vec.new _) 0#u32 = .ok (.Ok ()) :=
  code.bodyCore.complete blockBytes env locals _ 0#u32
    environment_limits (by simp [blockBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    ⟨pairResult, blockOps, rfl, block_encoded, block_typed, (by simp [blockOps, Spec.DeclaredReferences.Instructions, Spec.DeclaredReferences.instructionsIndices, Spec.DeclaredReferences.instructionIndices, pairOps, identityBlock, Spec.i32Const, Spec.Constants.i64])⟩

/-- `code.bodyCore` accepts `ifBytes` as a function of type 0. -/
theorem if_accepted : code.bodyCore ifBytes env locals (alloc.vec.Vec.new _) 0#u32 = .ok (.Ok ()) :=
  code.bodyCore.complete ifBytes env locals _ 0#u32
    environment_limits (by simp [ifBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    ⟨pairResult, ifOps, rfl, if_encoded, if_typed, (by simp [ifOps, Spec.DeclaredReferences.Instructions, Spec.DeclaredReferences.instructionsIndices, Spec.DeclaredReferences.instructionIndices, pairOps, identityIf, Spec.i32Const, Spec.Constants.i64])⟩

/-- `code.bodyCore` accepts `loopBytes` as a function of type 3. -/
theorem loop_accepted : code.bodyCore loopBytes env locals (alloc.vec.Vec.new _) 3#u32 = .ok (.Ok ()) :=
  code.bodyCore.complete loopBytes env locals _ 3#u32
    environment_limits (by simp [loopBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    ⟨emptyResult, loopOps, rfl, loop_encoded, loop_typed, (by simp [loopOps, Spec.DeclaredReferences.Instructions, Spec.DeclaredReferences.instructionsIndices, Spec.DeclaredReferences.instructionIndices, pairOps, loopInstr, Spec.i32Const, Spec.Constants.i64])⟩

/-- `code.bodyCore` accepts `tableBytes` as a function of type 0. -/
theorem table_accepted : code.bodyCore tableBytes env locals (alloc.vec.Vec.new _) 0#u32 = .ok (.Ok ()) :=
  code.bodyCore.complete tableBytes env locals _ 0#u32
    environment_limits (by simp [tableBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    ⟨pairResult, tableOps, rfl, table_encoded, table_typed, (by simp [tableOps, Spec.DeclaredReferences.Instructions, Spec.DeclaredReferences.instructionsIndices, Spec.DeclaredReferences.instructionIndices, tableBlock, tableInner, heterogeneousTable, Body.BrTable.instruction])⟩

/-- The accepted run on `blockBytes` yields a `Validated` soundness certificate. -/
theorem block_validated : Validated blockBytes env locals 0#u32 :=
  code.bodyCore.sound blockBytes env locals _ 0#u32 block_accepted

/-- The accepted run on `ifBytes` yields a `Validated` soundness certificate. -/
theorem if_validated : Validated ifBytes env locals 0#u32 :=
  code.bodyCore.sound ifBytes env locals _ 0#u32 if_accepted

/-- The accepted run on `loopBytes` yields a `Validated` soundness certificate. -/
theorem loop_validated : Validated loopBytes env locals 3#u32 :=
  code.bodyCore.sound loopBytes env locals _ 3#u32 loop_accepted

/-- The accepted run on `tableBytes` yields a `Validated` soundness certificate. -/
theorem table_validated : Validated tableBytes env locals 0#u32 :=
  code.bodyCore.sound tableBytes env locals _ 0#u32 table_accepted

end Itasca.Examples.Body

end
