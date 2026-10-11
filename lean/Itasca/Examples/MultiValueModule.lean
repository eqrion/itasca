import Itasca.Examples.ModuleExamples
import Itasca.Module.ModuleCompleteness
import Itasca.Body.ScalarConst
import Itasca.Binary.ModuleBinaryUnique

open Aeneas Aeneas.Std

namespace Itasca.MultiValueModule

open ModuleBinary ModuleElaboration

private theorem leb (b : U8) (h : b.val < 128 := by decide) : Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

private theorem one {α : Type} {R : α → List U8 → Prop} {x bs}
    (h : R x bs) : VecEncoding R [x] (1#u8 :: bs) :=
  ⟨[1#u8], bs, leb 1#u8, by simpa using Rep.cons h Rep.nil, rfl⟩

private theorem padded {α : Type} {R : α → List U8 → Prop} (id size : U8)
    (absent : α) {x bs} (h : R x bs) (hlen : bs.length = size.val)
    (hsize : size.val < 128 := by decide) :
    PaddedEncoding id R absent x (id :: size :: bs) :=
  ⟨[], _, .nil, .present ⟨[size], bs, hlen ▸ leb size hsize, h, rfl⟩, rfl⟩

private theorem omitted {α : Type} (id : U8) (R : α → List U8 → Prop) (absent : α) :
    PaddedEncoding id R absent absent [] := ⟨[], [], .nil, .absent, rfl⟩

def functionType : types.FuncType :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.I32, .I64] (by scalar_tac)⟩

def entry : Code := ⟨[], [Core.i32Const 0#i32, ScalarConst.i64 0#i64]⟩

def env : module.Env :=
  { ModuleExamples.emptyEnv with
    types := alloc.vec.Vec.from [functionType] (by scalar_tac)
    func_type_indices := alloc.vec.Vec.from [0#u32] (by scalar_tac)
    func_types := alloc.vec.Vec.from [functionType] (by scalar_tac) }

def raw : ModuleBinary.Module := fromEnv env [] [] [entry] []

def input : Slice U8 := ModuleExamples.bytes
  (magicVersion ++ [1#u8, 6#u8, 1#u8, 0x60#u8, 0#u8, 2#u8, 0x7F#u8, 0x7E#u8,
    3#u8, 2#u8, 1#u8, 0#u8,
    10#u8, 8#u8, 1#u8, 6#u8, 0#u8, 0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x0B#u8])
  (by simp [magicVersion]; scalar_tac)

private theorem cache : ModuleEnv.Cache env [] [] := by
  constructor
  · exact .cons ⟨by simp [env], rfl⟩ .nil
  all_goals simp [env, ModuleExamples.emptyEnv, ModuleEnv.importedFuncs,
    ModuleEnv.importedGlobals, ModuleEnv.importedTables, ModuleEnv.importedMems]

private theorem environment_valid : ModuleEnv.Valid env .Wasm2 := by
  constructor <;> simp [env, ModuleExamples.emptyEnv, Itasca.Profile.FuncTypeAdmissible,
    functionType, limits.MAX_MULTI_VALUE_PARAMS, limits.MAX_MULTI_VALUE_RESULTS,
    ModuleReferences.Coherent, ModuleReferences.collected]

private theorem entry_typed : CodeEntry.Typed env 0#u32 entry .Wasm2 := by
  refine ⟨by simp [env], ?_, trivial, by simp [entry], ?_⟩
  · let C := CodeEntry.bodyContext env [] [] [.I32, .I64]
    have hC : wf_context C := by
      constructor <;> simp [env, ModuleExamples.emptyEnv, Forall]
    have hp := ((Sequence.TypedPrefix.empty C hC).i32Const hC 0#i32).i64Const hC 0#i64
    simpa [env, functionType, entry, Code.declared, CodeEntry.instructionType, C,
      Sequence.stackTypes, Translate.valueType] using hp.typed _
        (Sequence.realizes_default false [.Val .I32, .Val .I64])
  · simp [entry, DeclaredReferences.Instructions, DeclaredReferences.instructionsIndices,
      DeclaredReferences.instructionIndices, Core.i32Const, ScalarConst.i64]

private theorem codes_typed : List.Forall₂
    (fun idx code => CodeEntry.Typed env idx code .Wasm2) env.func_type_indices.val [entry] :=
  .cons entry_typed .nil

/-- Generated typing is assembled from independently supplied declarative
body typing and exact environment caches, without a successful validator call. -/
theorem typed : Module_ok (moduleOf raw) := by
  exact ModuleElaboration.typed cache environment_valid
    (by simp [env, ModuleExamples.emptyEnv]) (by simp [env, ModuleExamples.emptyEnv])
    codes_typed (by simp) (by simp [env, ModuleExamples.emptyEnv]) (List.Forall₂.nil : List.Forall₂ (ModuleExternals.ExportResolves env) [] [])

private theorem zero32 : SignedLeb.Encoding [0#u8] (0#i32).val := by
  refine ⟨[], 0#u8, rfl, by decide, by simp, by decide, ?_, by decide, by decide⟩
  norm_num [SignedLeb.finalValue, Leb128.payload]

private theorem zero64 : SignedLeb64.Encoding [0#u8] (0#i64).val := by
  refine ⟨[], 0#u8, rfl, by decide, by simp, by decide, ?_, by decide, by decide⟩
  norm_num [SignedLeb64.finalValue, Leb128.payload]

private theorem base_body_encoding : Itasca.Profile.BodyBytes .Wasm1 entry.body
    [0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x0B#u8] := by
  refine ⟨[.plain (Core.i32Const 0#i32), .plain (ScalarConst.i64 0#i64), .end_], ?_, ?_⟩
  · exact Rep.cons
      (show Wasm.TokenEncoding (.plain (Core.i32Const 0#i32)) [0x41#u8,0#u8] from
        ⟨0x41#u8, [0#u8], rfl, .i32Const 0#i32 zero32⟩)
      (Rep.cons
        (show Wasm.TokenEncoding (.plain (ScalarConst.i64 0#i64)) [0x42#u8,0#u8] from
          ⟨0x42#u8, [0#u8], rfl, .i64Const 0#i64 zero64⟩)
        (Rep.cons (show Wasm.TokenEncoding .end_ [0x0B#u8] from
          ⟨0x0B#u8, [], rfl, .end_⟩) .nil))
  · exact ⟨_, rfl, .simple (.simple .nil (.plain _ (Core.i32Const_wf _)))
      (.plain _ (ScalarConst.i64_wf _))⟩

private theorem body_encoding : Itasca.Profile.BodyBytes .Wasm2 entry.body
    [0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x0B#u8] := by
  refine ⟨[.plain (Core.i32Const 0#i32), .plain (ScalarConst.i64 0#i64), .end_], ?_, ?_⟩
  · exact Rep.cons
      (show MultiValue.TokenEncoding (.plain (Core.i32Const 0#i32)) [0x41#u8,0#u8] from
        ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 zero32)⟩)
      (Rep.cons
        (show MultiValue.TokenEncoding (.plain (ScalarConst.i64 0#i64)) [0x42#u8,0#u8] from
          ⟨0x42#u8, [0#u8], rfl, .plain (.i64Const 0#i64 zero64)⟩)
        (Rep.cons (show MultiValue.TokenEncoding .end_ [0x0B#u8] from
          ⟨0x0B#u8, [], rfl, .end_⟩) .nil))
  · exact ⟨_, rfl, .simple (.simple .nil (.plain _ (Core.i32Const_wf _)))
      (.plain _ (ScalarConst.i64_wf _))⟩

/-- The binary premise records the complete module and its actual encoded
body size; no parser execution or canonical re-encoding is assumed. -/
theorem encoded (profile : ValidationProfile) : ModuleEncodingWithinLimits raw input.val profile := by
  constructor
  · simp [input, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion, limits.MAX_MODULE_BYTES]
  · refine ⟨[1#u8,6#u8,1#u8,0x60#u8,0#u8,2#u8,0x7F#u8,0x7E#u8], [],
      [3#u8,2#u8,1#u8,0#u8], [], [], [], [], [], [], [],
      [10#u8,8#u8,1#u8,6#u8,0#u8,0x41#u8,0#u8,0x42#u8,0#u8,0x0B#u8], [], [],
      ?_, omitted _ _ _, ?_, omitted _ _ _, omitted _ _ _, omitted _ _ _,
      omitted _ _ _, omitted _ _ _, omitted _ _ _, ?_, ?_, omitted _ _ _, .nil, rfl, ?_, ?_⟩
    · apply padded _ 6#u8 _ (one (x := functionType) ?_) rfl
      refine ⟨[0#u8], [2#u8,0x7F#u8,0x7E#u8], ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩, ?_, rfl⟩
      exact ⟨[2#u8], [0x7F#u8,0x7E#u8], leb 2#u8,
        Rep.cons (show ValueTypeEncoding .I32 [0x7F#u8] from rfl)
          (Rep.cons (show ValueTypeEncoding .I64 [0x7E#u8] from rfl) .nil), rfl⟩
    · exact padded _ 2#u8 _ (one (leb 0#u8)) rfl
    · cases profile with
      | Wasm1 => exact ⟨rfl, rfl⟩
      | Wasm2 => exact omitted _ _ _
    · apply padded _ 8#u8 _ (one (x := entry) ?_) rfl
      exact ⟨by simp [entry, Code.declared, limits.MAX_LOCALS], [6#u8], [0#u8],
        [0x41#u8,0#u8,0x42#u8,0#u8,0x0B#u8], leb 6#u8,
        ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩,
        by cases profile; exact base_body_encoding; exact body_encoding,
        by simp [limits.MAX_FUNCTION_BYTES], rfl⟩
    · cases profile <;> simp [ModuleTypesAllowed, ValueTypeAllowed, raw, fromEnv, env,
        ModuleExamples.emptyEnv, functionType, entry]
    · simp [DataCountValid, raw, fromEnv, env, ModuleExamples.emptyEnv, entry,
        instructionsUseData, instructionUsesData, Core.i32Const, ScalarConst.i64]

/-- A real two-result function is accepted by the public module API as a
consequence of the shared completeness theorem. -/
theorem accepted : ∃ decoded, module.validate_module input .Wasm2 = .ok (.Ok decoded) ∧
    Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw := by
  exact module.validate_module.profile_complete_with_metadata input raw .Wasm2 (encoded .Wasm2)
    (by simp [ModuleSignaturesWithinLimits, raw, fromEnv, env, functionType,
      Itasca.Profile.FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS, limits.MAX_MULTI_VALUE_RESULTS])
    (ModuleElaboration.elaborates cache codes_typed) typed
    (ModuleElaboration.profile cache environment_valid codes_typed)

/-- The same accepted bytes also instantiate the shared module soundness theorem. -/
theorem validated : ∃ decoded, module.validate_module input .Wasm2 = .ok (.Ok decoded) ∧
    ModuleSound.Validated input decoded .Wasm2 := by
  obtain ⟨decoded, ha, _, _⟩ := accepted
  exact ⟨decoded, ha, module.validate_module.profile_sound input decoded .Wasm2 ha⟩


/-- The identical binary is rejected by Wasm 1.0 because its independently
encoded function signature has two results. -/
theorem wasm1_rejected : ∃ err, module.validate_module input .Wasm1 = .ok (.Err err) := by
  obtain ⟨result, hr⟩ := module.validate_module.wasm_total input
  cases result with
  | Err err => exact ⟨err, hr⟩
  | Ok decoded =>
    obtain ⟨other, hb, _, _, _, hp, _⟩ := module.validate_module.wasm_sound input decoded hr
    have he : raw = other := ModuleEncoding.unique (encoded .Wasm1).encoding hb
    subst other
    have h := hp.arity functionType (by simp [raw, fromEnv, env])
    norm_num [Itasca.Profile.FuncType, functionType] at h

end Itasca.MultiValueModule
