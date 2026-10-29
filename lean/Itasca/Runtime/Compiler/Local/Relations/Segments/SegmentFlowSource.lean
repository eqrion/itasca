import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentTranslation
import Itasca.Runtime.Spec.SegmentPrograms
import Itasca.Module.Elab.SegmentSyntax
import Itasca.Runtime.Compiler.Local.Source.SourceFunctionTyping

/-!
Every emitted global read uses an imported i32 global.

Main declarations: `SegmentGlobalTypes`. A direct consumer is `Store.Initialization.SegmentInitializeSource`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

private theorem constant_i32_flow {function expr instruction env valueType}
    (constant : ConstantInstruction function 0#u32 expr valueType instruction)
    (valid : ModuleConstants.Valid env expr valueType)
    (typeEq : valueType = .I32)
    (rest : List runtime.bytecode.Instr) (next : SegmentFlow 1 rest) :
    SegmentFlow 0 (instruction :: rest) := by
  cases valid with
  | i32 value =>
    cases constant
    exact .constant 0 _ _ rest rfl (by decide) next
  | globalGet index ty bound typed imported immutable =>
    rw [typeEq] at constant
    cases constant
    exact .global index rest next
  | i64 => cases typeEq
  | f32 => cases typeEq
  | f64 => cases typeEq
  | v128 => cases typeEq
  | refFunc => cases typeEq
  | refNull ty => cases ty <;> cases typeEq

private theorem constant_i32_source {function expr instruction env valueType}
    (constant : ConstantInstruction function 0#u32 expr valueType instruction)
    (valid : ModuleConstants.Valid env expr valueType)
    (typeEq : valueType = .I32) :
    segmentInstructionSource function instruction =
      (ModuleConstants.expression expr).map admininstr_instr := by
  cases valid with
  | i32 value =>
    cases constant
    simp [segmentInstructionSource, Spec.Segment.i32, ModuleConstants.expression,
      ModuleConstants.instruction, Itasca.Spec.i32Const, admininstr_instr, IScalar.hcast_val_eq]
  | globalGet index ty bound typed imported immutable =>
    rw [typeEq] at constant
    cases constant
    rfl
  | i64 => cases typeEq
  | f32 => cases typeEq
  | f64 => cases typeEq
  | v128 => cases typeEq
  | refFunc => cases typeEq
  | refNull ty => cases ty <;> cases typeEq

theorem ElementProgram.flow {function index segment instructions env}
    (program : ElementProgram function index segment instructions)
    (valid : ModuleSegments.elementValid env segment)
    (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
    SegmentFlow 0 (instructions ++ rest) := by
  cases program with
  | passive mode => exact next
  | declarative mode word encoded => exact .elementDrop word rest next
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    have offsetValid : ModuleConstants.Valid env offset .I32 := by
      have active := valid.1
      rw [mode] at active
      exact active.choose_spec.2
    apply constant_i32_flow constant offsetValid rfl
    exact .constant 1 1#u32 0#u32 _ rfl (by decide)
      (.constant 2 2#u32 length _ rfl (by decide) (.table entry _ (.elementDrop word rest next)))

theorem DataProgram.flow {function index segment instructions env}
    (program : DataProgram function index segment instructions)
    (valid : ModuleData.Valid env segment)
    (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
    SegmentFlow 0 (instructions ++ rest) := by
  cases program with
  | passive mode => exact next
  | active memory offset mode word length encoded count instruction constant =>
    have offsetValid : ModuleConstants.Valid env offset .I32 := by
      unfold ModuleData.Valid at valid
      rw [mode] at valid
      exact valid.2
    apply constant_i32_flow constant offsetValid rfl
    exact .constant 1 1#u32 0#u32 _ rfl (by decide)
      (.constant 2 2#u32 length _ rfl (by decide) (.memory word _ (.dataDrop word rest next)))

private theorem flatten_flow (groups : List (List runtime.bytecode.Instr))
    (flows : ∀ group ∈ groups, ∀ rest, SegmentFlow 0 rest → SegmentFlow 0 (group ++ rest))
    (rest : List runtime.bytecode.Instr) (next : SegmentFlow 0 rest) :
    SegmentFlow 0 (groups.flatten ++ rest) := by
  induction groups with
  | nil => exact next
  | cons group groups ih =>
    have tailFlow := ih (fun item member => flows item (by simp [member]))
    simpa only [List.flatten_cons, List.append_assoc] using
      flows group (by simp) (groups.flatten ++ rest) tailFlow

theorem SegmentProgram.flow {module function} (program : SegmentProgram module function)
    (elementValid : ∀ segment ∈ module.module.env.elements.val,
      ModuleSegments.elementValid module.module.env segment)
    (dataValid : ∀ segment ∈ module.module.tail.data.val, ModuleData.Valid module.module.env segment) :
    SegmentFlow 0 function.code.val := by
  obtain ⟨elements, datas, body⟩ := program
  have elementFlows : ∀ group ∈ elements, ∀ rest, SegmentFlow 0 rest → SegmentFlow 0 (group ++ rest) := by
    intro group member rest next
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < module.module.env.elements.val.length := by
      have length := body.elementCount
      change elements.length = module.module.env.elements.val.length at length
      omega
    let segment := module.module.env.elements.val[index]
    have found : module.module.env.elements.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨actual, actualFound, actualProgram⟩ := body.elements index segment found
    have same : actual = group := by
      rw [List.getElem?_eq_getElem bound] at actualFound
      exact (Option.some.inj actualFound).symm.trans equal
    subst actual
    exact actualProgram.flow (elementValid segment (List.mem_of_getElem? found)) rest next
  have dataFlows : ∀ group ∈ datas, ∀ rest, SegmentFlow 0 rest → SegmentFlow 0 (group ++ rest) := by
    intro group member rest next
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < module.module.tail.data.val.length := by
      have length := body.dataCount
      change datas.length = module.module.tail.data.val.length at length
      omega
    let segment := module.module.tail.data.val[index]
    have found : module.module.tail.data.val[index]? = some segment := List.getElem?_eq_getElem sourceBound
    obtain ⟨actual, actualFound, actualProgram⟩ := body.datas index segment found
    have same : actual = group := by
      rw [List.getElem?_eq_getElem bound] at actualFound
      exact (Option.some.inj actualFound).symm.trans equal
    subst actual
    exact actualProgram.flow (dataValid segment (List.mem_of_getElem? found)) rest next
  rw [body.instructions]
  simpa only [List.append_assoc] using flatten_flow elements elementFlows
    (datas.flatten ++ [.Return 0#u32 0#u32]) (flatten_flow datas dataFlows _ .done)

theorem ElementProgram.source {function index segment instructions env}
    (program : ElementProgram function index segment instructions)
    (valid : ModuleSegments.elementValid env segment) :
    segmentSource function instructions =
      (Spec.Segment.elementProgram (ModuleElaboration.element (ModuleEnv.rawElement segment)) (.mk_uN index)).map admininstr_instr := by
  cases program with
  | passive mode => simp [segmentSource, Spec.Segment.elementProgram, ModuleElaboration.element, ModuleEnv.rawElement, ModuleSegments.elementMode, mode]
  | declarative mode word encoded => simp [segmentSource, segmentInstructionSource, Spec.Segment.elementProgram, ModuleElaboration.element, ModuleEnv.rawElement, ModuleSegments.elementMode, mode, encoded, admininstr_instr]
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    have offsetValid : ModuleConstants.Valid env offset .I32 := by
      have active := valid.1
      rw [mode] at active
      exact active.choose_spec.2
    simp only [segmentSource, List.flatMap_cons, List.flatMap_nil, constant_i32_source constant offsetValid rfl]
    simp [segmentInstructionSource, Spec.Segment.elementProgram, ModuleElaboration.element, ModuleEnv.rawElement,
      ModuleSegments.elementMode, mode, encoded, count, admininstr_instr, List.getElem!_eq_getElem?_getD,
      descriptor, Spec.Segment.i32, List.append_assoc]

theorem DataProgram.source {function index segment instructions env}
    (program : DataProgram function index segment instructions)
    (valid : ModuleData.Valid env segment) :
    segmentSource function instructions =
      (Spec.Segment.dataProgram (ModuleData.translate (ModuleData.raw segment)) (.mk_uN index)).map admininstr_instr := by
  cases program with
  | passive mode => simp [segmentSource, Spec.Segment.dataProgram, ModuleData.translate, ModuleData.raw, ModuleSegments.dataMode, mode]
  | active memory offset mode word length encoded count instruction constant =>
    have offsetValid : ModuleConstants.Valid env offset .I32 := by
      unfold ModuleData.Valid at valid
      rw [mode] at valid
      exact valid.2
    simp only [segmentSource, List.flatMap_cons, List.flatMap_nil, constant_i32_source constant offsetValid rfl]
    simp [segmentInstructionSource, Spec.Segment.dataProgram, ModuleData.translate, ModuleData.raw,
      ModuleSegments.dataMode, mode, encoded, count, admininstr_instr, Spec.Segment.i32, List.append_assoc]

private theorem group_sources {T : Type} [Inhabited T]
    (function : runtime.bytecode.CompiledFunction) (groups : List (List runtime.bytecode.Instr))
    (sources : List T) (translate : T → Nat → List admininstr)
    (count : groups.length = sources.length)
    (entries : ∀ (index : Nat) source, sources[index]? = some source → ∃ group,
      groups[index]? = some group ∧ segmentSource function group = translate source index) :
    segmentSource function groups.flatten =
      ((List.range sources.length).map (fun index => translate sources[index]! index)).flatten := by
  have mapped : groups.map (segmentSource function) =
      (List.range sources.length).map (fun index => translate sources[index]! index) := by
    apply List.ext_getElem
    · simp [count]
    · intro index left right
      have sourceBound : index < sources.length := by simpa using right
      have groupBound : index < groups.length := by simpa using left
      obtain ⟨group, found, translated⟩ := entries index sources[index] (List.getElem?_eq_getElem sourceBound)
      have same : group = groups[index] := by
        rw [List.getElem?_eq_getElem groupBound] at found
        exact (Option.some.inj found).symm
      simpa only [List.getElem_map, List.getElem_range, getElem!_pos sources index sourceBound, same] using translated
  rw [← mapped]
  clear mapped entries count sources
  induction groups with
  | nil => rfl
  | cons group groups ih => simpa [segmentSource, List.flatMap_append] using congrArg (segmentSource function group ++ ·) ih

private theorem mapped_programs {T U : Type} [Inhabited T] [Inhabited U]
    (sources : List T) (translate : T → U) (program : U → idx → List instr) :
    (((List.range sources.length).map (fun index =>
      (program (translate sources[index]!) (.mk_uN index)).map admininstr_instr)).flatten) =
    (((List.range (sources.map translate).length).map (fun index =>
      program (sources.map translate)[index]! (.mk_uN index))).flatten).map admininstr_instr := by
  rw [List.map_flatten]
  congr 1
  simp only [List.map_map, List.length_map]
  apply List.map_congr_left
  intro index member
  have bound := List.mem_range.mp member
  have mappedBound : index < (sources.map translate).length := by simpa using bound
  simp only [Function.comp_def, getElem!_pos sources index bound,
    getElem!_pos (sources.map translate) index mappedBound, List.getElem_map]

/-- The complete emitted initializer represents the source-ordered generated
segment programs; the final synthetic Return has empty source code. -/
theorem SegmentProgram.source {module function} (program : SegmentProgram module function)
    (elementValid : ∀ segment ∈ module.module.env.elements.val,
      ModuleSegments.elementValid module.module.env segment)
    (dataValid : ∀ segment ∈ module.module.tail.data.val, ModuleData.Valid module.module.env segment) :
    segmentSource function function.code.val =
      (Spec.Segment.elementPrograms (module.module.env.elements.val.map (fun entry =>
        ModuleElaboration.element (ModuleEnv.rawElement entry)))).flatten.map admininstr_instr ++
      (Spec.Segment.dataPrograms (module.module.tail.data.val.map (fun entry =>
        ModuleData.translate (ModuleData.raw entry)))).flatten.map admininstr_instr := by
  letI : Inhabited Itasca.module.Element := ⟨⟨.FuncRef, .Passive, default⟩⟩
  letI : Inhabited Itasca.module.Data := ⟨⟨.Passive, default⟩⟩
  obtain ⟨elements, datas, body⟩ := program
  have elementSources := group_sources function elements module.module.env.elements.val
    (fun entry index => (Spec.Segment.elementProgram (ModuleElaboration.element (ModuleEnv.rawElement entry))
      (.mk_uN index)).map admininstr_instr) body.elementCount (by
        intro index segment found
        obtain ⟨group, located, represented⟩ := body.elements index segment found
        exact ⟨group, located, represented.source (elementValid segment (List.mem_of_getElem? found))⟩)
  have dataSources := group_sources function datas module.module.tail.data.val
    (fun entry index => (Spec.Segment.dataProgram (ModuleData.translate (ModuleData.raw entry))
      (.mk_uN index)).map admininstr_instr) body.dataCount (by
        intro index segment found
        obtain ⟨group, located, represented⟩ := body.datas index segment found
        exact ⟨group, located, represented.source (dataValid segment (List.mem_of_getElem? found))⟩)
  have elementMapped := mapped_programs module.module.env.elements.val (fun entry => ModuleElaboration.element (ModuleEnv.rawElement entry)) Spec.Segment.elementProgram
  rw [elementMapped] at elementSources
  have dataMapped := mapped_programs module.module.tail.data.val (fun entry => ModuleData.translate (ModuleData.raw entry)) Spec.Segment.dataProgram
  rw [dataMapped] at dataSources
  rw [body.instructions]
  simp only [segmentSource, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    segmentInstructionSource, List.nil_append, List.append_nil]
  exact congrArg₂ (· ++ ·) elementSources dataSources

/-- Every emitted global read uses an imported i32 global. -/
def SegmentGlobalTypes (env : Itasca.module.Env) (instructions : List runtime.bytecode.Instr) : Prop :=
  ∀ slot index, runtime.bytecode.Instr.GlobalGet slot index ∈ instructions →
    ∃ ty, env.global_types.val[index.val]? = some ty ∧ ty.valtype = .I32 ∧
      index.val < env.num_imported_globals.val

private theorem constant_i32_global_type {function expr instruction env valueType}
    (constant : ConstantInstruction function 0#u32 expr valueType instruction)
    (valid : ModuleConstants.Valid env expr valueType) (typeEq : valueType = .I32) :
    SegmentGlobalTypes env [instruction] := by
  intro slot index member
  have equal := List.mem_singleton.mp member
  cases valid with
  | i32 value => cases constant; cases equal
  | globalGet idx ty bound typed imported immutable =>
    rw [typeEq] at constant
    cases constant
    cases equal
    exact ⟨ty, by simpa [typed] using List.getElem?_eq_getElem bound, typeEq, imported⟩
  | i64 => cases typeEq
  | f32 => cases typeEq
  | f64 => cases typeEq
  | v128 => cases typeEq
  | refFunc => cases typeEq
  | refNull ty => cases ty <;> cases typeEq

theorem ElementProgram.global_types {function index segment instructions env}
    (program : ElementProgram function index segment instructions)
    (valid : ModuleSegments.elementValid env segment) : SegmentGlobalTypes env instructions := by
  cases program with
  | passive mode => simp [SegmentGlobalTypes]
  | declarative mode word encoded => simp [SegmentGlobalTypes]
  | active table offset mode word length entry encoded count descriptor instruction constant =>
    have offsetValid : ModuleConstants.Valid env offset .I32 := by
      have active := valid.1
      rw [mode] at active
      exact active.choose_spec.2
    intro slot index member
    have justConstant : runtime.bytecode.Instr.GlobalGet slot index ∈ [instruction] := by simpa using member
    exact constant_i32_global_type constant offsetValid rfl slot index justConstant

theorem DataProgram.global_types {function index segment instructions env}
    (program : DataProgram function index segment instructions)
    (valid : ModuleData.Valid env segment) : SegmentGlobalTypes env instructions := by
  cases program with
  | passive mode => simp [SegmentGlobalTypes]
  | active memory offset mode word length encoded count instruction constant =>
    have offsetValid : ModuleConstants.Valid env offset .I32 := by
      unfold ModuleData.Valid at valid
      rw [mode] at valid
      exact valid.2
    intro slot index member
    have justConstant : runtime.bytecode.Instr.GlobalGet slot index ∈ [instruction] := by simpa using member
    exact constant_i32_global_type constant offsetValid rfl slot index justConstant

private theorem groups_property {T : Type} (groups : List (List runtime.bytecode.Instr))
    (sources : List T) (env : Itasca.module.Env) (count : groups.length = sources.length)
    (entries : ∀ (index : Nat) source, sources[index]? = some source → ∃ group,
      groups[index]? = some group ∧ SegmentGlobalTypes env group) :
    SegmentGlobalTypes env groups.flatten := by
  intro slot index member
  obtain ⟨group, present, instruction⟩ := List.mem_flatten.mp member
  obtain ⟨ordinal, bound, equal⟩ := List.mem_iff_getElem.mp present
  have sourceBound : ordinal < sources.length := by omega
  obtain ⟨actual, found, types⟩ := entries ordinal sources[ordinal] (List.getElem?_eq_getElem sourceBound)
  have same : actual = group := by
    rw [List.getElem?_eq_getElem bound] at found
    exact (Option.some.inj found).symm.trans equal
  subst actual
  exact types slot index instruction

theorem SegmentProgram.global_types {module function} (program : SegmentProgram module function)
    (elementValid : ∀ segment ∈ module.module.env.elements.val,
      ModuleSegments.elementValid module.module.env segment)
    (dataValid : ∀ segment ∈ module.module.tail.data.val, ModuleData.Valid module.module.env segment) :
    SegmentGlobalTypes module.module.env function.code.val := by
  obtain ⟨elements, datas, body⟩ := program
  have elementTypes := groups_property elements module.module.env.elements.val module.module.env
    body.elementCount (by
      intro index segment found
      obtain ⟨group, located, represented⟩ := body.elements index segment found
      exact ⟨group, located, represented.global_types (elementValid segment (List.mem_of_getElem? found))⟩)
  have dataTypes := groups_property datas module.module.tail.data.val module.module.env
    body.dataCount (by
      intro index segment found
      obtain ⟨group, located, represented⟩ := body.datas index segment found
      exact ⟨group, located, represented.global_types (dataValid segment (List.mem_of_getElem? found))⟩)
  intro slot index member
  rw [body.instructions] at member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with (member | member) | impossible
  · exact elementTypes slot index member
  · exact dataTypes slot index member
  · cases impossible

end Itasca.Runtime.Compiler
