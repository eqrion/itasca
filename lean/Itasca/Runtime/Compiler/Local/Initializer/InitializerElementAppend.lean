import Itasca.Runtime.Compiler.Local.Initializer.ElementContracts
import Itasca.Runtime.Compiler.Local.Initializer.ModuleLoopContracts
import Itasca.Runtime.Compiler.Local.Initializer.ElementLoopContracts
import Itasca.Runtime.Compiler.Local.Initializer.ElementValueContracts
import Itasca.Runtime.Compiler.Local.Initializer.DataOffsetContracts
import Itasca.Runtime.Compiler.Local.Initializer.GlobalContracts
import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts
import Itasca.Runtime.Compiler.Local.Initializer.ConstantContracts
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Module.Const.Parser

/-!
Sections, each formerly its own module: InitializerProofs, InitializerExpression, InitializerMappings, InitializerMappingLoops, InitializerElementAppend.
-/

/-! ## InitializerProofs -/

section

/-! The extracted synthetic-initializer emitter and constant compiler terminate
under allocator laws and representable vector lengths. Successful calls append
exactly the certified scalar/reference/vector instruction, with vector constants
embedded in the actual pool. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem initializer_emit {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (code : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (fits : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.1 = .Ok () → out.2.2.val = code.val ++ [instruction] ⦄ := by
  obtain ⟨⟨status, afterBudget, after⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.emit.total ops law budget code instruction fits)
  rw [called]
  simp only [WP.spec_ok]
  intro accepted
  subst status
  exact (runtime.compiler.initialize.emit.inv ops budget afterBudget code after instruction (.Ok ()) called).success law

@[step] theorem initializer_constant {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.1 = .Ok () → ConstantLowered function out.2.2 expr ty dst ⦄ := by
  obtain ⟨⟨status, afterBudget, after⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.constant.total ops law budget function expr ty dst codeFits poolFits)
  rw [called]
  simp only [WP.spec_ok]
  intro accepted
  subst status
  exact (runtime.compiler.initialize.constant.inv ops budget afterBudget function after expr ty dst (.Ok ()) called).success law

end Itasca.Runtime.Compiler

end

/-! ## InitializerExpression -/

section

/-! Successful synthetic initializer compilation retains its exact two-instruction
program, literal pool, slot width, and position in the executable module. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std


/-- Actual successful expression lowering supplies the executable initializer certificate.
Source expression typing and runtime index resolution are separate obligations. -/
theorem initializer_expression {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (index : Usize) (after : runtime.compiler.ExecutableModule) (budgetAfter : runtime.compiler.Budget A)
    (success : runtime.compiler.initialize.expression ops module budget expr ty =
      .ok (.Ok index, after, budgetAfter)) :
    ∃ function, InitializerCode function expr ty ∧ index.val = module.functions.val.length ∧
      after = { module with functions := after.functions } ∧
      after.functions.val = module.functions.val ++ [function] := by
  exact (runtime.compiler.initialize.expression.inv ops module after budget budgetAfter expr ty (.Ok index) success).success law

end Itasca.Runtime.Compiler

end

/-! ## InitializerMappings -/

section

/-! Exact retained initializer indices from the actual compiler helpers. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A successful global initializer append records the exact source expression,
new function index, and two-instruction certificate, preserving other fields. -/
theorem initializer_lower_global {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (global : Itasca.metadata.Global)
    (found : module.module.env.globals.val[index.val]? = some global)
    (success : runtime.compiler.initialize.lower_global ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ function fnIndex,
      InitializerCode function global.init global.gtype.valtype ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions, global_initializers := after.global_initializers } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      after.global_initializers.val = module.global_initializers.val ++ [fnIndex] := by
  exact (runtime.compiler.initialize.lower_global.inv_selected ops module after budget budgetAfter
    index global found (.Ok ()) success).success law

def InitializerAt (functions : List runtime.bytecode.CompiledFunction)
    (index : Usize) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) : Prop :=
  ∃ code, functions[index.val]? = some code ∧ InitializerCode code expr ty

theorem InitializerAt.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {index expr ty}
    (cert : InitializerAt before index expr ty) : InitializerAt after index expr ty := by
  obtain ⟨code, found, compiled⟩ := cert
  have bound := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨code, ?_, compiled⟩
  rw [← prefixEq, List.getElem?_take] at found
  simpa [bound] using found

/-- Each successful element-value lowering appends the actual source value's
initializer and records precisely its issued function index. -/
theorem initializer_lower_element_value {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.metadata.Element) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (success : runtime.compiler.initialize.lower_element_value ops module budget indices i j =
      .ok (.Ok (), after, budgetAfter, outIndices)) :
    ∃ function fnIndex,
      InitializerCode function expr (Itasca.ModuleConstants.referenceValueType segment.elem) ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      outIndices.val = indices.val ++ [fnIndex] := by
  exact (runtime.compiler.initialize.lower_element_value.inv_selected ops module after budget budgetAfter
    indices outIndices i j segment expr found valueFound (.Ok ()) success).success law

theorem initializer_lower_data_active {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Data)
    (memory : U32) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (active : segment.mode = .Active memory expr)
    (success : runtime.compiler.initialize.lower_data_offset ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ function fnIndex,
      InitializerCode function expr .I32 ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions, data_offsets := after.data_offsets } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      after.data_offsets.val = module.data_offsets.val ++ [some fnIndex] := by
  have effect := runtime.compiler.initialize.lower_data_offset.inv_selected ops module after budget budgetAfter
    index segment found (.Ok ()) success
  rw [active] at effect
  exact effect.active_success law

/-- Passive data segments retain an explicit absent offset without adding code. -/
theorem initializer_lower_data_passive {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (passive : segment.mode = .Passive)
    (success : runtime.compiler.initialize.lower_data_offset ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    after = { module with data_offsets := after.data_offsets } ∧
      after.data_offsets.val = module.data_offsets.val ++ [none] := by
  have effect := runtime.compiler.initialize.lower_data_offset.inv_selected ops module after budget budgetAfter
    index segment found (.Ok ()) success
  rw [passive] at effect
  exact effect.passive_success law

end Itasca.Runtime.Compiler

end

/-! ## InitializerMappingLoops -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Indexed source expressions and their retained synthetic functions. -/
def InitializerEntries (functions : List runtime.bytecode.CompiledFunction)
    (expressions : List Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (indices : List Usize) : Prop :=
  List.Forall₂ (fun expr index => InitializerAt functions index expr ty) expressions indices

theorem InitializerEntries.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {expressions ty indices}
    (entries : InitializerEntries before expressions ty indices) :
    InitializerEntries after expressions ty indices := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def GlobalInitializerEntries (functions : List runtime.bytecode.CompiledFunction)
    (globals : List Itasca.metadata.Global) (indices : List Usize) : Prop :=
  List.Forall₂ (fun global index => InitializerAt functions index global.init global.gtype.valtype)
    globals indices

theorem GlobalInitializerEntries.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {globals indices}
    (entries : GlobalInitializerEntries before globals indices) :
    GlobalInitializerEntries after globals indices := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def GlobalMappingPrefix (before current : runtime.compiler.ExecutableModule) (count : Nat) : Prop :=
  current = { before with functions := current.functions, global_initializers := current.global_initializers } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  GlobalInitializerEntries current.functions.val (before.module.env.globals.val.take count)
    current.global_initializers.val

theorem global_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : GlobalMappingPrefix before current index.val)
    (bound : index.val < before.module.env.globals.val.length)
    (success : runtime.compiler.initialize.lower_global ops current budget index =
      .ok (.Ok (), after, budgetAfter)) : GlobalMappingPrefix before after (index.val + 1) := by
  obtain ⟨unchanged, prefixEq, entries⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let global := before.module.env.globals.val[index.val]
  have found : current.module.env.globals.val[index.val]? = some global := by
    rw [source]
    exact List.getElem?_eq_getElem bound
  obtain ⟨function, fnIndex, cert, position, changed, functions, indices⟩ :=
    initializer_lower_global ops law current after budget budgetAfter index global found success
  have extended := entries.extend (after := after.functions.val) (by simp [functions])
  refine ⟨?_, ?_, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · rw [functions, List.take_append_of_le_length]
    · exact prefixEq
    · have hlen := congrArg List.length prefixEq
      simp only [List.length_take] at hlen
      change before.functions.val.length ≤ current.functions.val.length
      omega
  · unfold GlobalInitializerEntries at extended ⊢
    rw [List.take_add_one, indices]
    have single : List.Forall₂
        (fun global index => InitializerAt after.functions.val index global.init global.gtype.valtype)
        [global] [fnIndex] := by
      refine .cons ?_ .nil
      refine ⟨function, ?_, cert⟩
      rw [functions, position]
      simp
    simpa [List.getElem?_eq_getElem bound, global] using List.rel_append extended single

/-- Successful completion of the actual global initializer loop retains a
certificate for each source global, with exact module-field preservation. -/
theorem initializer_global_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : GlobalMappingPrefix before current index.val)
    (bound : index.val ≤ before.module.env.globals.val.length)
    (success : runtime.compiler.initialize.lower_loop0 ops current budget index (.Ok ()) =
      .ok (after, budgetAfter, .Ok ())) :
    GlobalMappingPrefix before after before.module.env.globals.val.length := by
  have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) prefixInv.1
  let P := fun next (_ : runtime.compiler.Budget A) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → cursor.val ≤ before.module.env.globals.val.length ∧ GlobalMappingPrefix before next cursor.val
  let Q := fun next (_ : runtime.compiler.Budget A) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → GlobalMappingPrefix before next before.module.env.globals.val.length
  have preserved := InitializerModuleLoop.inv
    { rules := initializerGlobalLoop ops, before := current, budget := budget, j := index, status := .Ok (),
      length := alloc.vec.Vec.len before.module.env.globals,
      lengthEq := by simpa only [initializerGlobalLoop, source], P := P, Q := Q,
      advance := (by
      intro next charged cursor same inside prior result later laterBudget nextIndex called increment accepted
      subst result
      obtain ⟨position, mapped⟩ := prior rfl
      change cursor.val < before.module.env.globals.val.length at inside
      have appended := global_mapping_append ops law before next later charged laterBudget cursor mapped inside called
      exact ⟨by omega, by simpa only [increment] using appended⟩),
      finish := (by
      intro next charged cursor result same prior stopped accepted
      obtain ⟨position, mapped⟩ := prior accepted
      have last := stopped.resolve_right (by intro rejected; exact rejected accepted)
      have equal : cursor.val = before.module.env.globals.val.length := by
        change before.module.env.globals.val.length ≤ cursor.val at last
        omega
      simpa only [equal] using mapped), initial := fun _ => ⟨bound, prefixInv⟩ }
    after budgetAfter (.Ok ()) success
  exact preserved rfl

end Itasca.Runtime.Compiler

end

/-! ## InitializerElementAppend -/

section

/-!
Element initializer mappings and append composition. ElementMappingPrefix and OffsetInitializer transport emitted element values and their source offset.
-/

/-! ## Initializer Element Mappings -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def ElementMappingPrefix (before current : runtime.compiler.ExecutableModule)
    (segment : Itasca.metadata.Element) (count : Nat) (indices : alloc.vec.Vec Usize) : Prop :=
  current = { before with functions := current.functions } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  InitializerEntries current.functions.val (segment.init.val.take count)
    (Itasca.ModuleConstants.referenceValueType segment.elem) indices.val

theorem element_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment)
    (prefixInv : ElementMappingPrefix before current segment j.val indices)
    (bound : j.val < segment.init.val.length)
    (success : runtime.compiler.initialize.lower_element_value ops current budget indices i j =
      .ok (.Ok (), after, budgetAfter, outIndices)) :
    ElementMappingPrefix before after segment (j.val + 1) outIndices := by
  obtain ⟨unchanged, prefixEq, entries⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let expr := segment.init.val[j.val]
  have exprFound : segment.init.val[j.val]? = some expr := List.getElem?_eq_getElem bound
  obtain ⟨function, fnIndex, cert, position, changed, functions, indices⟩ :=
    initializer_lower_element_value ops law current after budget budgetAfter indices outIndices i j
      segment expr (by simpa [source] using found) exprFound success
  have extended := entries.extend (after := after.functions.val) (by simp [functions])
  refine ⟨?_, ?_, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · rw [functions, List.take_append_of_le_length]
    · exact prefixEq
    · have hlen := congrArg List.length prefixEq
      simp only [List.length_take] at hlen
      change before.functions.val.length ≤ current.functions.val.length
      omega
  · unfold InitializerEntries at extended ⊢
    rw [List.take_add_one, indices]
    have single : List.Forall₂
        (fun expr index => InitializerAt after.functions.val index expr
          (Itasca.ModuleConstants.referenceValueType segment.elem)) [expr] [fnIndex] := by
      refine .cons ?_ .nil
      refine ⟨function, ?_, cert⟩
      rw [functions, position]
      simp
    simpa [List.getElem?_eq_getElem bound, expr] using List.rel_append extended single

/-- Successful evaluation of the actual inner compiler loop establishes the
complete vector of element-value initializer certificates. -/
theorem initializer_element_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment)
    (prefixInv : ElementMappingPrefix before current segment j.val indices)
    (bound : j.val ≤ segment.init.val.length)
    (success : runtime.compiler.initialize.lower_element_loop ops current budget i indices j (.Ok ()) =
      .ok (after, budgetAfter, outIndices, .Ok ())) :
    ElementMappingPrefix before after segment segment.init.val.length outIndices := by
  have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) prefixInv.1
  have currentFound : current.module.env.elements.val[i.val]? = some segment := by simpa only [source] using found
  let P := fun next (_ : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → ElementMappingPrefix before next segment cursor.val scratch
  let Q := fun next (_ : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → ElementMappingPrefix before next segment segment.init.val.length scratch
  have completed : Q after budgetAfter outIndices (.Ok ()) := by
    apply runtime.compiler.initialize.lower_element_loop.inv
      { ops := ops, before := current, budget := budget, indices := indices, i := i, j := j,
        status := .Ok (), segment := segment, found := currentFound, bounded := bound,
        P := P, Q := Q, advance := ?_, finish := ?_, initial := fun _ => prefixInv }
      after budgetAfter outIndices (.Ok ()) success
    · intro next charged scratch cursor source inside prior result last lastBudget lastIndices nextIndex lowered increment
      intro accepted
      subst result
      have appended := element_mapping_append ops law before next last charged lastBudget scratch lastIndices
        i cursor segment found (prior rfl) inside lowered
      simpa only [increment] using appended
    · intro next charged scratch cursor result source position prior stopped accepted
      have last := stopped.resolve_right (by intro rejected; exact rejected accepted)
      simpa only [last] using prior accepted
  exact completed rfl

end Itasca.Runtime.Compiler

end

/-! ## Initializer Element Append -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def OffsetInitializer (functions : List runtime.bytecode.CompiledFunction)
    (expr : Option Itasca.wasm_types.ConstExpr) (index : Option Usize) : Prop :=
  match expr, index with
  | none, none => True
  | some expr, some index => InitializerAt functions index expr .I32
  | _, _ => False

theorem OffsetInitializer.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {expr index}
    (cert : OffsetInitializer before expr index) : OffsetInitializer after expr index := by
  cases expr <;> cases index <;> simp only [OffsetInitializer] at cert ⊢
  exact cert.extend prefixEq

theorem initializer_lower_element {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Element)
    (found : module.module.env.elements.val[index.val]? = some segment)
    (success : runtime.compiler.initialize.lower_element ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ indices offset,
      after = { module with functions := after.functions, element_initializers := after.element_initializers, element_offsets := after.element_offsets } ∧
      after.functions.val.take module.functions.length = module.functions.val ∧
      after.element_initializers.val = module.element_initializers.val ++ [indices] ∧
      after.element_offsets.val = module.element_offsets.val ++ [offset] ∧
      InitializerEntries after.functions.val segment.init.val
        (Itasca.ModuleConstants.referenceValueType segment.elem) indices.val ∧
      OffsetInitializer after.functions.val (sourceElementOffset segment) offset := by
  have collected (stages : InitializerElementPrefix ops module budget index) :
      ElementMappingPrefix module stages.middle segment segment.init.val.length stages.indices := by
    apply initializer_element_loop ops law module module stages.middle budget stages.collected
      (alloc.vec.Vec.new Usize) stages.indices index 0#usize segment found ?_ (by change 0 ≤ segment.init.val.length; omega) stages.loopCalled
    exact ⟨rfl, by simp only [alloc.vec.Vec.length, List.take_length], .nil⟩
  have effect := runtime.compiler.initialize.lower_element.inv ops module after budget budgetAfter index (.Ok ()) success
  cases effect with
  | absent stages _status _charged offsets read pushed =>
    obtain ⟨changed, prefixEq, entries⟩ := collected stages
    simp only [List.take_length] at entries
    obtain ⟨_, rowsEq⟩ := budget_push_success ops law stages.collected stages.charged
      stages.middle.element_initializers stages.rows stages.indices stages.rowCalled
    obtain ⟨_, offsetsEq⟩ := budget_push_success ops law stages.charged budgetAfter
      stages.middle.element_offsets offsets none pushed
    have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) changed
    have oldRows := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_initializers) changed
    have oldOffsets := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_offsets) changed
    dsimp only at source oldRows oldOffsets
    rw [source, element_offset_found _ _ segment found] at read
    have offsetEq := Result.ok_injective read
    refine ⟨stages.indices, none, ?_, prefixEq, ?_, ?_, entries, ?_⟩
    · dsimp only [InitializerElementPrefix.result]
      rw [changed]
    · simpa only [InitializerElementPrefix.result, oldRows] using rowsEq
    · simpa only [oldOffsets] using offsetsEq
    · simp only [OffsetInitializer, offsetEq]
  | present stages expr final expressionBudget fnIndex _status _charged offsets read expression pushed =>
    obtain ⟨changed, prefixEq, entries⟩ := collected stages
    simp only [List.take_length] at entries
    obtain ⟨_, rowsEq⟩ := budget_push_success ops law stages.collected stages.charged
      stages.middle.element_initializers stages.rows stages.indices stages.rowCalled
    have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) changed
    have oldRows := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_initializers) changed
    have oldOffsets := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_offsets) changed
    dsimp only at source oldRows oldOffsets
    rw [source, element_offset_found _ _ segment found] at read
    have offsetEq := Result.ok_injective read
    obtain ⟨function, certificate, position, finalEq, functions⟩ :=
      initializer_expression ops law stages.result stages.charged expr .I32 fnIndex final expressionBudget expression
    obtain ⟨_, offsetsEq⟩ := budget_push_success ops law expressionBudget budgetAfter final.element_offsets offsets (some fnIndex) pushed
    have finalRows := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_initializers) finalEq
    have finalOffsets := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_offsets) finalEq
    dsimp only [InitializerElementPrefix.result] at finalRows finalOffsets functions position
    have extended := entries.extend (after := final.functions.val) (by simp only [functions, List.take_left])
    refine ⟨stages.indices, some fnIndex, ?_, ?_, ?_, ?_, extended, ?_⟩
    · rw [finalEq]
      dsimp only [InitializerElementPrefix.result]
      conv_lhs => rw [changed]
    · rw [functions, List.take_append_of_le_length]
      · exact prefixEq
      · have size := congrArg List.length prefixEq
        simp only [List.length_take] at size
        change module.functions.val.length ≤ stages.middle.functions.val.length
        omega
    · simpa only [finalRows, oldRows] using rowsEq
    · simpa only [finalOffsets, oldOffsets] using offsetsEq
    · simp only [OffsetInitializer, offsetEq]
      refine ⟨function, ?_, certificate⟩
      rw [functions, position]
      simp only [alloc.vec.Vec.len, Usize.ofNatCore_val_eq, List.getElem?_concat_length]


end Itasca.Runtime.Compiler

end

end
