import Itasca.Spec.DeclaredReferences

/-!
# The `ref.func` declaration condition

Wasm 2.0 requires every function index used by `ref.func` inside a function body to occur
elsewhere in the module, outside the functions and the start declaration (for example in an
element segment, an export or a global initializer). The generated `Module_ok` omits this
condition. `generated_typing_missing_premise` exhibits a module accepted by `Module_ok` and
rejected by the `DeclaredReferences.Module` supplement; the remaining examples show which
declaration sites satisfy it.
-/

namespace Itasca.Examples.Wasm2DeclaredReferences

open DeclaredReferences

/-- The function type `[] -> [funcref]`. -/
def referenceType : functype := .mk_functype (.mk_list []) (.mk_list [.FUNCREF])

/-- A function whose body is `ref.func 0`, returning its own reference. -/
def selfReference : func := .FUNC (.mk_uN 0) [] [.REF_FUNC (.mk_uN 0)]

/-- A module containing only `selfReference`, so function 0 is referenced but never declared. -/
def undeclared : _root_.module :=
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

/-- The `DeclaredReferences.Module` supplement rejects `undeclared`. -/
theorem undeclared_rejected : ¬ DeclaredReferences.Module undeclared := by
  simp [DeclaredReferences.Module, undeclared, declarations, Function, selfReference,
    Instructions, instructionsIndices, instructionIndices]

/-- `undeclared` is accepted by `Module_ok` and rejected by the supplement, so the generated rules
need it. -/
theorem generated_typing_missing_premise :
    Module_ok undeclared ∧ ¬ DeclaredReferences.Module undeclared :=
  ⟨generated_module_typed, undeclared_rejected⟩

/-- `undeclared` plus a declarative element segment listing `ref.func 0`. -/
def declarative : _root_.module :=
  .MODULE [.TYPE referenceType] [] [selfReference] [] [] []
    [.ELEM .FUNCREF [[.REF_FUNC (.mk_uN 0)]] .DECLARE] [] none []

/-- A declarative element segment declares function 0. -/
theorem declarative_declares : DeclaredReferences.Module declarative := by
  simp [DeclaredReferences.Module, declarative, declarations, Function, selfReference,
    Instructions, instructionsIndices, instructionIndices, elementIndices, elementModeIndices]

/-- `undeclared` plus an export of function 0. -/
def exported : _root_.module :=
  .MODULE [.TYPE referenceType] [] [selfReference] [] [] [] [] [] none
    [.EXPORT (.mk_name []) (.FUNC (.mk_uN 0))]

/-- Exporting function 0 declares it. -/
theorem export_declares : DeclaredReferences.Module exported := by
  simp [DeclaredReferences.Module, exported, declarations, Function, selfReference,
    Instructions, instructionsIndices, instructionIndices, exportIndices]

/-- `undeclared` plus a global whose initializer is `ref.func 0`. -/
def globalReference : _root_.module :=
  .MODULE [.TYPE referenceType] [] [selfReference]
    [.GLOBAL (.mk_globaltype none .FUNCREF) [.REF_FUNC (.mk_uN 0)]] [] [] [] [] none []

/-- A global initializer using `ref.func 0` declares function 0. -/
theorem global_declares : DeclaredReferences.Module globalReference := by
  simp [DeclaredReferences.Module, globalReference, declarations, Function, selfReference,
    Instructions, instructionsIndices, instructionIndices, globalIndices]

/-- Making function 0 the start function does not declare it. The example concerns the
declaration condition only, not the start function's type. -/
theorem start_does_not_declare :
    ¬ DeclaredReferences.Module
      (.MODULE [.TYPE referenceType] [] [selfReference] [] [] [] [] []
        (some (.START (.mk_uN 0))) []) := by
  simp [DeclaredReferences.Module, declarations, Function, selfReference,
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

end Itasca.Examples.Wasm2DeclaredReferences
