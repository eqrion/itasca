import Exec.Spec.Typing.FramePayloadTyping
import Exec.Spec.Typing.SourceAdministrativeTyping
import Exec.Spec.Typing.HostTypingPreservation
import Exec.Spec.Typing.AbruptValuesTyping

/-! Source defaults, local-frame construction, and defined-function entry
preserve semantic typing using the actual typed function instance. -/

namespace Exec.Spec
open SpecExt

theorem source_default_typed {s : store} (storeWf : wf_store s) {type : valtype} {value : val}
    (default : fun_default_ type (some value)) : Val_ok s value type := by
  cases default
  all_goals first
    | (apply Val_ok.numtype; exact storeWf; assumption)
    | (apply Val_ok.vectype; exact storeWf; assumption)
    | exact .reftype _ (.REF_NULL _) _ (.null _ _ storeWf) storeWf

theorem source_defaults_typed {s : store} (storeWf : wf_store s) (types : List valtype)
    (defaults : List (Option val)) (count : defaults.length=types.length)
    (paired : Forall₂ (fun option type => fun_default_ type option) defaults types)
    (present : Forall (fun option => option ≠ none) defaults) :
    ResultsTyped s types (defaults.map Option.get!) := by
  have relation : List.Forall₂ (fun option type => fun_default_ type option) defaults types :=
    forall₂_of_lengths count paired
  clear paired count
  revert present
  induction relation with
  | nil => intro _; exact .nil
  | @cons option type defaults types head tail ih =>
    intro present
    cases option with
    | none => exact False.elim (present none (by simp) rfl)
    | some value =>
      exact .cons (source_default_typed storeWf head)
        (ih (fun option member => present option (by simp [member])))

def functionBodyContext (context : _root_.context) (params locals results : List valtype) : _root_.context :=
  {(default : _root_.context) with LOCALS := params++locals, LABELS := [.mk_list results], RETURN := some (.mk_list results)} ++ context

theorem function_body_view {context : _root_.context} {index : idx} {locals : List «local»}
    {body : List instr} {params results : List valtype}
    (typed : Func_ok context (.FUNC index locals body) (.mk_functype (.mk_list params) (.mk_list results))) :
    ∃ localTypes, locals=localTypes.map «local».LOCAL ∧
      Expr_ok (functionBodyContext context params localTypes results) body (.mk_list results) := by
  cases typed
  refine ⟨_,rfl,?_⟩
  assumption

private def localType : «local» → valtype
  | .LOCAL type => type

theorem source_local_types_injective {left right : List valtype}
    (same : left.map «local».LOCAL=right.map «local».LOCAL) : left=right := by
  have selected := congrArg (List.map localType) same
  simpa [Function.comp_def,localType] using selected

theorem source_expr_administrative {s : store} (storeWf : wf_store s) {context : _root_.context}
    {body : List instr} {results : List valtype} (typed : Expr_ok context body (.mk_list results)) :
    Expr_ok2 s context (body.map admininstr_instr) (.mk_list results) := by
  cases typed
  apply Expr_ok2.mk_Expr_ok2
  · apply source_instrs_administrative storeWf
    assumption
  · exact storeWf
  · assumption
  · apply wf_instrs
    assumption

def functionLocalsContext (types : List valtype) : _root_.context :=
  {(default : _root_.context) with LOCALS := types}

theorem moduleinst_context_wf {s : store} {module : moduleinst} {context : _root_.context}
    (typed : Moduleinst_ok s module context) : wf_context context := by cases typed; assumption

theorem moduleinst_module_wf {s : store} {module : moduleinst} {context : _root_.context}
    (typed : Moduleinst_ok s module context) : wf_moduleinst module := by cases typed; assumption

theorem function_locals_context_wf (types : List valtype) : wf_context (functionLocalsContext types) :=
  .context_case_ [] [] [] [] [] [] [] types [] none (by simp [Forall]) (by simp [Forall])

theorem frame_of_typed_locals {s : store} {module : moduleinst} {context : _root_.context}
    (moduleTyped : Moduleinst_ok s module context) (storeWf : wf_store s)
    {types : List valtype} {values : List val} (localsTyped : ResultsTyped s types values) :
    Frame_ok s ⟨values,module⟩ (functionLocalsContext types++context) := by
  apply Frame_ok.mk_Frame_ok _ _ _ _ _ moduleTyped localsTyped.length_eq.symm
  · intro pair member
    exact List.forall₂_zip localsTyped.flip member
  · exact storeWf
  · exact moduleinst_context_wf moduleTyped
  · exact .frame_case_ _ _ (resultsTyped_wf localsTyped) (moduleinst_module_wf moduleTyped)
  · exact function_locals_context_wf types

theorem context_wf_fields {context : _root_.context} (typed : wf_context context) :
    Forall wf_tabletype context.TABLES ∧ Forall wf_memtype context.MEMS := by
  cases typed
  constructor <;> assumption

theorem context_wf_of_fields (context : _root_.context)
    (tables : Forall wf_tabletype context.TABLES) (memories : Forall wf_memtype context.MEMS) :
    wf_context context := by
  cases context
  constructor <;> assumption

theorem function_entry_instruction_typed {s : store} {ambient : _root_.context}
    (storeWf : wf_store s) (ambientWf : wf_context ambient)
    {module : moduleinst} {moduleContext : _root_.context} (moduleTyped : Moduleinst_ok s module moduleContext)
    {index : idx} {localTypes : List valtype} {body : List instr} {params results : List valtype}
    (functionTyped : Func_ok moduleContext (.FUNC index (localTypes.map «local».LOCAL) body)
      (.mk_functype (.mk_list params) (.mk_list results)))
    {args defaults : List val} (arguments : ResultsTyped s params args) (localsTyped : ResultsTyped s localTypes defaults)
    (arity : Nat) (count : arity=results.length) :
    Instr_ok2 s ambient (.FRAME_ arity ⟨args++defaults,module⟩ [.LABEL_ arity [] (body.map admininstr_instr)])
      (.mk_functype (.mk_list []) (.mk_list results)) := by
  obtain ⟨actualTypes,typesEq,bodySource⟩ := function_body_view functionTyped
  have sameTypes := source_local_types_injective typesEq
  cases sameTypes
  let frameContext := functionLocalsContext (params++localTypes)++moduleContext
  let returnContext : _root_.context := {(default : _root_.context) with RETURN := some (.mk_list results)} ++ frameContext
  let labelContext : _root_.context := {(default : _root_.context) with LABELS := [.mk_list results]} ++ returnContext
  have bodyExpression := source_expr_administrative storeWf bodySource
  have bodyAdmin : Instrs_ok2 s labelContext (body.map admininstr_instr)
      (.mk_functype (.mk_list []) (.mk_list results)) := by
    cases bodyExpression
    assumption
  have labelContextWf := (instrs_ok2_wf bodyAdmin).2.1
  have fields := context_wf_fields labelContextWf
  have returnContextWf : wf_context returnContext := context_wf_of_fields _ fields.1 fields.2
  have labelDeclarationWf : wf_context ({(default : _root_.context) with LABELS := [.mk_list results]} : _root_.context) :=
    .context_case_ [] [] [] [] [] [] [] [] [.mk_list results] none (by simp [Forall]) (by simp [Forall])
  have returnDeclarationWf : wf_context ({(default : _root_.context) with RETURN := some (.mk_list results)} : _root_.context) :=
    .context_case_ [] [] [] [] [] [] [] [] [] (some (.mk_list results)) (by simp [Forall]) (by simp [Forall])
  have bodyWf := (instrs_ok2_wf bodyAdmin).2.2
  have labelWf : wf_admininstr (.LABEL_ arity [] (body.map admininstr_instr)) :=
    .admininstr_case_71 _ _ _ (by simp [Forall]) bodyWf
  have labelTyped := Instr_ok2.label s returnContext arity [] (body.map admininstr_instr) results results
    (instrs_identity storeWf returnContextWf results) bodyAdmin storeWf returnContextWf labelWf labelDeclarationWf count
  have expression := Expr_ok2.mk_Expr_ok2 s returnContext [.LABEL_ arity [] (body.map admininstr_instr)] results
    (.instr _ _ _ _ _ labelTyped storeWf returnContextWf labelWf) storeWf returnContextWf
    (by simpa [Forall] using labelWf)
  have allLocals := resultsTyped_append arguments localsTyped
  have frameTyped := frame_of_typed_locals moduleTyped storeWf allLocals
  have frameWf : wf_frame ⟨args++defaults,module⟩ :=
    .frame_case_ _ _ (resultsTyped_wf allLocals) (moduleinst_module_wf moduleTyped)
  have moduleFields := context_wf_fields (moduleinst_context_wf moduleTyped)
  have frameContextWf : wf_context frameContext := context_wf_of_fields _ moduleFields.1 moduleFields.2
  exact .Instr_ok2_frame s ambient arity _ _ results frameContext frameTyped expression
    storeWf ambientWf frameContextWf
    (.admininstr_case_72 _ _ _ frameWf (by simpa [Forall] using labelWf)) returnDeclarationWf count

theorem wasm_instance_body_view {s : store} {module : moduleinst} {type : functype}
    {index : idx} {locals : List «local»} {body : List instr}
    (typed : Funcinst_ok s ⟨type,module,.FUNC index locals body⟩ type) :
    ∃ context, Moduleinst_ok s module context ∧ Func_ok context (.FUNC index locals body) type := by
  cases typed with
  | mk_Funcinst_ok _ _ _ context _ moduleTyped bodyTyped _ _ _ => exact ⟨context,moduleTyped,bodyTyped⟩

theorem function_entry_read_typing_preserved {s : store} {context : _root_.context}
    (components : SourceStoreComponents s) (address : Nat) (module : moduleinst)
    (index : idx) (localTypes : List valtype) (body : List instr) (params results : List valtype)
    (found : s.FUNCS[address]?=some ⟨.mk_functype (.mk_list params) (.mk_list results),module,
      .FUNC index (localTypes.map «local».LOCAL) body⟩)
    (args : List val) (defaults : List (Option val)) (arity : Nat)
    (defaultCount : defaults.length=localTypes.length)
    (defaultValues : Forall₂ (fun option type => fun_default_ type option) defaults localTypes)
    (present : Forall (fun option => option ≠ none) defaults)
    (argumentCount : args.length=params.length) (resultCount : arity=results.length)
    {input output : List valtype}
    (typed : Instrs_ok2 s context (vals args++[.CALL_ADDR address])
      (.mk_functype (.mk_list input) (.mk_list output))) :
    Instrs_ok2 s context [.FRAME_ arity ⟨args++defaults.map Option.get!,module⟩
      [.LABEL_ arity [] (body.map admininstr_instr)]]
      (.mk_functype (.mk_list input) (.mk_list output)) := by
  have storeWf := (instrs_ok2_wf typed).1
  have contextWf := (instrs_ok2_wf typed).2.1
  have functionTyped := components.functions _ (List.mem_of_getElem? found)
  obtain ⟨moduleContext,moduleTyped,bodyTyped⟩ := wasm_instance_body_view functionTyped
  have defaultsTyped := source_defaults_typed storeWf localTypes defaults defaultCount defaultValues present
  have signature : s.FUNCS[address]?.map funcinst.TYPE = some (.mk_functype (.mk_list params) (.mk_list results)) := by
    simp only [found,Option.map_some]
  apply value_operation_at_context typed
  intro primitiveInput primitiveOutput primitive
  obtain ⟨rfl,rfl⟩ := call_instruction_type primitive rfl signature
  refine ⟨argumentCount.symm,?_⟩
  intro arguments
  have entered := function_entry_instruction_typed storeWf contextWf moduleTyped bodyTyped arguments defaultsTyped arity resultCount
  exact .instr _ _ _ _ _ entered storeWf contextWf (instruction_typing_wf entered)

end Exec.Spec
