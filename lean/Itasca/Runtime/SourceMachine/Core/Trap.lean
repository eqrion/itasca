import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.SourceMachine.Sim.Basic
import Itasca.Runtime.SourceMachine.Sim.Typing
import Itasca.Runtime.SourceMachine.Sim.Typed
import Itasca.Runtime.SourceMachine.Memory.Semantics
import Itasca.Runtime.SourceMachine.Memory.Decode
import Itasca.Runtime.SourceMachine.Sim.Instruction
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Sim.Trap

/-!
Sections, each formerly its own module: Typing, ContentExtension, GlobalContents, GlobalTyping, Simulation, Globals, Select, MemoryStep, Step, Pure, PureMetadata, MemoryTyping, MemoryMutation, Trap.
-/

/-! ## Typing -/

section

namespace Itasca.Runtime.SourceMachine

/-- Semantic typing of store payloads used by mutable instructions. Function
bodies remain in `ATyped.functions`; no unproved generated `Store_ok` is used. -/
structure StoreContentsTyped (s : store) : Prop where
  globals : ∀ global ∈ s.GLOBALS, Globalinst_ok s global global.TYPE
  tables : ∀ table ∈ s.TABLES, Tableinst_ok s table table.TYPE
  memories : ∀ memory ∈ s.MEMS, Meminst_ok s memory memory.TYPE
  elements : ∀ element ∈ s.ELEMS, Eleminst_ok s element element.TYPE
  data : ∀ entry ∈ s.DATAS, Datainst_ok s entry .OK

structure CoreTyped (s : AState) : Prop where
  typed : ATyped s
  contents : StoreContentsTyped s.store

theorem extern_global_lookup {s : store} {address : Nat} {ty : globaltype}
    (typed : Externaddr_ok s (.GLOBAL address) (.GLOBAL ty)) :
    ∃ object, s.GLOBALS[address]? = some object ∧ object.TYPE = ty := by
  generalize he : externaddr.GLOBAL address = external at typed
  generalize ht : externtype.GLOBAL ty = externalType at typed
  induction typed with
  | global a object bound found wf ext =>
    cases he
    cases ht
    refine ⟨object,?_,rfl⟩
    simpa [getElem!_pos, bound] using congrArg some found
  | sub external old new typed sub wf oldWf newWf ih =>
    cases sub with
    | global old new same _ _ =>
      cases same
      exact ih he ht
    | _ => cases ht
  | _ => cases he

theorem ModuleBindings.global_lookup {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) {index : Nat} {ty : globaltype}
    (found : C.GLOBALS[index]? = some ty) :
    ∃ address object, m.GLOBALS[index]? = some address ∧
      s.GLOBALS[address]? = some object ∧ object.TYPE = ty := by
  have right := (List.getElem?_eq_some_iff.mp found).1
  have left : index < m.GLOBALS.length := by rw [bindings.globals.length_eq]; exact right
  have relation := bindings.globals.get left right
  have value : C.GLOBALS[index] = ty := (List.getElem?_eq_some_iff.mp found).2
  simp only [List.get_eq_getElem, value] at relation
  obtain ⟨object,lookup,objectType⟩ := extern_global_lookup relation
  exact ⟨m.GLOBALS[index],object,List.getElem?_eq_getElem left,lookup,objectType⟩

theorem StoreContentsTyped.global_value {s : store} (contents : StoreContentsTyped s)
    {address : Nat} {global : globalinst} {mutable : «mut»} {ty : valtype}
    (found : s.GLOBALS[address]? = some global)
    (type : global.TYPE = .mk_globaltype mutable ty) : Val_ok s global.VALUE ty := by
  have typed := contents.globals global (List.mem_of_getElem? found)
  cases typed with
  | mk_Globalinst_ok actual valueType value globalType valueTyped wf valueWf =>
    cases type
    exact valueTyped

end Itasca.Runtime.SourceMachine

end

/-! ## ContentExtension -/

section

namespace Itasca.Runtime.SourceMachine
open Itasca.Runtime.Spec

theorem globalinst_typed_extend {before after : store} (extension : Extend_store before after)
    {object ty} (typed : Globalinst_ok before object ty) : Globalinst_ok after object ty := by
  cases typed with
  | mk_Globalinst_ok mutable type value typeOk valueOk _ wf =>
    exact .mk_Globalinst_ok _ _ _ _ typeOk (val_typed_extend extension valueOk)
      (extend_store_wf extension).2 wf

theorem tableinst_typed_extend {before after : store} (extension : Extend_store before after)
    {object ty} (typed : Tableinst_ok before object ty) : Tableinst_ok after object ty := by
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ wf typeWf =>
    exact .mk_Tableinst_ok _ _ _ _ _ typeOk
      (fun value member => ref_ok_extend extension (refsOk value member)) length
      (extend_store_wf extension).2 wf typeWf

theorem meminst_typed_extend {before after : store} (extension : Extend_store before after)
    {object ty} (typed : Meminst_ok before object ty) : Meminst_ok after object ty := by
  cases typed with
  | mk_Meminst_ok count maximum bytes typeOk length _ wf typeWf =>
    exact .mk_Meminst_ok _ _ _ _ typeOk length (extend_store_wf extension).2 wf typeWf

/-- The unchanged payloads remain typed after a store mutation; the replacement
itself must be checked at its declared type. -/
theorem StoreContentsTyped.global_replacement {before after : store}
    (contents : StoreContentsTyped before) (extension : Extend_store before after)
    (address : Nat) (object : globalinst)
    (globals : after.GLOBALS = before.GLOBALS.set address object)
    (tables : after.TABLES = before.TABLES) (memories : after.MEMS = before.MEMS)
    (elements : after.ELEMS = before.ELEMS) (data : after.DATAS = before.DATAS)
    (replacement : Globalinst_ok after object object.TYPE) : StoreContentsTyped after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [globals]
    have old : ∀ global ∈ before.GLOBALS, Globalinst_ok after global global.TYPE :=
      fun global member => globalinst_typed_extend extension (contents.globals global member)
    intro global member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact old global member
    · exact replacement
  · intro table member
    rw [tables] at member
    exact tableinst_typed_extend extension (contents.tables table member)
  · intro memory member
    rw [memories] at member
    exact meminst_typed_extend extension (contents.memories memory member)
  · intro element member
    rw [elements] at member
    exact eleminst_ok_extend extension (extend_elem_refl element) (contents.elements element member)
  · intro entry member
    rw [data] at member
    have typed := contents.data entry member
    have wf : wf_datainst entry := by cases typed; assumption
    exact datainst_ok_extend extension (extend_data_refl entry wf) typed

end Itasca.Runtime.SourceMachine

end

/-! ## GlobalContents -/

section

/-!
Global store update contents and mutation certificates, feeding typed source global execution.
-/

/-! ## Global Mutation -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem global_write_as_set (s : store) (f : frame) (index address : Nat)
    (object : globalinst) (value : val) (mapped : f.MODULE.GLOBALS[index]? = some address)
    (found : s.GLOBALS[address]? = some object) :
    Spec.globalWrite s f index value =
      {s with GLOBALS := s.GLOBALS.set address {object with VALUE := value}} := by
  simp only [Spec.globalWrite, List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

/-- A typed mutable-global write extends the source store. Unlike raw extension,
this theorem retains the declared value type of the new payload. -/
theorem global_write_extends (s : store) (f : frame) (index address : Nat)
    (object : globalinst) (value : val) (ty : valtype)
    (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.GLOBALS[index]? = some address)
    (found : s.GLOBALS[address]? = some object)
    (mutable : object.TYPE = .mk_globaltype (some .MUT) ty)
    (valueTyped : Val_ok s value ty) : Extend_store s (Spec.globalWrite s f index value) := by
  have oldWf : wf_globalinst object := by
    have global := contents.globals object (List.mem_of_getElem? found)
    cases global
    assumption
  have valueWf := val_ok_wf valueTyped
  have freshWf := Spec.global_write_wf s f index value wf valueWf
  have same := global_write_as_set s f index address object value mapped found
  rw [same] at freshWf ⊢
  apply Spec.extend_store_set_global _ _ _ wf freshWf
  intro bound
  have atAddress : s.GLOBALS[address]! = object := by simp [List.getElem!_eq_getElem?_getD,found]
  rw [atAddress]
  cases object with
  | MKglobalinst type old =>
    dsimp only at mutable
    cases mutable
    exact Spec.extend_global_mutable ty old value oldWf (.globalinst_case_ _ _ valueWf)

end Itasca.Runtime.SourceMachine

end

/-! ## Global Contents -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem StoreContentsTyped.global_write {s : store} (contents : StoreContentsTyped s)
    (wf : wf_store s) (f : frame) (index address : Nat) (object : globalinst) (value : val) (ty : valtype)
    (mapped : f.MODULE.GLOBALS[index]? = some address) (found : s.GLOBALS[address]? = some object)
    (mutable : object.TYPE = .mk_globaltype (some .MUT) ty) (valueTyped : Val_ok s value ty) :
    StoreContentsTyped (Spec.globalWrite s f index value) := by
  have extension := global_write_extends s f index address object value ty wf contents mapped found mutable valueTyped
  have valueFresh := val_typed_extend extension valueTyped
  have freshWf := (extend_store_wf extension).2
  have objectFresh : Globalinst_ok (Spec.globalWrite s f index value)
      {object with VALUE := value} {object with VALUE := value}.TYPE := by
    cases object with
    | MKglobalinst type old =>
      dsimp only at mutable
      cases mutable
      exact .mk_Globalinst_ok _ _ _ _ (.mk_Globaltype_ok _ _) valueFresh freshWf
        (.globalinst_case_ _ _ (val_ok_wf valueFresh))
  exact contents.global_replacement extension address {object with VALUE := value}
    (congrArg store.GLOBALS (global_write_as_set s f index address object value mapped found))
    rfl rfl rfl rfl objectFresh

end Itasca.Runtime.SourceMachine

end

end

/-! ## GlobalTyping -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- The canonical global typing rule and actual module binding identify a
concrete, correctly typed global value and its continuation. -/
theorem global_get_frame_typed {s : store} {f : AFrame} {code : List instr}
    {index : Nat} (contents : StoreContentsTyped s)
    (h : FrameTyped s { f with code := .GLOBAL_GET (.mk_uN index) :: code } []) :
    ∃ address object, f.module.GLOBALS[index]? = some address ∧
      s.GLOBALS[address]? = some object ∧
      FrameTyped s {f with code := code, vals := f.vals ++ [object.VALUE]} [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front,ins,outs,hop,hstack,hafter⟩ := code_stack_after (value_types_concrete f.vals) hc
    cases hop with
    | global_get _ _ ty mutable hi ht _ _ =>
      have bound : index < C.GLOBALS.length := by simpa [labelContext,proj_uN_0] using hi
      have sourceType : C.GLOBALS[index]? = some (.mk_globaltype mutable ty) := by
        simp only [labelContext,proj_uN_0] at ht
        simpa [getElem!_pos, bound] using congrArg some ht
      obtain ⟨address,object,mapped,found,typed⟩ := bindings.global_lookup sourceType
      have value := contents.global_value found typed
      have actualType := value_type_of_typed value
      refine ⟨address,object,mapped,found,?_⟩
      apply FrameTyped.mk (f := {f with code := code, vals := f.vals ++ [object.VALUE]}) C
        bindings localTypes locals ?_ returns ?_ hw
      · simpa only [ResultsTyped,List.map_append,List.map_cons,List.map_nil,actualType] using
          List.rel_append values (List.Forall₂.cons value List.Forall₂.nil)
      · simp only [List.append_nil] at hstack
        simpa only [List.map_append,List.map_cons,List.map_nil,List.append_nil,hstack,actualType] using hafter

/-- Popping a typed global.set operand preserves the code continuation in the
old store. The separate typed content update then transports this frame. -/
theorem global_set_frame_continuation {s : store} {f : AFrame} {code : List instr}
    {index : Nat} {front : List val} {value : val}
    (h : FrameTyped s {f with code := .GLOBAL_SET (.mk_uN index) :: code, vals := front ++ [value]} []) :
    ∃ address object ty, f.module.GLOBALS[index]? = some address ∧
      s.GLOBALS[address]? = some object ∧ object.TYPE = .mk_globaltype (some .MUT) ty ∧
      Val_ok s value ty ∧ FrameTyped s {f with code := code, vals := front} [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨base,ins,outs,hop,hstack,hafter⟩ :=
      code_stack_after (value_types_concrete (front ++ [value])) hc
    cases hop with
    | global_set _ _ ty hi ht _ _ =>
      have bound : index < C.GLOBALS.length := by simpa [labelContext,proj_uN_0] using hi
      have sourceType : C.GLOBALS[index]? = some (.mk_globaltype (some .MUT) ty) := by
        simp only [labelContext,proj_uN_0] at ht
        simpa [getElem!_pos, bound] using congrArg some ht
      obtain ⟨address,object,mapped,found,typed⟩ := bindings.global_lookup sourceType
      simp only [List.map_append,List.map_cons,List.map_nil] at hstack
      have sameLength : (front.map valueType).length = base.length := by
        have lengths := congrArg List.length hstack
        simp only [List.length_append,List.length_cons,List.length_nil] at lengths
        omega
      obtain ⟨baseEq,lastEq⟩ := List.append_inj hstack sameLength
      have valueTypeEq : valueType value = ty := by simpa using lastEq
      have valueTyped : Val_ok s value ty := by
        have self := results_typed_self_mem (value := value) values (by simp)
        simpa only [valueTypeEq] using self
      refine ⟨address,object,ty,mapped,found,typed,valueTyped,?_⟩
      have prefixTyped : ResultsTyped s (front.map valueType) front := by
        simpa using results_typed_take front.length values
      apply FrameTyped.mk (f := {f with code := code, vals := front}) C
        bindings localTypes locals prefixTyped returns ?_ hw
      simpa only [List.append_nil,baseEq] using hafter

end Itasca.Runtime.SourceMachine

end

/-! ## Simulation -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- Lift a store-changing redex through the active operand stack, labels and
suspended callers. The same frame syntax is interpreted in the new store. -/
theorem mutable_stack_simulation (before afterStore : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val)
    (ha : wf_frame ambient)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (step : StepH ⟨⟨before, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨afterStore, f.toFrame⟩, vals produced⟩) :
    StepH (decode ⟨before, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨afterStore, ambient,
      { f with code := after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have h₁ := step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := step_h_decode_labels h₁ f.labels baseValues hl hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights, decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

theorem global_get_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat) (global : globalinst)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ f.vals.length)
    (hi : index < 2^32) (mapped : f.module.GLOBALS[index]? = some address)
    (found : s.GLOBALS[address]? = some global) :
    StepH (decode ⟨s, ambient,
      { f with code := .GLOBAL_GET (.mk_uN index) :: after } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := f.vals ++ [global.VALUE] } :: rest, []⟩) := by
  have step := Spec.global_get_step s f.toFrame index address global hs hf hi mapped found
  simpa [vals,admininstr_instr] using mutable_stack_simulation s s ambient f rest
    (.GLOBAL_GET (.mk_uN index)) after f.vals [] [global.VALUE] ha hl hv hc hr heights step

theorem global_set_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index : Nat) (front : List val) (value : val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front) (valueWf : wf_val value)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (hi : index < 2^32) (mapped : index < f.module.GLOBALS.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .GLOBAL_SET (.mk_uN index) :: after, vals := front ++ [value] } :: rest, []⟩) []
      (decode ⟨Spec.globalWrite s f.toFrame index value, ambient,
      { f with code := after, vals := front } :: rest, []⟩) := by
  have step := Spec.global_set_step s f.toFrame index value hs hf hi valueWf mapped
  simpa [vals,admininstr_instr] using mutable_stack_simulation s
    (Spec.globalWrite s f.toFrame index value) ambient f rest
    (.GLOBAL_SET (.mk_uN index)) after front [value] [] ha hl hv hc hr heights step

end Itasca.Runtime.SourceMachine

end

/-! ## Globals -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

/-- Resolve the owning instance's global address before reading its value. -/
def globalGet (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match f.module.GLOBALS[index]? with
  | none => .stuck
  | some address => match s.store.GLOBALS[address]? with
    | none => .stuck
    | some object => advance s {f with code := after, vals := f.vals ++ [object.VALUE]} rest

/-- Global writes retain declared mutability/type and change one payload. -/
def globalSet (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat) (after : List instr) : AResult :=
  match pop f.vals, f.module.GLOBALS[index]? with
  | some (front,value), some address =>
    match s.store.GLOBALS[address]? with
    | none => .stuck
    | some object =>
      match object.TYPE with
      | .mk_globaltype none _ => .stuck
      | .mk_globaltype (some .MUT) ty =>
        if valueType value = ty then
          advance {s with store := Spec.globalWrite s.store f.toFrame index value}
            {f with code := after, vals := front} rest
        else .stuck
  | _,_ => .stuck

/-- Typed global reads are executable, preserve full source typing, and take
one generated source reduction under every active/suspended context. -/
theorem global_get_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, globalGet ⟨s,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩
      f rest index after = .next next ∧ CoreTyped next ∧
      StepH (decode ⟨s,ambient,{f with code := .GLOBAL_GET (.mk_uN index) :: after} :: rest,[]⟩) [] (decode next) := by
  have frameTyped : FrameTyped s {f with code := .GLOBAL_GET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨address,object,mapped,found,continuation⟩ := global_get_frame_typed typed.contents frameTyped
  let next : AState := ⟨s,ambient,{f with code := after, vals := f.vals ++ [object.VALUE]} :: rest,[]⟩
  have fresh : ATyped next := active_frame_preservation typed.typed continuation rfl
  refine ⟨next,?_,⟨fresh,typed.contents⟩,?_⟩
  · simp only [globalGet,mapped,found,advance,next]
  · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
    have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
    have restWf : Forall FrameWf rest := by
      cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
    have indexWf := codeWf (.GLOBAL_GET (.mk_uN index)) (by simp)
    have bound : index < 2^32 := by
      cases indexWf with | instr_case_46 _ valid =>
      cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
    exact global_get_simulation s ambient f rest after index address object
      typed.typed.store typed.typed.ambient frameWf labelsWf valuesWf tailWf restWf
      (by simpa only [FrameHeights] using frame_typed_heights frameTyped) bound mapped found

/-- Typed writes make one source transition, preserve all store payload typing,
and leave every saved frame valid in the extended store. -/
theorem global_set_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (index : Nat) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) :
    ∃ next, globalSet ⟨s,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩
      f rest index after = .next next ∧ CoreTyped next ∧ Extend_store s next.store ∧
      StepH (decode ⟨s,ambient,{f with code := .GLOBAL_SET (.mk_uN index) :: after} :: rest,[]⟩) [] (decode next) := by
  have frameTyped : FrameTyped s {f with code := .GLOBAL_SET (.mk_uN index) :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,ins,outs,_,_,operation,split,operandTypes,frontWf,heights⟩ :=
    frame_typed_operands_bounds frameTyped
  cases operation
  cases operandTypes with
  | cons valueTyped tail =>
    cases tail
    rename_i value
    have decomposed : FrameTyped s
        {f with code := .GLOBAL_SET (.mk_uN index) :: after, vals := front ++ [value]} [] := by
      simpa only [split] using frameTyped
    obtain ⟨address,object,ty,mapped,found,mutable,valueOk,continuation⟩ := global_set_frame_continuation decomposed
    have extension := global_write_extends s f.toFrame index address object value ty
      typed.typed.store typed.contents mapped found mutable valueOk
    have contents := typed.contents.global_write typed.typed.store f.toFrame index address object value ty
      mapped found mutable valueOk
    have oldTyped := active_frame_preservation typed.typed continuation rfl
    have fresh := oldTyped.extend_same extension rfl
    let next : AState := ⟨Spec.globalWrite s f.toFrame index value,ambient,
      {f with code := after, vals := front} :: rest,[]⟩
    refine ⟨next,?_,⟨fresh,contents⟩,extension,?_⟩
    · simp only [globalSet,split,pop_append,mapped,found,mutable,value_type_of_typed valueOk,
        ite_true,advance,next]
    · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
      have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
      have restWf : Forall FrameWf rest := by
        cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
      have indexWf := codeWf (.GLOBAL_SET (.mk_uN index)) (by simp)
      have bound : index < 2^32 := by
        cases indexWf with | instr_case_47 _ valid =>
        cases valid with | uN_case_0 _ valid => norm_num at valid ⊢; omega
      have source := global_set_simulation s ambient f rest after index front value
        typed.typed.store typed.typed.ambient frameWf labelsWf frontWf (val_ok_wf valueOk)
        tailWf restWf heights bound (List.getElem?_eq_some_iff.mp mapped).1
      simpa only [split,next] using source

end Itasca.Runtime.SourceMachine.Core

end

/-! ## Select -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

def select (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr) : AResult :=
  match pop f.vals with
  | some (remaining,condition) => match integer .I32 condition, pop remaining with
    | some bits, some (remaining,right) => match pop remaining with
      | some (front,left) =>
        if valueType left = valueType right then
          advance s {f with code := after, vals := front ++ [if bits = 0 then right else left]} rest
        else .stuck
      | none => .stuck
    | _,_ => .stuck
  | none => .stuck

theorem select_frame_preservation {s : store} {f : AFrame} {after : List instr}
    {front : List val} {left right : val} {bits : Nat}
    (typed : FrameTyped s {f with code := .SELECT none :: after, vals := front ++ [left,right,integerVal .I32 bits]} []) :
    FrameTyped s {f with code := after, vals := front ++ [if bits = 0 then right else left]} [] := by
  cases typed with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨base,ins,outs,operation,stack,continuation⟩ :=
      code_stack_after (value_types_concrete (front ++ [left,right,integerVal .I32 bits])) hc
    cases operation with
    | select_impl _ ty type numeric vector sub allowed contextWf instructionWf =>
      simp only [List.map_append,List.map_cons,List.map_nil] at stack
      have length : (front.map valueType).length = base.length := by
        have lengths := congrArg List.length stack
        simp only [List.length_append,List.length_cons,List.length_nil] at lengths
        omega
      obtain ⟨baseEq,types⟩ := List.append_inj stack length
      simp only [List.cons.injEq] at types
      have leftType : valueType left = ty := types.1
      have rightType : valueType right = ty := types.2.1
      have selectedTyped : Val_ok s (if bits = 0 then right else left) ty := by
        split
        · simpa only [rightType] using results_typed_self_mem (value := right) values (by simp)
        · simpa only [leftType] using results_typed_self_mem (value := left) values (by simp)
      have selectedType := value_type_of_typed selectedTyped
      have prefixTyped : ResultsTyped s (front.map valueType) front := by
        simpa using results_typed_take front.length values
      apply FrameTyped.mk (f := {f with code := after, vals := front ++ [if bits = 0 then right else left]}) C
        bindings localTypes locals ?_ returns ?_ hw
      · simpa only [ResultsTyped,List.map_append,List.map_cons,List.map_nil,selectedType] using
          List.rel_append prefixTyped (List.Forall₂.cons selectedTyped List.Forall₂.nil)
      · simpa only [List.map_append,List.map_cons,List.map_nil,List.append_nil,selectedType,baseEq] using continuation

theorem select_simulation (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (left right : val) (bits : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (leftWf : wf_val left) (rightWf : wf_val right) (bitsBound : bits < 2^32) :
    StepH (decode ⟨s,ambient,
      {f with code := .SELECT none :: after, vals := front ++ [left,right,integerVal .I32 bits]} :: rest,[]⟩) []
      (decode ⟨s,ambient,{f with code := after, vals := front ++ [if bits = 0 then right else left]} :: rest,[]⟩) := by
  have conditionWf := integer_val_wf .I32 bits bitsBound
  have selectWf : wf_instr (.SELECT none) := .instr_case_3 _
  apply pure_stack_simulation s ambient f rest (.SELECT none) after front
    [left,right,integerVal .I32 bits] [if bits = 0 then right else left]
    hs ha hf hl hv hc hr heights
  · simpa [Forall] using And.intro leftWf (And.intro rightWf conditionWf)
  · by_cases zero : bits = 0 <;> simp [zero,Forall,leftWf,rightWf]
  · exact selectWf
  · by_cases zero : bits = 0
    · simpa [vals,integerVal,admininstr_val,admininstr_instr,numtype_Inn,zero] using
        Step_pure.select_false left right (.mk_num__0 .I32 (.mk_uN bits)) none
          (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0]) leftWf rightWf
          (.admininstr_case_13 _ _ (integer_num_wf .I32 bits bitsBound)) (wf_admininstr_instr selectWf)
    · simpa [vals,integerVal,admininstr_val,admininstr_instr,numtype_Inn,zero] using
        Step_pure.select_true left right (.mk_num__0 .I32 (.mk_uN bits)) none
          (by simp [proj_num__0]) (by simpa [proj_num__0,proj_uN_0]) leftWf rightWf
          (.admininstr_case_13 _ _ (integer_num_wf .I32 bits bitsBound)) (wf_admininstr_instr selectWf)

/-- The generated select rule supplies two equally typed alternatives and an
i32 condition, so the executable branch is total on every typed frame. -/
theorem select_progress (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := .SELECT none :: after} :: rest,[]⟩) :
    ∃ next, select ⟨s,ambient,{f with code := .SELECT none :: after} :: rest,[]⟩
      f rest after = .next next ∧ CoreTyped next ∧
      StepH (decode ⟨s,ambient,{f with code := .SELECT none :: after} :: rest,[]⟩) [] (decode next) := by
  have frameTyped : FrameTyped s {f with code := .SELECT none :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  obtain ⟨C,front,operands,ins,outs,_,_,operation,split,operandTypes,frontWf,heights⟩ :=
    frame_typed_operands_bounds frameTyped
  cases operation
  cases operandTypes with
  | cons leftTyped tail =>
    cases tail with
    | cons rightTyped tail =>
      cases tail with
      | cons conditionTyped tail =>
        cases tail
        rename_i left right condition
        obtain ⟨bits,rfl,bitsBound⟩ := integer_val_inv (ty := .I32) conditionTyped
        have matching : valueType left = valueType right :=
          (value_type_of_typed leftTyped).trans (value_type_of_typed rightTyped).symm
        have continuation := select_frame_preservation (bits := bits) (by simpa only [split] using frameTyped)
        have fresh := active_frame_preservation typed.typed continuation rfl
        let next : AState := ⟨s,ambient,
          {f with code := after, vals := front ++ [if bits = 0 then right else left]} :: rest,[]⟩
        refine ⟨next,?_,⟨fresh,typed.contents⟩,?_⟩
        · have shape : f.vals = ((front ++ [left]) ++ [right]) ++ [integerVal .I32 bits] := by
            simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
          have decoded : integer .I32 (integerVal .I32 bits) = some bits := by
            simpa only [numtype_Inn] using integer_accepts .I32 bits bitsBound
          simp only [select,shape,pop_append,decoded,matching,
            ite_true,advance,next]
        · obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
          have tailWf : Forall wf_instr after := fun instruction member => codeWf instruction (by simp [member])
          have restWf : Forall FrameWf rest := by
            cases typed.typed.frames with | cons _ tail => exact frames_typed_wf tail
          have source := select_simulation s ambient f rest after front left right bits
            typed.typed.store typed.typed.ambient frameWf labelsWf frontWf tailWf restWf heights
            (val_ok_wf leftTyped) (val_ok_wf rightTyped) bitsBound
          simpa only [split,next] using source

end Itasca.Runtime.SourceMachine.Core

end

/-! ## MemoryStep -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt

/-- Scalar loads resolve memory zero in the current instance and use unwrapped
natural effective-address arithmetic before decoding the selected bytes. -/
def load (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Memory.Load) (argument : memarg) : AResult :=
  match pop f.vals,f.module.MEMS[0]? with
  | some (front,address),some memoryAddress =>
    match integer .I32 address,s.store.MEMS[memoryAddress]? with
    | some bits,some object =>
      let start := bits + proj_uN_0 argument.OFFSET
      if start + op.bytes ≤ object.BYTES.length then
        advance s {f with code := after, vals := front ++ [op.value ((object.BYTES.drop start).take op.bytes)]} rest
      else .trap
    | _,_ => .stuck
  | _,_ => .stuck

/-- Scalar stores retain the source memory's type and length, replacing only
an in-bounds byte interval. Operand decoding precedes the write. -/
def store (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Memory.Store) (argument : memarg) : AResult :=
  match pop f.vals,f.module.MEMS[0]? with
  | some (remaining,.CONST ty value),some memoryAddress =>
    if ty = op.type then
      match pop remaining,s.store.MEMS[memoryAddress]? with
      | some (front,address),some object =>
        match integer .I32 address with
        | none => .stuck
        | some bits =>
          let start := bits + proj_uN_0 argument.OFFSET
          if start + op.bytes ≤ object.BYTES.length then
            advance {s with store := Spec.memoryPayloadWrite s.store f.toFrame start (op.payload value)}
              {f with code := after, vals := front} rest
          else .trap
      | _,_ => .stuck
    else .stuck
  | _,_ => .stuck

end Itasca.Runtime.SourceMachine.Core

end

/-! ## Step -/

section

namespace Itasca.Runtime.SourceMachine.Core

/-- Execute a scalar Core instruction. Pure integer/control instructions reuse
the established transition; mutable instructions resolve their own store maps. -/
def instruction (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (op : instr) (after : List instr) : AResult :=
  let state : AState := ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩
  match op with
  | .CONST ty value => advance state {f with code := after, vals := f.vals ++ [.CONST ty value]} rest
  | .SELECT none => select state f rest after
  | .GLOBAL_GET (.mk_uN index) => globalGet state f rest index after
  | .GLOBAL_SET (.mk_uN index) => globalSet state f rest index after
  | .LOAD ty packed argument =>
    match Memory.decodeLoad ty packed with
    | some descriptor => load state f rest after descriptor argument
    | none => .stuck
  | .STORE ty packed argument =>
    match Memory.decodeStore ty packed with
    | some descriptor => store state f rest after descriptor argument
    | none => .stuck
  | _ => astep state

/-- Mutable scalar abstract execution. Host calls remain an explicit boundary;
no host result is manufactured by the pure machine. -/
def step (s : AState) : AResult :=
  match s.frames with
  | [] => .done s.results
  | f :: rest =>
    match f.code with
    | [] => astep s
    | op :: after => instruction s.store s.ambient f rest op after

theorem instruction_load (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Load) (argument : memarg) :
    instruction s ambient f rest (op.source argument) after =
      load ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after op argument := by
  simp only [instruction,Memory.Load.source,Memory.decode_load_descriptor]

theorem instruction_store (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Memory.Store) (argument : memarg) :
    instruction s ambient f rest (op.source argument) after =
      store ⟨s,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after op argument := by
  simp only [instruction,Memory.Store.source,Memory.decode_store_descriptor]

end Itasca.Runtime.SourceMachine.Core

end

/-! ## Pure -/

section

namespace Itasca.Runtime.SourceMachine.Core
open SpecExt Itasca.Runtime.Spec

theorem instruction_slice (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : PureHead op)
    (typed : FrameTyped s {f with code := op :: after} []) :
    instruction s ambient f rest op after =
      astep ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩ := by
  cases covered with
  | numeric descriptor =>
    cases descriptor with
    | conversion conversion => cases conversion <;> rfl
    | _ => rfl
  | const ty value =>
    have progress := const_progress s ambient f rest after ty value typed
    simp only [instruction,astep] at progress ⊢
    split <;> simp_all [advance]
  | local_get index => cases index; rfl
  | local_set index => cases index; rfl
  | local_tee index => cases index; rfl
  | br index => cases index; rfl
  | br_if index => cases index; rfl
  | call index => cases index; rfl
  | _ => rfl

/-- All numeric constants, including floating encodings, are administrative
moves with identical source decoding and a strictly decreasing potential. -/
theorem constant_progress (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (ty : numtype) (value : num_)
    (typed : CoreTyped ⟨s,ambient,{f with code := .CONST ty value :: after} :: rest,[]⟩) :
    ∃ next, instruction s ambient f rest (.CONST ty value) after = .next next ∧ CoreTyped next ∧
      NextSim ⟨s,ambient,{f with code := .CONST ty value :: after} :: rest,[]⟩ next := by
  let next : AState := ⟨s,ambient,{f with code := after, vals := f.vals ++ [.CONST ty value]} :: rest,[]⟩
  have fresh := const_preservation s ambient f rest after ty value [] typed.typed
  have frameTyped : FrameTyped s {f with code := .CONST ty value :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  refine ⟨next,rfl,⟨fresh,typed.contents⟩,Or.inl ⟨?_,?_⟩⟩
  · exact decode_const s ambient f rest ty value after (by simpa only [FrameHeights] using frame_typed_heights frameTyped)
  · exact const_measure_decreases s ambient f rest ty value after

end Itasca.Runtime.SourceMachine.Core

end

/-! ## PureMetadata -/

section

namespace Itasca.Runtime.SourceMachine

/-- Every legacy pure abstract transition retains its source store exactly,
including control transfer, defined calls, and function returns. -/
theorem astep_store {s next : AState} (step : astep s = .next next) : next.store = s.store := by
  simp only [astep] at step
  repeat' first | split at step | contradiction
  all_goals
    simp only [advance,returnFrame,enterLabel,branch,call,Numeric.transition,Numeric.finish] at step
    repeat' first | split at step | contradiction
    all_goals
      simp only [advance,AResult.next.injEq] at step
      cases step
      rfl

end Itasca.Runtime.SourceMachine

end

/-! ## MemoryTyping -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem extern_mem_lookup {s : store} {address : Nat} {ty : memtype}
    (typed : Externaddr_ok s (.MEM address) (.MEM ty)) :
    ∃ object, s.MEMS[address]? = some object := by
  generalize he : externaddr.MEM address = external at typed
  generalize ht : externtype.MEM ty = externalType at typed
  induction typed generalizing ty with
  | mem a object bound found wf ext =>
    cases he
    cases ht
    refine ⟨object,?_⟩
    simpa [getElem!_pos, bound] using congrArg some found
  | sub external old new typed sub wf oldWf newWf ih =>
    cases sub with
    | mem old new relation _ _ => exact ih he rfl
    | _ => cases ht
  | _ => cases he

theorem ModuleBindings.memory_lookup {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) (present : 0 < C.MEMS.length) :
    ∃ address object, m.MEMS[0]? = some address ∧ s.MEMS[address]? = some object := by
  have left : 0 < m.MEMS.length := by rw [bindings.mems.length_eq]; exact present
  have relation := bindings.mems.get left present
  obtain ⟨object,lookup⟩ := extern_mem_lookup relation
  exact ⟨m.MEMS[0],object,List.getElem?_eq_getElem left,lookup⟩

theorem memory_load_typing {C : context} {ty : numtype} {packed : Option loadop_}
    (argument : memarg) {ins outs}
    (typed : Instr_ok C (.LOAD ty packed argument) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.I32] ∧ outs = [valtype_numtype ty] ∧ 0 < C.MEMS.length := by
  cases typed with
  | load_val => exact ⟨rfl,rfl,by assumption⟩
  | load_pack _ ty => cases ty <;> exact ⟨rfl,rfl,by assumption⟩

theorem memory_store_typing {C : context} {ty : numtype} {packed : Option sz}
    (argument : memarg) {ins outs}
    (typed : Instr_ok C (.STORE ty packed argument) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.I32,valtype_numtype ty] ∧ outs = [] ∧ 0 < C.MEMS.length := by
  cases typed with
  | store_val => exact ⟨rfl,rfl,by assumption⟩
  | store_pack _ ty => cases ty <;> exact ⟨rfl,rfl,by assumption⟩

theorem Memory.Load.typing {C : context} (op : Memory.Load) (argument : memarg) {ins outs}
    (typed : Instr_ok C (op.source argument) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.I32] ∧ outs = [valtype_numtype op.type] ∧ 0 < C.MEMS.length :=
  memory_load_typing argument typed

theorem Memory.Store.typing {C : context} (op : Memory.Store) (argument : memarg) {ins outs}
    (typed : Instr_ok C (op.source argument) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.I32,valtype_numtype op.type] ∧ outs = [] ∧ 0 < C.MEMS.length :=
  memory_store_typing argument typed

theorem memory_load_frame_continuation {s : store} {f : AFrame} {code : List instr}
    (op : Memory.Load) (argument : memarg) {front : List val} {address value : val}
    (h : FrameTyped s {f with code := op.source argument :: code, vals := front ++ [address]} [])
    (result : Val_ok s value (valtype_numtype op.type)) :
    ∃ memoryAddress object, f.module.MEMS[0]? = some memoryAddress ∧
      s.MEMS[memoryAddress]? = some object ∧
      FrameTyped s {f with code := code, vals := front ++ [value]} [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨base,ins,outs,operation,stack,continuation⟩ :=
      code_stack_after (value_types_concrete (front ++ [address])) hc
    obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
    obtain ⟨memoryAddress,object,mapped,found⟩ := bindings.memory_lookup present
    simp only [List.map_append,List.map_cons,List.map_nil] at stack
    have length : (front.map valueType).length = base.length := by
      have lengths := congrArg List.length stack
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨baseEq,lastEq⟩ := List.append_inj stack length
    have prefixTyped : ResultsTyped s (front.map valueType) front := by
      simpa using results_typed_take front.length values
    have actualType := value_type_of_typed result
    refine ⟨memoryAddress,object,mapped,found,?_⟩
    apply FrameTyped.mk (f := {f with code := code, vals := front ++ [value]}) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped,List.map_append,List.map_cons,List.map_nil,actualType] using
        List.rel_append prefixTyped (List.Forall₂.cons result List.Forall₂.nil)
    · simpa only [List.map_append,List.map_cons,List.map_nil,List.append_nil,actualType,baseEq] using continuation

theorem memory_store_frame_continuation {s : store} {f : AFrame} {code : List instr}
    (op : Memory.Store) (argument : memarg) {front : List val} {address value : val}
    (h : FrameTyped s {f with code := op.source argument :: code, vals := front ++ [address,value]} []) :
    ∃ memoryAddress object, f.module.MEMS[0]? = some memoryAddress ∧
      s.MEMS[memoryAddress]? = some object ∧
      FrameTyped s {f with code := code, vals := front} [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨base,ins,outs,operation,stack,continuation⟩ :=
      code_stack_after (value_types_concrete (front ++ [address,value])) hc
    obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
    obtain ⟨memoryAddress,object,mapped,found⟩ := bindings.memory_lookup present
    simp only [List.map_append,List.map_cons,List.map_nil] at stack
    have length : (front.map valueType).length = base.length := by
      have lengths := congrArg List.length stack
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    obtain ⟨baseEq,lastEq⟩ := List.append_inj stack length
    have prefixTyped : ResultsTyped s (front.map valueType) front := by
      simpa using results_typed_take front.length values
    refine ⟨memoryAddress,object,mapped,found,?_⟩
    apply FrameTyped.mk (f := {f with code := code, vals := front}) C
      bindings localTypes locals prefixTyped returns ?_ hw
    simpa only [List.append_nil,baseEq] using continuation

end Itasca.Runtime.SourceMachine

end

/-! ## MemoryMutation -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem memory_payload_write_as_set (s : store) (f : frame) (address start : Nat)
    (object : meminst) (payload : List byte) (mapped : f.MODULE.MEMS[0]? = some address)
    (found : s.MEMS[address]? = some object) :
    Spec.memoryPayloadWrite s f start payload =
      {s with MEMS := s.MEMS.set address {object with BYTES := splice object.BYTES payload start}} := by
  simp only [Spec.memoryPayloadWrite,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem splice_length {T : Type} (bytes payload : List T) (start : Nat) :
    (splice bytes payload start).length = bytes.length := by
  simp only [splice,List.length_append,List.length_take,List.length_drop]
  omega

theorem splice_wf (bytes payload : List byte) (start : Nat)
    (old : Forall wf_byte bytes) (fresh : Forall wf_byte payload) :
    Forall wf_byte (splice bytes payload start) := by
  intro byte member
  simp only [splice,List.mem_append] at member
  rcases member with (first | middle) | last
  · exact old byte (List.mem_of_mem_take first)
  · exact fresh byte (List.mem_of_mem_take middle)
  · exact old byte (List.mem_of_mem_drop last)

theorem memory_payload_write_extends (s : store) (f : frame) (address start : Nat)
    (object : meminst) (payload : List byte) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object)
    (payloadWf : Forall wf_byte payload) : Extend_store s (Spec.memoryPayloadWrite s f start payload) := by
  have typed := contents.memories object (List.mem_of_getElem? found)
  have freshWf := memory_payload_write_wf s f start payload wf payloadWf
  rw [memory_payload_write_as_set s f address start object payload mapped found] at freshWf ⊢
  apply extend_store_set_mem _ _ _ wf freshWf
  intro bound
  have atAddress : s.MEMS[address]! = object := by simp [List.getElem!_eq_getElem?_getD,found]
  rw [atAddress]
  cases typed with
  | mk_Meminst_ok count maximum bytes typeOk length storeWf objectWf typeWf =>
    have byteWf : Forall wf_byte bytes := by cases objectWf; assumption
    exact extend_mem_contents count count maximum bytes (splice bytes payload start)
      (by omega) (by rw [splice_length]) objectWf
      (.meminst_case_ _ _ typeWf (splice_wf bytes payload start byteWf payloadWf))

theorem StoreContentsTyped.memory_replacement {before after : store}
    (contents : StoreContentsTyped before) (extension : Extend_store before after)
    (address : Nat) (object : meminst)
    (memories : after.MEMS = before.MEMS.set address object)
    (globals : after.GLOBALS = before.GLOBALS) (tables : after.TABLES = before.TABLES)
    (elements : after.ELEMS = before.ELEMS) (data : after.DATAS = before.DATAS)
    (replacement : Meminst_ok after object object.TYPE) : StoreContentsTyped after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro global member
    rw [globals] at member
    exact globalinst_typed_extend extension (contents.globals global member)
  · intro table member
    rw [tables] at member
    exact tableinst_typed_extend extension (contents.tables table member)
  · intro memory member
    rw [memories] at member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact meminst_typed_extend extension (contents.memories memory member)
    · exact replacement
  · intro element member
    rw [elements] at member
    exact eleminst_ok_extend extension (extend_elem_refl element) (contents.elements element member)
  · intro entry member
    rw [data] at member
    have typed := contents.data entry member
    have wf : wf_datainst entry := by cases typed; assumption
    exact datainst_ok_extend extension (extend_data_refl entry wf) typed

theorem StoreContentsTyped.memory_write {s : store} (contents : StoreContentsTyped s)
    (wf : wf_store s) (f : frame) (address start : Nat) (object : meminst) (payload : List byte)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object)
    (payloadWf : Forall wf_byte payload) : StoreContentsTyped (Spec.memoryPayloadWrite s f start payload) := by
  have extension := memory_payload_write_extends s f address start object payload wf contents mapped found payloadWf
  have freshWf := (extend_store_wf extension).2
  have typed := contents.memories object (List.mem_of_getElem? found)
  have objectFresh : Meminst_ok (Spec.memoryPayloadWrite s f start payload)
      {object with BYTES := splice object.BYTES payload start} object.TYPE := by
    cases typed with
    | mk_Meminst_ok count maximum bytes typeOk length storeWf objectWf typeWf =>
      have byteWf : Forall wf_byte bytes := by cases objectWf; assumption
      exact .mk_Meminst_ok _ _ _ _ typeOk (by simpa only [splice_length] using length) freshWf
        (.meminst_case_ _ _ typeWf (splice_wf bytes payload start byteWf payloadWf)) typeWf
  exact contents.memory_replacement extension address {object with BYTES := splice object.BYTES payload start}
    (congrArg store.MEMS (memory_payload_write_as_set s f address start object payload mapped found))
    rfl rfl rfl rfl objectFresh

end Itasca.Runtime.SourceMachine

end

/-! ## Trap -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- An instruction-local bounds or arithmetic trap unwinds all labels and
callers after consuming exactly the typed redex operands. -/
theorem operand_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (front consumed : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (step : StepH ⟨⟨s,f.toFrame⟩,vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s,f.toFrame⟩,[.TRAP]⟩) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s,ambient,{f with code := instruction :: after, vals := front ++ consumed} :: rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ := by
  have lifted := step_h_active ambient rest f.arity
    (step_h_decode_labels (step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
      f.labels front hl hv) ha hr
  have framesWf : Forall FrameWf ({f with code := after, vals := front} :: rest) := by
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨hf,hl,hv,hc⟩
    · exact hr frame member
  obtain ⟨n,tail⟩ := trap_frames s ambient ({f with code := after, vals := front} :: rest) hs ha framesWf
  refine ⟨n+1,by omega,?_⟩
  have combined := StepsHN.cons lifted tail
  simp only [decode,decodeFrames,vals,List.map_nil,List.nil_append,List.map_cons,AFrame.toFrame,AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [decodeFrames,frameContext,instrContext,vals,List.append_assoc,AFrame.toFrame,AFrame.arity] using combined

end Itasca.Runtime.SourceMachine

end
