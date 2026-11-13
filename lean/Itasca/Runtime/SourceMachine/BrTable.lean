import Itasca.Runtime.SourceMachine.Sim.Step
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.Sim.Terminal
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.SourceMachine.Decode
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Simd.Exclusion
import Itasca.Runtime.SourceMachine.Core.Typing
import Itasca.Runtime.Spec.Typing.HostTyping
import Itasca.Runtime.SourceMachine.Sim.Compose

/-!
Sections, each formerly its own module: Invoke, Results, ReferenceBounds, LabelHeights, SupportedState, ExecutableExclusion, StoreTyping, BrTable.
-/

/-! ## Invoke -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

def entryState (s : store) (ambient : frame) (address : funcaddr)
    (moduleInst : moduleinst) (results : List valtype) (body : List instr)
    (args defaults : List val) : AState :=
  ⟨s, ambient, [⟨address, results, args ++ defaults, moduleInst,
    [⟨results, results, [], 0, []⟩], body, []⟩], []⟩

end Itasca.Runtime.SourceMachine

end

/-! ## Results -/

section

/-!
Retention of the invocation result signature through source-machine frames. The outermost frame and final returned values keep the declared result types while inner calls may use other signatures.
-/

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- The outermost active function retains the invocation's declared results;
inner callees may have independent signatures. -/
inductive FramesReturn (expected : List valtype) : List AFrame → Prop where
  | last {f : AFrame} : f.resultTypes = expected → FramesReturn expected [f]
  | under {f : AFrame} {rest : List AFrame} : FramesReturn expected rest → FramesReturn expected (f :: rest)

/-- Attach an invocation signature until all frames finish, then require its
actual returned values to have that exact signature. -/
def InvocationResult (expected : List valtype) (s : AState) : Prop :=
  match s.frames with
  | [] => ResultsTyped s.store expected s.results
  | frames => FramesReturn expected frames

theorem FramesReturn.replace {expected : List valtype} {f f' : AFrame} {rest : List AFrame}
    (h : FramesReturn expected (f :: rest)) (same : f'.resultTypes = f.resultTypes) :
    FramesReturn expected (f' :: rest) := by
  cases h with
  | last result => exact .last (same.trans result)
  | under rest => exact .under rest

theorem entry_result (s : store) (ambient : frame) (address : funcaddr)
    (moduleInst : moduleinst) (results : List valtype) (body : List instr)
    (args defaults : List val) :
    InvocationResult results (entryState s ambient address moduleInst results body args defaults) :=
  .last rfl

theorem advance_result {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} {next : AState} {expected : List valtype}
    (h : InvocationResult expected ⟨s, ambient, f :: rest, []⟩)
    (step : advance ⟨s, ambient, f :: rest, []⟩ f' rest = .next next)
    (same : f'.resultTypes = f.resultTypes) : InvocationResult expected next := by
  simp only [advance, AResult.next.injEq] at step
  rw [← step]
  exact FramesReturn.replace h same

theorem return_frame_result {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {next : AState} {expected : List valtype}
    (typed : ATyped ⟨s, ambient, f :: rest, []⟩)
    (h : InvocationResult expected ⟨s, ambient, f :: rest, []⟩)
    (step : returnFrame ⟨s, ambient, f :: rest, []⟩ f rest = .next next) : InvocationResult expected next := by
  have values : ResultsTyped s (f.vals.map valueType) f.vals := by
    cases typed.frames with
    | cons hf _ => cases hf; assumption
  have suffix : ResultsTyped s ((f.vals.drop (f.vals.length - f.arity)).map valueType)
      (f.vals.drop (f.vals.length - f.arity)) := by
    simpa only [ResultsTyped, List.map_drop] using List.forall₂_drop (f.vals.length - f.arity) values
  simp only [returnFrame] at step
  split at step
  · rename_i valid
    rw [valid.2] at suffix
    cases rest with
    | nil =>
      simp only [AResult.next.injEq] at step
      rw [← step]
      change FramesReturn expected [f] at h
      cases h with
      | last result => simpa only [InvocationResult, result] using suffix
      | under rest => cases rest
    | cons caller callers =>
      simp only [advance, AResult.next.injEq] at step
      rw [← step]
      change FramesReturn expected (f :: caller :: callers) at h
      cases h with
      | under rest => exact FramesReturn.replace rest rfl
  · contradiction

theorem call_result {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {index : Nat} {after : List instr} {next : AState} {expected : List valtype}
    (h : InvocationResult expected ⟨s, ambient, f :: rest, []⟩)
    (step : call ⟨s, ambient, f :: rest, []⟩ f rest index after = .next next) : InvocationResult expected next := by
  simp only [call] at step
  repeat' first | split at step | contradiction
  all_goals
    simp only [AResult.next.injEq] at step
    rw [← step]
    exact FramesReturn.under (FramesReturn.replace h rfl)

/-- Signature preservation depends on the source type invariant only when the
last frame returns actual values; other steps preserve the outermost frame. -/
theorem instruction_result (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (expected : List valtype) (allowed : PureHead op)
    (typed : ATyped ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (h : InvocationResult expected ⟨s, ambient, { f with code := op :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .next next) :
    InvocationResult expected next := by
  cases allowed with
  | numeric descriptor =>
    obtain ⟨values, rfl⟩ := Numeric.astep_effect ⟨s, ambient, [], []⟩ f rest after descriptor next step
    exact advance_result h rfl rfl
  | call index => cases index with | mk_uN i => exact call_result h step
  | ret => exact return_frame_result typed h step
  | _ =>
    simp only [astep, integerBinary, branch, enterLabel] at step
    repeat' first | split at step | contradiction
    all_goals exact advance_result h step rfl

end Itasca.Runtime.SourceMachine

end

/-! ## ReferenceBounds -/

section

namespace Itasca.Runtime.SourceMachine

/-- Reference addresses carried by values fit a fixed address space. -/
def ReferenceBound (bound : Nat) : val → Prop
  | .REF_FUNC_ADDR address | .REF_HOST_ADDR address => address < bound
  | _ => True

def ValuesBound (bound : Nat) (values : List val) : Prop := ∀ value ∈ values, ReferenceBound bound value

def FrameReferencesBound (bound : Nat) (f : AFrame) : Prop :=
  ValuesBound bound f.locals ∧ ValuesBound bound f.vals

@[simp] theorem values_bound_nil (bound : Nat) : ValuesBound bound [] := by simp [ValuesBound]

@[simp] theorem values_bound_append {bound left right} :
    ValuesBound bound (left ++ right) ↔ ValuesBound bound left ∧ ValuesBound bound right := by
  simp only [ValuesBound, List.mem_append]
  constructor
  · intro h; exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨hl, hr⟩ v (hv | hv)
    · exact hl v hv
    · exact hr v hv

@[simp] theorem values_bound_cons {bound value rest} :
    ValuesBound bound (value :: rest) ↔ ReferenceBound bound value ∧ ValuesBound bound rest := by
  simp [ValuesBound]

 theorem ValuesBound.set {bound values value} (bounded : ValuesBound bound values)
    (allowed : ReferenceBound bound value) (index : Nat) : ValuesBound bound (values.set index value) := by
  induction values generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simpa using values_bound_cons.mpr ⟨allowed, (values_bound_cons.mp bounded).2⟩
    | succ index =>
      simpa using values_bound_cons.mpr ⟨(values_bound_cons.mp bounded).1, ih (values_bound_cons.mp bounded).2 index⟩

end Itasca.Runtime.SourceMachine

end

/-! ## LabelHeights -/

section

namespace Itasca.Runtime.SourceMachine

/-- Generated source typing exposes the nesting bound below every active
label. This ensures downward branch transfers preserve saved outer prefixes. -/
theorem code_stack_outer_heights {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results)
    (depth : Nat) (target : Label) (lookup : labels[depth]? = some target) :
    ∀ label ∈ labels.drop (depth + 1), label.height ≤ target.height := by
  induction h generalizing depth target with
  | outer _ => simp at lookup
  | @label label labels saved operands code results height nesting hc cont after ih =>
    cases depth with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst target
      simpa only [List.drop_succ_cons, List.drop_zero] using nesting
    | succ depth =>
      simp only [List.getElem?_cons_succ] at lookup
      simpa only [List.drop_succ_cons] using ih depth target lookup

theorem FrameTyped.outer_heights {s : store} {frame : AFrame} {incoming : List valtype}
    (typed : FrameTyped s frame incoming)
    (depth : Nat) (target : Label) (lookup : frame.labels[depth]? = some target) :
    ∀ label ∈ frame.labels.drop (depth + 1), label.height ≤ target.height := by
  cases typed with
  | mk C bindings localTypes locals values returns code wf =>
    exact code_stack_outer_heights code depth target lookup

end Itasca.Runtime.SourceMachine

end

/-! ## SupportedState -/

section

/-!
Source instruction-support certificates for active frames and stored functions. This grammar restriction is independent of runtime bytecode and concrete values.
-/

namespace Itasca.Runtime.SourceMachine

/-- Source support is independent of values and concrete bytecode emission. -/
def FrameSupported (f : AFrame) : Prop :=
  Forall BinaryInstr f.code ∧ Forall (fun label => Forall BinaryInstr label.cont ∧ Forall BinaryInstr label.after) f.labels

def FunctionsSupported (s : store) : Prop :=
  ∀ function ∈ s.FUNCS, match function.CODE with
    | .HOST _ => True
    | .FUNC _ _ body => Forall BinaryInstr body

structure SupportedState (s : AState) : Prop where
  active : Forall (FrameSupported) s.frames
  functions : FunctionsSupported s.store

theorem FunctionsSupported.same {before after : store}
    (functions : FunctionsSupported before) (same : after.FUNCS = before.FUNCS) :
    FunctionsSupported after := by simpa only [FunctionsSupported,same] using functions

theorem SupportedState.tail {before afterStore : store}
    {ambient : frame} {f : AFrame} {rest : List AFrame} {op : instr} {after : List instr}
    (covered : SupportedState ⟨before,ambient,{f with code := op::after}::rest,[]⟩)
    (same : afterStore.FUNCS = before.FUNCS) (values : List val) :
    SupportedState ⟨afterStore,ambient,{f with code := after, vals := values}::rest,[]⟩ := by
  refine ⟨?_,covered.functions.same same⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · have old := covered.active _ (List.mem_cons_self ..)
    exact ⟨fun instruction member => old.1 instruction (List.mem_cons_of_mem _ member),old.2⟩
  · exact covered.active item (List.mem_cons_of_mem _ member)

end Itasca.Runtime.SourceMachine

end

/-! ## ExecutableExclusion -/

section

namespace Itasca.Runtime.SourceMachine

/-- The two source heads added after the scalar/stateful/SIMD union. -/
def executableExtensionTag : instr → Bool
  | .SELECT (some _) | .BR_TABLE .. => true
  | _ => false

theorem PureHead.executable_extension_tag {source} (allowed : PureHead source) :
    executableExtensionTag source = false := by
  cases allowed with
  | numeric op => cases op with
    | conversion op => cases op <;> rfl
    | _ => rfl
  | _ => rfl

theorem CoreHead.executable_extension_tag {source} (allowed : CoreHead source) :
    executableExtensionTag source = false := by
  cases allowed with
  | pure h => exact h.executable_extension_tag
  | _ => rfl

theorem ScalarHead.executable_extension_tag {source} (allowed : ScalarHead source) :
    executableExtensionTag source = false := by
  cases allowed with
  | core h => exact h.executable_extension_tag
  | float op => cases op <;> rfl

theorem SimdInstr.executable_extension_tag {source} (allowed : SimdInstr source) :
    executableExtensionTag source = false := by
  have tag := allowed.source_tag
  cases source <;> simp_all [executableExtensionTag,simdSourceTag]

end Itasca.Runtime.SourceMachine

end

/-! ## StoreTyping -/

section

/-! Bridges from the source machine's component certificates to the generated
instance/store judgments. Export conditions are explicit source metadata. -/
namespace Itasca.Runtime.SourceMachine

/-- The external namespace used by the generated module-instance judgment. -/
def moduleAddresses (m : moduleinst) : List externaddr :=
  m.GLOBALS.map externaddr.GLOBAL ++ (m.MEMS.map externaddr.MEM ++
    (m.TABLES.map externaddr.TABLE ++ m.FUNCS.map externaddr.FUNC))

private theorem paired_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (paired : List.Forall₂ R xs ys) {x : α} (member : x ∈ xs) : ∃ y, R x y := by
  obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
  have other : index < ys.length := by rw [← paired.length_eq]; exact bound
  exact ⟨ys[index], paired.get bound other⟩

theorem externaddr_type_wf {s : store} {address : externaddr} {ty : externtype}
    (typed : Externaddr_ok s address ty) : wf_externtype ty := by
  cases typed <;> assumption

private theorem disjoint_of_nodup {α : Type} [BEq α] [LawfulBEq α]
    {xs : List α} (distinct : xs.Nodup) : disjoint_ α xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.nodup_cons] at distinct
    simp [disjoint_, distinct.1, ih distinct.2]

/-- Every module address denotes a source external with a type. -/
theorem ModuleBindings.address_typed {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) (storeWf : wf_store s)
    {address : externaddr} (member : address ∈ moduleAddresses m) :
    ∃ ty, Externaddr_ok s address ty := by
  simp only [moduleAddresses, List.mem_append, List.mem_map] at member
  rcases member with ⟨a, present, rfl⟩ | ⟨a, present, rfl⟩ | ⟨a, present, rfl⟩ | ⟨a, present, rfl⟩
  · obtain ⟨ty, typed⟩ := paired_left bindings.globals present
    exact ⟨.GLOBAL ty, typed⟩
  · obtain ⟨ty, typed⟩ := paired_left bindings.mems present
    exact ⟨.MEM ty, typed⟩
  · obtain ⟨ty, typed⟩ := paired_left bindings.tables present
    exact ⟨.TABLE ty, typed⟩
  · obtain ⟨ty, fn, found, same⟩ := paired_left bindings.funcs present
    refine ⟨.FUNC ty, ?_⟩
    rw [← same]
    exact .func s a fn (List.getElem?_eq_some_iff.mp found).1
      (by simp [List.getElem!_eq_getElem?_getD, found]) storeWf (.externtype_case_0 _)

/-- Export typing follows from module membership and the actual bindings. -/
theorem ModuleBindings.exports_typed {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) (storeWf : wf_store s) (moduleWf : wf_moduleinst m)
    (members : ∀ entry ∈ m.EXPORTS, entry.ADDR ∈ moduleAddresses m) :
    Forall (Exportinst_ok s) m.EXPORTS := by
  have sourceSyntax : Forall wf_exportinst m.EXPORTS := by cases moduleWf; assumption
  intro entry member
  obtain ⟨ty, typed⟩ := bindings.address_typed storeWf (members entry member)
  cases entry with
  | MKexportinst exportName address =>
    exact .mk_Exportinst_ok s exportName address ty typed storeWf (externaddr_type_wf typed) (sourceSyntax _ member)

/-- A module's checked address maps plus its export metadata recover the full
source judgment, including modules with no exports or external namespace. -/
theorem ModuleBindings.moduleinst_ok {s : store} {m : moduleinst} {C : context}
    (bindings : ModuleBindings s m C) (storeWf : wf_store s) (moduleWf : wf_moduleinst m)
    (locals : C.LOCALS = []) (labels : C.LABELS = []) (result : C.RETURN = none)
    (distinct : (m.EXPORTS.map exportinst.NAME).Nodup)
    (members : ∀ entry ∈ m.EXPORTS, entry.ADDR ∈ moduleAddresses m) :
    Moduleinst_ok s m C := by
  cases m with
  | MKmoduleinst types funcs globals tables mems elems datas exports =>
    cases C with
    | MKcontext contextTypes contextFuncs contextGlobals contextTables contextMems contextElems contextDatas contextLocals contextLabels contextReturn =>
      dsimp only at locals labels result
      subst contextLocals; subst contextLabels; subst contextReturn
      have typesEq := bindings.types
      dsimp only at typesEq
      subst contextTypes
      apply Moduleinst_ok.mk_Moduleinst_ok s types funcs globals tables mems elems datas exports
        contextFuncs contextGlobals contextTables contextMems contextElems contextDatas
      · intro ty member; cases ty with | mk_functype params results => cases params; cases results; constructor
      · exact bindings.globals.length_eq
      · exact fun _ member => List.forall₂_zip bindings.globals member
      · exact bindings.funcs.length_eq
      · intro pair member
        obtain ⟨fn, found, same⟩ := List.forall₂_zip bindings.funcs member
        rw [← same]
        exact .func s pair.1 fn (List.getElem?_eq_some_iff.mp found).1
          (by simp [List.getElem!_eq_getElem?_getD, found]) storeWf (.externtype_case_0 _)
      · exact bindings.mems.length_eq
      · exact fun _ member => List.forall₂_zip bindings.mems member
      · exact bindings.tables.length_eq
      · exact fun _ member => List.forall₂_zip bindings.tables member
      · exact bindings.exports_typed storeWf moduleWf members
      · exact bindings.datas.length_eq
      · intro address member
        obtain ⟨_, entry, found, _⟩ := paired_left bindings.datas member
        exact (List.getElem?_eq_some_iff.mp found).1
      · intro pair member
        obtain ⟨entry, found, typed⟩ := List.forall₂_zip bindings.datas member
        simpa [List.getElem!_eq_getElem?_getD, found] using typed
      · exact bindings.elems.length_eq
      · intro address member
        obtain ⟨_, entry, found, _⟩ := paired_left bindings.elems member
        exact (List.getElem?_eq_some_iff.mp found).1
      · intro pair member
        obtain ⟨entry, found, typed⟩ := List.forall₂_zip bindings.elems member
        simpa [List.getElem!_eq_getElem?_getD, found] using typed
      · simpa only [Map] using disjoint_of_nodup distinct
      · intro entry member
        have present := members entry member
        have entryWf : wf_exportinst entry := by
          have wf : Forall wf_exportinst exports := by cases moduleWf; assumption
          exact wf entry member
        apply Exportinst_in.mk_Exportinst_in
        · have positive := List.length_pos_of_mem present
          simpa only [moduleAddresses, Map, List.append_assoc] using positive
        · simpa only [moduleAddresses, Map, List.append_assoc, List.contains_iff_mem] using present
        · exact entryWf
      · exact storeWf
      · exact moduleWf
      · exact bindings.wf
      · intro ty member; constructor
      · intro ty member; constructor
      · intro ty member
        have wf : Forall wf_memtype contextMems := by cases bindings.wf; assumption
        exact .externtype_case_3 _ (wf ty member)
      · intro ty member
        have wf : Forall wf_tabletype contextTables := by cases bindings.wf; assumption
        exact .externtype_case_2 _ (wf ty member)

/-- Assemble the genuine generated store judgment from the independently
checked component and function-instance judgments. -/
theorem StoreContentsTyped.store_ok {s : store} (contents : StoreContentsTyped s)
    (storeWf : wf_store s)
    (functions : ∀ fn ∈ s.FUNCS, Funcinst_ok s fn fn.TYPE) : Store_ok s := by
  apply Store_ok.mk_Store_ok s s.GLOBALS (s.GLOBALS.map globalinst.TYPE)
    s.MEMS (s.MEMS.map meminst.TYPE) s.TABLES (s.TABLES.map tableinst.TYPE)
    s.FUNCS (s.FUNCS.map funcinst.TYPE) s.DATAS (s.DATAS.map (fun _ => datatype.OK))
    s.ELEMS (s.ELEMS.map eleminst.TYPE)
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.globals)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.memories)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.tables)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr functions)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.data)) member
  · simp
  · exact fun _ member => List.forall₂_zip
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr contents.elements)) member
  · rfl
  · exact storeWf
  · intro ty member
    obtain ⟨memory, rawMember, rfl⟩ := List.mem_map.mp member
    cases contents.memories memory rawMember <;> assumption
  · intro ty member
    obtain ⟨table, rawMember, rfl⟩ := List.mem_map.mp member
    cases contents.tables table rawMember <;> assumption
  · exact storeWf

end Itasca.Runtime.SourceMachine

end

/-! ## BrTable -/

section

namespace Itasca.Runtime.SourceMachine.BrTable
open SpecExt Itasca.Runtime.Spec

/-- The final label is used whenever the unsigned selector is out of range. -/
def select (labels : List labelidx) (fallback : labelidx) (index : Nat) : labelidx :=
  if index < labels.length then labels[index]! else fallback

theorem select_table (labels : List labelidx) (fallback : labelidx) (index : Nat) :
    (labels ++ [fallback])[Nat.min index labels.length]? = some (select labels fallback index) := by
  by_cases bound : index < labels.length
  · simp [select,bound,Nat.min_eq_left (Nat.le_of_lt bound),List.getElem?_append,bound,getElem!_pos labels index bound]
  · simp [select,bound,Nat.min_eq_right (by omega : labels.length ≤ index),List.getElem?_append]

theorem select_size (labels : List labelidx) (fallback : labelidx) (index : Nat) :
    sizeOf (select labels fallback index) ≤ sizeOf labels + sizeOf fallback := by
  unfold select
  split
  · rename_i bound
    rw [getElem!_pos labels index bound]
    have small := List.sizeOf_lt_of_mem (List.getElem_mem bound)
    omega
  · omega

theorem select_wf {labels : List labelidx} {fallback : labelidx} (index : Nat)
    (wellFormed : wf_instr (.BR_TABLE labels fallback)) : wf_uN 32 (select labels fallback index) := by
  cases wellFormed with
  | instr_case_9 _ _ listWf fallbackWf =>
    unfold select
    split
    · rename_i bound
      rw [getElem!_pos labels index bound]
      exact listWf _ (List.getElem_mem bound)
    · exact fallbackWf

/-- BR_TABLE performs one generated source step to the selected BR. The
subsequent branch transfer reuses the ordinary BR semantics. -/
theorem simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (front : List val)
    (bits : Nat) (labels : List labelidx) (fallback : labelidx)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val front)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (hb : bits < 2 ^ integerWidth .I32) (hi : wf_instr (.BR_TABLE labels fallback)) :
    StepH (decode ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) []
      (decode ⟨s,ambient,{f with code := .BR (select labels fallback bits) :: after, vals := front}::rest,[]⟩) := by
  have hbr : wf_instr (.BR (select labels fallback bits)) := .instr_case_7 _ (select_wf bits hi)
  have effect : Step_pure [admininstr_val (integerVal .I32 bits),.BR_TABLE labels fallback]
      [.BR (select labels fallback bits)] := by
    by_cases bound : bits < labels.length
    · simpa [select,bound,integerVal,admininstr_val,numtype_Inn,proj_num__0,proj_uN_0] using
        Step_pure.br_table_lt (.mk_num__0 .I32 (.mk_uN bits)) labels fallback
          (by simpa [proj_num__0,proj_uN_0] using bound) (by simp [proj_num__0])
          (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi)
          (by simpa [proj_num__0,proj_uN_0,admininstr_instr] using wf_admininstr_instr (i := .BR labels[bits]!) (by simpa only [select,if_pos bound] using hbr))
    · simpa only [select,if_neg bound,integerVal,admininstr_val,numtype_Inn] using
        Step_pure.br_table_ge (.mk_num__0 .I32 (.mk_uN bits)) labels fallback
          (by simp [proj_num__0]) (by simp [proj_num__0,proj_uN_0]; omega)
          (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi)
          (wf_admininstr_instr (i := .BR fallback) (by simpa only [select,if_neg bound] using hbr))
  simpa only [List.append_nil,List.singleton_append] using
    pure_code_simulation s ambient f rest (.BR_TABLE labels fallback)
      [.BR (select labels fallback bits)] after front [integerVal .I32 bits] [] hs ha hf hl hv hc hr heights
      (by intro v member; simp only [List.mem_singleton] at member; subst v; exact integer_val_wf .I32 bits hb)
      (forall_nil _) hi (by intro i member; simp only [List.mem_singleton] at member; subst i; exact hbr) effect

/-- Generated BR_TABLE typing makes every selectable target accept the actual
branch-value suffix, including bottom-type subtyping elimination. -/
theorem frame_preservation {s : store} {f : AFrame} {after : List instr}
    {frontValues : List val} {bits : Nat} {labels : List labelidx} {fallback : labelidx}
    (typed : FrameTyped s {f with code := .BR_TABLE labels fallback :: after, vals := frontValues ++ [integerVal .I32 bits]} []) :
    FrameTyped s {f with code := .BR (select labels fallback bits) :: after, vals := frontValues} [] := by
  cases typed with
  | mk C bindings localTypes locals values returns code frameWf =>
    simp only [List.append_nil] at code
    obtain ⟨front,ins,outs,head,stack,tail,heights⟩ :=
      code_stack_after_bounds (value_types_concrete (frontValues ++ [integerVal .I32 bits])) code
    cases head with
    | br_table _ _ _ discarded branchTypes outputs targetBounds targetTypes defaultBound defaultTypes contextWf instructionWf =>
      have base : frontValues.map valueType = front ++ (discarded ++ branchTypes) := by
        simpa only [List.map_append,List.map_cons,List.map_nil,integerVal,valueType,
          numtype_Inn,valtype_numtype,← List.append_assoc,List.append_cancel_right_eq] using stack
      have concrete : Forall (fun ty => ty ≠ valtype.BOT) branchTypes := by
        intro ty member
        apply value_types_concrete frontValues ty
        rw [base]
        simp only [List.mem_append]
        exact Or.inr (Or.inr member)
      have selectedBound : proj_uN_0 (select labels fallback bits) < (labelContext C f.labels).LABELS.length := by
        unfold select
        split
        · rename_i bound
          rw [getElem!_pos labels bits bound]
          exact targetBounds _ (List.getElem_mem bound)
        · exact defaultBound
      have selectedTypes : proj_list_0 valtype ((labelContext C f.labels).LABELS[proj_uN_0 (select labels fallback bits)]!) = branchTypes := by
        have subtype : Resulttype_sub (.mk_list branchTypes)
            ((labelContext C f.labels).LABELS[proj_uN_0 (select labels fallback bits)]!) := by
          unfold select
          split
          · rename_i bound
            rw [getElem!_pos labels bits bound]
            exact targetTypes _ (List.getElem_mem bound)
          · exact defaultTypes
        generalize (labelContext C f.labels).LABELS[proj_uN_0 (select labels fallback bits)]! = actual at subtype ⊢
        cases actual with
        | mk_list actual => exact (concrete_result_sub_eq concrete subtype).symm
      have selectedWf : wf_instr (.BR (select labels fallback bits)) := .instr_case_7 _ (select_wf bits instructionWf)
      have head' := Instr_ok.br (labelContext C f.labels) (select labels fallback bits)
        discarded branchTypes outs selectedBound selectedTypes contextWf selectedWf
      have retained : ResultsTyped s (frontValues.map valueType) frontValues := by
        simpa using results_typed_take frontValues.length values
      apply FrameTyped.mk (f := {f with code := .BR (select labels fallback bits) :: after, vals := frontValues})
        C bindings localTypes locals retained returns ?_ frameWf
      simpa only [List.append_nil,base] using code_stack_prepend head' selectedWf heights tail

theorem correct (s : store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (front : List val) (bits : Nat) (labels : List labelidx) (fallback : labelidx)
    (bound : bits < 2^32)
    (typed : ATyped ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩) :
    ATyped ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ ∧
    NextSim ⟨s,ambient,{f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]}::rest,[]⟩
      ⟨s,ambient,{f with code := .BR (select labels fallback bits)::after,vals := front}::rest,[]⟩ := by
  have frameTyped : FrameTyped s {f with code := .BR_TABLE labels fallback :: after, vals := front ++ [integerVal .I32 bits]} [] := by
    cases typed.frames with | cons head _ => exact head
  have restWf : Forall FrameWf rest := by
    cases typed.frames with | cons _ tail => exact frames_typed_wf tail
  obtain ⟨frameWf,labelsWf,valuesWf,codeWf⟩ := frame_typed_wf frameTyped
  have afterWf : Forall wf_instr after := fun i member => codeWf i (List.mem_cons_of_mem _ member)
  have opWf := codeWf (.BR_TABLE labels fallback) (List.mem_cons_self ..)
  have frontWf : Forall wf_val front := fun v member => valuesWf v (List.mem_append_left _ member)
  have heights : ∀ label ∈ f.labels, label.height ≤ front.length := by
    obtain ⟨C,first,operands,ins,outs,bindings,locals,head,split,operandTypes,firstWf,bounds⟩ := frame_typed_operands_bounds (f := {f with vals := front ++ [integerVal .I32 bits]}) frameTyped
    cases head with
    | br_table =>
      have sizes := congrArg List.length split
      have operandSizes := operandTypes.length_eq
      simp only [List.length_append,List.length_singleton] at sizes operandSizes
      intro label member
      have small := bounds label member
      omega
  exact ⟨active_frame_preservation typed (frame_preservation frameTyped) rfl,
    NextSim.single (simulation s ambient f rest after front bits labels fallback typed.store typed.ambient
      frameWf labelsWf frontWf afterWf restWf heights bound opWf)⟩

theorem operands {s : store} {f : AFrame} {after : List instr}
    {labels : List labelidx} {fallback : labelidx}
    (typed : FrameTyped s {f with code := .BR_TABLE labels fallback :: after} []) :
    ∃ front bits, f.vals = front ++ [integerVal .I32 bits] ∧ bits < 2^32 := by
  obtain ⟨C,first,operands,ins,outs,bindings,locals,head,split,operandTypes⟩ := frame_typed_operands typed
  cases head with
  | br_table =>
    obtain ⟨discarded,remaining,rfl,_,remainingTyped⟩ := results_typed_split operandTypes
    obtain ⟨arguments,selector,rfl,_,selectorTyped⟩ := results_typed_split remainingTyped
    cases selectorTyped with
    | cons value empty =>
      cases empty
      obtain ⟨bits,rfl,bound⟩ := integer_val_inv (ty := .I32) value
      refine ⟨first ++ discarded ++ arguments,bits,?_,bound⟩
      simpa only [List.append_assoc] using split

end Itasca.Runtime.SourceMachine.BrTable

end
