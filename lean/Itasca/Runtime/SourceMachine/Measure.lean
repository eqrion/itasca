import Itasca.Runtime.SourceMachine.Simd.Source
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Stateful.Descriptor
import Itasca.Runtime.SourceMachine.Memory.Decode
import Itasca.Runtime.SourceMachine.Numeric.Semantics
import Itasca.Runtime.SourceMachine.Typing
import Itasca.Runtime.Spec.Integer
import Mathlib.Tactic

/-!
Sections, each formerly its own module: BinaryInstr, PureHead, Core, Safety, ModuleBindingsExtension, FrameTypingExtension, Measure.
-/

/-! ## BinaryInstr -/

section

/-!
# Binary instructions

`BinaryInstr` is the source syntax a decoded binary function body can contain: every
Wasm 2.0 instruction except the administrative forms. `Code/Local/Source/SourceExecutable`
proves that each decoded body satisfies it. It is an internal store invariant, never a
premise of a headline theorem.
-/

namespace Itasca.Runtime.SourceMachine

inductive BinaryInstr : instr → Prop where
  | nop : BinaryInstr .NOP
  | unreachable : BinaryInstr .UNREACHABLE
  | drop : BinaryInstr .DROP
  | const (ty : numtype) (value : num_) : BinaryInstr (.CONST ty value)
  | numeric (op : Numeric.Instruction) : BinaryInstr op.source
  | float (op : Float.Instruction) : BinaryInstr op.source
  | select : BinaryInstr (.SELECT none)
  | typed_select (ty : valtype) : BinaryInstr (.SELECT (some [ty]))
  | local_get (index : idx) : BinaryInstr (.LOCAL_GET index)
  | local_set (index : idx) : BinaryInstr (.LOCAL_SET index)
  | local_tee (index : idx) : BinaryInstr (.LOCAL_TEE index)
  | global_get (index : idx) : BinaryInstr (.GLOBAL_GET index)
  | global_set (index : idx) : BinaryInstr (.GLOBAL_SET index)
  | load (op : Memory.Load) (argument : memarg) : BinaryInstr (op.source argument)
  | store (op : Memory.Store) (argument : memarg) : BinaryInstr (op.source argument)
  | stateful (op : Stateful.Instruction) : BinaryInstr op.source
  | simd {source} : SimdInstr source → BinaryInstr source
  | block (ty : blocktype) (body : List instr) : Forall BinaryInstr body → BinaryInstr (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) : Forall BinaryInstr body → BinaryInstr (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) :
      Forall BinaryInstr yes → Forall BinaryInstr no → BinaryInstr (.IFELSE ty yes no)
  | br (depth : labelidx) : BinaryInstr (.BR depth)
  | br_if (depth : labelidx) : BinaryInstr (.BR_IF depth)
  | br_table (labels : List labelidx) (fallback : labelidx) : BinaryInstr (.BR_TABLE labels fallback)
  | call (index : funcidx) : BinaryInstr (.CALL index)
  | call_indirect (table : tableidx) (type : typeidx) : BinaryInstr (.CALL_INDIRECT table type)
  | ret : BinaryInstr .RETURN

/-- Structured control is never the source of an operation descriptor. -/
def structuredTag : instr → Bool
  | .BLOCK .. | .LOOP .. | .IFELSE .. => true
  | _ => false

private theorem numeric_unstructured (op : Numeric.Instruction) : structuredTag op.source = false := by
  cases op with
  | conversion op => cases op <;> rfl
  | _ => rfl

private theorem float_unstructured (op : Float.Instruction) : structuredTag op.source = false := by
  cases op <;> rfl

private theorem stateful_unstructured (op : Stateful.Instruction) : structuredTag op.source = false := by
  cases op <;> rfl

private theorem simd_unstructured {source} (simd : SimdInstr source) : structuredTag source = false := by
  cases simd with
  | pure signature => cases signature <;> rfl
  | constant => rfl
  | memory signature => cases signature <;> rfl

theorem BinaryInstr.block_body {ty body} (allowed : BinaryInstr (.BLOCK ty body)) :
    Forall BinaryInstr body := by
  generalize equal : instr.BLOCK ty body = source at allowed
  cases allowed with
  | block _ _ body => cases equal; exact body
  | numeric op => have tag := numeric_unstructured op; rw [← equal] at tag; cases tag
  | float op => have tag := float_unstructured op; rw [← equal] at tag; cases tag
  | stateful op => have tag := stateful_unstructured op; rw [← equal] at tag; cases tag
  | simd simd => have tag := simd_unstructured simd; rw [← equal] at tag; cases tag
  | _ => cases equal

theorem BinaryInstr.loop_body {ty body} (allowed : BinaryInstr (.LOOP ty body)) :
    Forall BinaryInstr body := by
  generalize equal : instr.LOOP ty body = source at allowed
  cases allowed with
  | loop _ _ body => cases equal; exact body
  | numeric op => have tag := numeric_unstructured op; rw [← equal] at tag; cases tag
  | float op => have tag := float_unstructured op; rw [← equal] at tag; cases tag
  | stateful op => have tag := stateful_unstructured op; rw [← equal] at tag; cases tag
  | simd simd => have tag := simd_unstructured simd; rw [← equal] at tag; cases tag
  | _ => cases equal

theorem BinaryInstr.if_bodies {ty yes no} (allowed : BinaryInstr (.IFELSE ty yes no)) :
    Forall BinaryInstr yes ∧ Forall BinaryInstr no := by
  generalize equal : instr.IFELSE ty yes no = source at allowed
  cases allowed with
  | ifelse _ _ _ yes no => cases equal; exact ⟨yes,no⟩
  | numeric op => have tag := numeric_unstructured op; rw [← equal] at tag; cases tag
  | float op => have tag := float_unstructured op; rw [← equal] at tag; cases tag
  | stateful op => have tag := stateful_unstructured op; rw [← equal] at tag; cases tag
  | simd simd => have tag := simd_unstructured simd; rw [← equal] at tag; cases tag
  | _ => cases equal

end Itasca.Runtime.SourceMachine

end

/-! ## PureHead -/

section

namespace Itasca.Runtime.SourceMachine

/-- Source heads executed by `astep`, which never changes the store. -/
inductive PureHead : instr → Prop where
  | numeric (op : Numeric.Instruction) : PureHead op.source
  | nop : PureHead .NOP
  | unreachable : PureHead .UNREACHABLE
  | drop : PureHead .DROP
  | const (ty : Inn) (value : iN) :
      PureHead (.CONST (numtype_Inn ty) (.mk_num__0 ty value))
  | local_get (index : idx) : PureHead (.LOCAL_GET index)
  | local_set (index : idx) : PureHead (.LOCAL_SET index)
  | local_tee (index : idx) : PureHead (.LOCAL_TEE index)
  | block (ty : blocktype) (body : List instr) : PureHead (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) : PureHead (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) : PureHead (.IFELSE ty yes no)
  | br (depth : labelidx) : PureHead (.BR depth)
  | br_if (depth : labelidx) : PureHead (.BR_IF depth)
  | call (index : funcidx) : PureHead (.CALL index)
  | ret : PureHead .RETURN

end Itasca.Runtime.SourceMachine

end

/-! ## Core -/

section

/-!
The core source-instruction grammar and its state predicates. Extended operation families preserve this explicit grammar boundary rather than treating core as a historical proof version.
-/

namespace Itasca.Runtime.SourceMachine

/-- Source heads executed by `Core.instruction`: the `astep` heads, plus constants,
select and the global and memory accesses it resolves against the store. -/
inductive CoreHead : instr → Prop where
  | pure {source} : PureHead source → CoreHead source
  | const (ty : numtype) (value : num_) : CoreHead (.CONST ty value)
  | select : CoreHead (.SELECT none)
  | global_get (index : idx) : CoreHead (.GLOBAL_GET index)
  | global_set (index : idx) : CoreHead (.GLOBAL_SET index)
  | load (op : Memory.Load) (argument : memarg) : CoreHead (op.source argument)
  | store (op : Memory.Store) (argument : memarg) : CoreHead (op.source argument)

/-- Source heads lowered by the scalar emitter: `CoreHead` and scalar float operations. -/
inductive ScalarHead : instr → Prop where
  | core {source} : CoreHead source → ScalarHead source
  | float (op : Float.Instruction) : ScalarHead op.source

end Itasca.Runtime.SourceMachine

end

/-! ## Safety -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt
open Itasca.DeclarativeComplete

/-- Removing nop preserves the generated source typing judgment, including
arbitrary framing and bottom subtyping in the original derivation. -/
theorem nop_typing_tail {C : context} {before after : List valtype} {code : List instr}
    (h : Instrs_ok C (.NOP :: code) ⟨.mk_list before, .mk_list after⟩) :
    Instrs_ok C code ⟨.mk_list before, .mk_list after⟩ := by
  obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal h
  cases hop
  simpa using narrow_input hrest hin

theorem nop_code_preservation {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack (.NOP :: code) results) :
    CodeStackTyped C labels stack code results := by
  cases h with
  | outer hc => exact .outer (nop_typing_tail hc)
  | label height nesting hc cont rest => exact .label height nesting (nop_typing_tail hc) cont rest

theorem nop_frame_preservation {s : store} {f : AFrame} {incoming : List valtype}
    {code : List instr} (h : FrameTyped s { f with code := .NOP :: code } incoming) :
    FrameTyped s { f with code := code } incoming := by
  cases h with
  | mk C bindings localTypes locals values returns codeTyped hw =>
    exact .mk C bindings localTypes locals values returns (nop_code_preservation codeTyped) hw

/-- The nop case of abstract-machine preservation is proved from source typing. -/
theorem nop_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (results : List val)
    (h : ATyped ⟨s, ambient, { f with code := .NOP :: code } :: rest, results⟩) :
    ATyped ⟨s, ambient, { f with code := code } :: rest, results⟩ := by
  obtain ⟨hs, functions, ha, frames, values, active, heights⟩ := h
  cases frames with
  | cons hf hr =>
    exact ⟨hs, functions, ha, .cons (nop_frame_preservation hf) hr, values, (fun _ => active (by simp)),
      replace_frame_heights heights (frame_typed_heights (nop_frame_preservation hf))⟩

@[simp] theorem pop_append (values : List val) (value : val) :
    pop (values ++ [value]) = some (values, value) := by
  simp [pop]

theorem const_typing_tail {C : context} {before after : List valtype} {code : List instr}
    {ty : numtype} {value : num_}
    (h : Instrs_ok C (.CONST ty value :: code) ⟨.mk_list before, .mk_list after⟩) :
    Instrs_ok C code ⟨.mk_list (before ++ [valtype_numtype ty]), .mk_list after⟩ := by
  obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal h
  cases hop
  apply narrow_input hrest
  simpa using result_sub_append hin (result_sub_refl [valtype_numtype ty])

theorem const_code_preservation {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr} {ty : numtype} {value : num_}
    (h : CodeStackTyped C labels stack (.CONST ty value :: code) results) :
    CodeStackTyped C labels (stack ++ [valtype_numtype ty]) code results := by
  cases h with
  | outer hc => exact .outer (const_typing_tail hc)
  | @label label labels saved operands _ _ height nesting hc cont rest =>
    simpa only [List.append_assoc] using
      (CodeStackTyped.label height nesting (const_typing_tail hc) cont rest)

theorem code_stack_wf {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results) : Forall wf_instr code := by
  cases h with
  | outer hc => exact (wellFormed hc).2
  | label _ _ hc _ _ => exact (wellFormed hc).2

theorem const_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {ty : numtype} {value : num_} (hs : wf_store s)
    (h : FrameTyped s { f with code := .CONST ty value :: code } []) :
    FrameTyped s { f with code := code, vals := f.vals ++ [.CONST ty value] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns codeTyped hw =>
    have hconst := code_stack_wf codeTyped (.CONST ty value) (by simp)
    cases hconst with
    | instr_case_13 _ _ hnum =>
      have hval : Val_ok s (.CONST ty value) (valtype_numtype ty) :=
        .numtype _ _ _ hs (.val_case_0 _ _ hnum)
      apply FrameTyped.mk (f := { f with code := code, vals := f.vals ++ [.CONST ty value] })
        (incoming := []) C bindings localTypes locals ?_ returns ?_ hw
      · simpa [List.map_append, valueType, ResultsTyped] using
          (List.rel_append values (List.Forall₂.cons hval List.Forall₂.nil))
      · simpa [List.map_append, valueType, ResultsTyped] using const_code_preservation codeTyped

theorem const_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (ty : numtype) (value : num_)
    (results : List val)
    (h : ATyped ⟨s, ambient, { f with code := .CONST ty value :: code } :: rest, results⟩) :
    ATyped ⟨s, ambient,
      { f with code := code, vals := f.vals ++ [.CONST ty value] } :: rest, results⟩ := by
  obtain ⟨hs, functions, ha, frames, values, active, heights⟩ := h
  cases frames with
  | cons hf hr =>
    exact ⟨hs, functions, ha, .cons (const_frame_preservation hs hf) hr,
      values, (fun _ => active (by simp)),
      replace_frame_heights heights (frame_typed_heights (const_frame_preservation hs hf))⟩

theorem code_stack_head {C : context} {labels : List Label}
    {stack results : List valtype} {op : instr} {code : List instr}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack (op :: code) results) :
    ∃ front ins outs,
      Instr_ok (labelContext C labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      stack = front ++ ins := by
  cases h with
  | outer hc =>
    obtain ⟨front, ins, outs, hop, hin, _⟩ := head_normal hc
    exact ⟨front, ins, outs, hop, concrete_result_sub_eq concrete hin⟩
  | @label label labels saved operands _ _ _ _ hc _ _ =>
    obtain ⟨front, ins, outs, hop, hin, _⟩ := head_normal hc
    have cop : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right _ hty)
    have heq := concrete_result_sub_eq cop hin
    exact ⟨saved ++ front, ins, outs, hop, by simp only [heq, List.append_assoc]⟩

theorem results_typed_split {s : store} {before after : List valtype} {values : List val}
    (h : ResultsTyped s (before ++ after) values) :
    ∃ first last, values = first ++ last ∧
      ResultsTyped s before first ∧ ResultsTyped s after last := by
  induction before generalizing values with
  | nil => exact ⟨[], values, rfl, .nil, h⟩
  | cons ty before ih =>
    cases h with
    | cons hv hs =>
      obtain ⟨first, last, rfl, hf, hl⟩ := ih hs
      exact ⟨_ :: first, last, rfl, .cons hv hf, hl⟩

/-- Inverting source typing yields actual operands of the instruction's declared
input types, with no bottom values or stack-polymorphic witness assumptions. -/
theorem frame_typed_operands {s : store} {f : AFrame} {op : instr} {code : List instr}
    (h : FrameTyped s { f with code := op :: code } []) :
    ∃ C first operands ins outs,
      ModuleBindings s f.module C ∧ C.LOCALS = f.locals.map valueType ∧
      Instr_ok (labelContext C f.labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      f.vals = first ++ operands ∧ ResultsTyped s ins operands := by
  cases h with
  | mk C bindings locals hlocals values returns hc hw =>
    have concrete : Forall (fun ty => ty ≠ valtype.BOT) (f.vals.map valueType) := by
      intro ty hty
      obtain ⟨value, _, rfl⟩ := List.mem_map.mp hty
      exact value_type_ne_bot value
    have hc' : CodeStackTyped C f.labels (f.vals.map valueType) (op :: code) f.resultTypes := by
      simpa only [List.append_nil] using hc
    obtain ⟨front, ins, outs, hop, heq⟩ := code_stack_head concrete hc'
    have values' : ResultsTyped s (front ++ ins) f.vals := by rw [← heq]; exact values
    obtain ⟨first, operands, hsplit, _, hoperands⟩ := results_typed_split values'
    exact ⟨C, first, operands, ins, outs, bindings, locals, hop, hsplit, hoperands⟩

/-- Every saved label lies below the primitive instruction's operands. This
strengthens stack inversion with the absolute heights needed by branches. -/
theorem code_stack_head_bounds {C : context} {labels : List Label}
    {stack results : List valtype} {op : instr} {code : List instr}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack (op :: code) results) :
    ∃ front ins outs,
      Instr_ok (labelContext C labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      stack = front ++ ins ∧ (∀ label ∈ labels, label.height ≤ front.length) := by
  cases h with
  | outer hc =>
    obtain ⟨front, ins, outs, hop, hin, _⟩ := head_normal hc
    exact ⟨front, ins, outs, hop, concrete_result_sub_eq concrete hin, by simp⟩
  | @label label labels saved operands _ _ height nesting hc _ _ =>
    obtain ⟨front, ins, outs, hop, hin, _⟩ := head_normal hc
    have cop : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right _ hty)
    have heq := concrete_result_sub_eq cop hin
    refine ⟨saved ++ front, ins, outs, hop, by simp only [heq, List.append_assoc], ?_⟩
    intro target ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp only [List.length_append, height]; omega
    · have hh := nesting target ht
      simp only [List.length_append, height]; omega

/-- Normalizing the first generated typing rule also retains the typed
continuation after replacing its operand suffix by the declared outputs. -/
theorem code_stack_after {C : context} {labels : List Label}
    {stack results : List valtype} {op : instr} {code : List instr}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack (op :: code) results) :
    ∃ front ins outs,
      Instr_ok (labelContext C labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      stack = front ++ ins ∧ CodeStackTyped C labels (front ++ outs) code results := by
  cases h with
  | outer hc =>
    obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal hc
    exact ⟨front, ins, outs, hop, concrete_result_sub_eq concrete hin, .outer hrest⟩
  | @label label labels saved operands _ _ height nesting hc cont rest =>
    obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal hc
    have cop : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right _ hty)
    have heq := concrete_result_sub_eq cop hin
    exact ⟨saved ++ front, ins, outs, hop,
      by simp only [heq, List.append_assoc],
      by simpa only [List.append_assoc] using CodeStackTyped.label height nesting hrest cont rest⟩

theorem results_typed_take {s : store} {values : List val} (n : Nat)
    (h : ResultsTyped s (values.map valueType) values) :
    ResultsTyped s ((values.take n).map valueType) (values.take n) := by
  simpa only [ResultsTyped, List.map_take] using List.forall₂_take n h

theorem code_stack_after_bounds {C : context} {labels : List Label}
    {stack results : List valtype} {op : instr} {code : List instr}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack (op :: code) results) :
    ∃ front ins outs,
      Instr_ok (labelContext C labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      stack = front ++ ins ∧ CodeStackTyped C labels (front ++ outs) code results ∧
      (∀ label ∈ labels, label.height ≤ front.length) := by
  cases h with
  | outer hc =>
    obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal hc
    exact ⟨front, ins, outs, hop, concrete_result_sub_eq concrete hin, .outer hrest, by simp⟩
  | @label label labels saved operands _ _ height nesting hc cont rest =>
    obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal hc
    have cop : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right _ hty)
    have heq := concrete_result_sub_eq cop hin
    refine ⟨saved ++ front, ins, outs, hop,
      by simp only [heq, List.append_assoc],
      by simpa only [List.append_assoc] using CodeStackTyped.label height nesting hrest cont rest, ?_⟩
    intro target ht
    rcases List.mem_cons.mp ht with rfl | ht
    · simp only [List.length_append, height]; omega
    · have hh := nesting target ht
      simp only [List.length_append, height]; omega

end Itasca.Runtime.SourceMachine

end

/-! ## ModuleBindingsExtension -/

section

namespace Itasca.Runtime.SourceMachine

/-- Module bindings survive specification store extension, including growth,
content writes, and dropping segments. -/
theorem ModuleBindings.extend {s t : store} {module : moduleinst} {C : context}
    (bindings : ModuleBindings s module C) (extension : Extend_store s t) :
    ModuleBindings t module C := by
  refine ⟨bindings.types, ?_, ?_, ?_, ?_, ?_, ?_, bindings.wf⟩
  · apply bindings.funcs.imp
    rintro address ty ⟨fn, found, typed⟩
    exact ⟨fn, Spec.function_lookup_extend extension found, typed⟩
  · exact bindings.globals.imp (fun _ _ typed => Spec.externaddr_ok_extend extension typed)
  · exact bindings.tables.imp (fun _ _ typed => Spec.externaddr_ok_extend extension typed)
  · exact bindings.mems.imp (fun _ _ typed => Spec.externaddr_ok_extend extension typed)
  · apply bindings.elems.imp
    rintro address ty ⟨entry, found, typed⟩
    exact Spec.element_lookup_extend extension found typed
  · apply bindings.datas.imp
    rintro address ty ⟨entry, found, typed⟩
    exact Spec.data_lookup_extend extension found typed

/-- Existing function bodies keep their source typing under store extension.
New function bodies are certified independently when they are published. -/
theorem FunctionsTyped.extend_old {s t : store} (functions : FunctionsTyped s)
    (extension : Extend_store s t) (fn : funcinst) (member : fn ∈ s.FUNCS) :
    match fn.CODE with
    | .HOST _ => Functype_ok fn.TYPE
    | .FUNC index locals body => ∃ C, ModuleBindings t fn.MODULE C ∧
        C.LOCALS = [] ∧ C.LABELS = [] ∧ C.RETURN = none ∧
        Func_ok C (.FUNC index locals body) fn.TYPE := by
  have typed := functions fn member
  cases code : fn.CODE with
  | HOST identity => simpa only [code] using typed
  | FUNC index locals body =>
    simp only [code] at typed ⊢
    obtain ⟨C, bindings, locals, labels, returns, body⟩ := typed
    exact ⟨C, bindings.extend extension, locals, labels, returns, body⟩

/-- A store update that adds no functions preserves all function typing. -/
theorem FunctionsTyped.extend_same {s t : store} (functions : FunctionsTyped s)
    (extension : Extend_store s t) (same : t.FUNCS = s.FUNCS) : FunctionsTyped t := by
  intro fn member
  exact functions.extend_old extension fn (same ▸ member)
end Itasca.Runtime.SourceMachine

end

/-! ## FrameTypingExtension -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- Store extension preserves the type of every existing operand/reference. -/
theorem val_typed_extend {before after : store} (extension : Extend_store before after)
    {value : val} {ty : valtype} (typed : Val_ok before value ty) : Val_ok after value ty := by
  have fresh := (extend_store_wf extension).2
  cases typed with
  | numtype ty bits _ wf => exact .numtype after ty bits fresh wf
  | vectype ty bits _ wf => exact .vectype after ty bits fresh wf
  | reftype value ty reference _ => exact .reftype after value ty (ref_ok_extend extension reference) fresh

theorem results_typed_extend {before after : store} (extension : Extend_store before after)
    {types : List valtype} {values : List val} (typed : ResultsTyped before types values) :
    ResultsTyped after types values := typed.imp (fun _ _ value => val_typed_extend extension value)

theorem FrameTyped.extend {before after : store} (extension : Extend_store before after)
    {frame incoming} (typed : FrameTyped before frame incoming) : FrameTyped after frame incoming := by
  cases typed with
  | mk context bindings locals localTypes values result code wf =>
    exact .mk context (bindings.extend extension) locals (results_typed_extend extension localTypes)
      (results_typed_extend extension values) result code wf

theorem FramesTyped.extend {before after : store} (extension : Extend_store before after)
    {frames incoming} (typed : FramesTyped before frames incoming) : FramesTyped after frames incoming := by
  induction typed with
  | nil results => exact .nil results
  | cons frame rest ih => exact .cons (frame.extend extension) ih

/-- Content updates preserve the complete abstract typing invariant. Adding
functions requires a separate typing attachment for those new bodies. -/
theorem ATyped.extend_same {state : AState} {after : _root_.store}
    (typed : ATyped state) (extension : Extend_store state.store after)
    (functions : after.FUNCS = state.store.FUNCS) : ATyped {state with store := after} :=
  ⟨(extend_store_wf extension).2, typed.functions.extend_same extension functions,
    typed.ambient, typed.frames.extend extension, typed.results, typed.activeResults, typed.heights⟩
end Itasca.Runtime.SourceMachine

end

/-! ## Measure -/

section

/-!
The pending-instruction measure for administrative constant moves. Absorbing a constant strictly decreases this measure without constraining callers or value sizes.
-/

namespace Itasca.Runtime.SourceMachine

/-- Pending instructions in the active frame. Suspended callers do not affect
the bound on consecutive administrative constant moves; real steps may reset it. -/
def administrativeMeasure (s : AState) : Nat :=
  match s.frames with
  | [] => 0
  | f :: _ => f.code.length

/-- Absorbing one constant into the operand stack strictly decreases the
administrative measure, independently of labels, callers, and value sizes. -/
theorem const_measure_decreases (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (ty : numtype) (value : num_) (after : List instr) :
    administrativeMeasure ⟨s, ambient,
      { f with code := after, vals := f.vals ++ [.CONST ty value] } :: rest, []⟩ <
    administrativeMeasure ⟨s, ambient,
      { f with code := .CONST ty value :: after } :: rest, []⟩ := by
  simp [administrativeMeasure]

end Itasca.Runtime.SourceMachine

end
