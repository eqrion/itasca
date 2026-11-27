import Itasca.Runtime.SourceMachine.Simulation
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Spec.Typing
import Itasca.Runtime.Spec.PrimitiveOperations

open WebAssembly

/-!
Proofs for Runtime / SourceMachine.

This module collects Typing, MemoryDecoding.
Each section documents its contracts and consumers.
-/

/-! ## Typing -/

section

/-! ## Step -/

section

/-! Executable abstract transition for the integer vertical slice. Other
instruction families return `stuck` until their transition cases are added;
no total-Wasm progress claim is made by this definition. -/

namespace Itasca.SourceMachine

/-- Remove the top value while retaining bottom-to-top stack order. -/
def pop (values : List val) : Option (List val × val) :=
  match values.reverse with
  | [] => none
  | value :: rest => some (rest.reverse, value)

/-- Numeric tags are checked in addition to their enclosing value tag. -/
def integer (ty : numtype) : val → Option Nat
  | .CONST ty' (.mk_num__0 ity (.mk_uN bits)) =>
      if ty = ty' ∧ ty = numtype_Inn ity ∧ bits < 2 ^ (if ty = .I32 then 32 else 64)
      then some bits else none
  | _ => none

def advance (s : AState) (f : AFrame) (rest : List AFrame) : AResult :=
  .next { s with frames := f :: rest }

namespace Numeric

/-- Finish one well-tagged integer operation, preserving all non-stack fields. -/
def finish (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (front : List val) (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) : AResult :=
  match op.apply a b with
  | none => .trap
  | some result => advance s
      { f with code := after, vals := front ++ [integerVal op.output result.toNat] } rest

/-- Checked stack decoding for every scalar integer descriptor. -/
def transition (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Instruction) : AResult :=
  match pop f.vals with
  | none => .stuck
  | some (front, right) =>
    match integer (numtype_Inn op.input) right with
    | none => .stuck
    | some rightBits =>
      let b := BitVec.ofNat (sizenn (numtype_Inn op.input)) rightBits
      if op.arity = 1 then finish s f rest after front op b b else
      match pop front with
      | none => .stuck
      | some (front, left) =>
        match integer (numtype_Inn op.input) left with
        | none => .stuck
        | some leftBits => finish s f rest after front op
            (BitVec.ofNat (sizenn (numtype_Inn op.input)) leftBits) b

end Numeric

/-- All callers of this helper have already checked operand widths. -/
def integerBinary (op : binop_Inn) (width a b : Nat) : Option Nat :=
  match op with
  | .ADD => some ((a + b) % 2 ^ width)
  | .SUB => some ((a + 2 ^ width - b) % 2 ^ width)
  | _ => none

def blockType (m : moduleinst) : blocktype → Option functype
  | ._RESULT none => some ⟨.mk_list [], .mk_list []⟩
  | ._RESULT (some ty) => some ⟨.mk_list [], .mk_list [ty]⟩
  | ._IDX (.mk_uN i) => m.TYPES[i]?

/-- A branch exits the target label. A loop's continuation re-enters its loop. -/
def branch (s : AState) (f : AFrame) (rest : List AFrame) (depth : Nat) : AResult :=
  match f.labels[depth]? with
  | none => .stuck
  | some target =>
    if target.height + target.arity ≤ f.vals.length ∧
        (f.vals.drop (f.vals.length - target.arity)).map valueType = target.branchTypes then
      advance s { f with vals := f.vals.take target.height ++ f.vals.drop (f.vals.length - target.arity), labels := f.labels.drop (depth + 1), code := target.cont ++ target.after } rest
    else .stuck

def enterLabel (s : AState) (f : AFrame) (rest : List AFrame)
    (bt : blocktype) (body after : List instr) (loop : Bool) : AResult :=
  match blockType f.module bt with
  | none => .stuck
  | some ⟨.mk_list params, .mk_list results⟩ =>
    if params.length ≤ f.vals.length ∧
        (f.vals.drop (f.vals.length - params.length)).map valueType = params then
      let label : Label := {
        branchTypes := if loop then params else results
        resultTypes := results
        cont := if loop then [.LOOP bt body] else []
        height := f.vals.length - params.length
        after := after }
      advance s { f with code := body, labels := label :: f.labels } rest
    else .stuck

/-- Return discards labels and passes only the declared number of results. -/
def returnFrame (s : AState) (f : AFrame) (rest : List AFrame) : AResult :=
  if f.arity ≤ f.vals.length ∧
      (f.vals.drop (f.vals.length - f.arity)).map valueType = f.resultTypes then
    let results := f.vals.drop (f.vals.length - f.arity)
    match rest with
    | [] => .next { s with frames := [], results := results }
    | caller :: callers => advance s { caller with vals := caller.vals ++ results } callers
  else .stuck

def astep (s : AState) : AResult :=
  match s.frames with
  | [] => .done s.results
  | f :: rest =>
    match f.code with
    | [] =>
      match f.labels with
      | [] => returnFrame s f rest
      | label :: labels =>
        if f.vals.length = label.height + label.resultTypes.length ∧
            (f.vals.drop label.height).map valueType = label.resultTypes then
          advance s { f with labels := labels, code := label.after } rest
        else .stuck
    | instruction :: after =>
      match instruction with
      | .NOP => advance s { f with code := after } rest
      | .UNREACHABLE => .trap
      | .CONST ty value =>
        match integer ty (.CONST ty value) with
        | some _ => advance s { f with code := after, vals := f.vals ++ [.CONST ty value] } rest
        | none => .stuck
      | .DROP =>
        match pop f.vals with
        | none => .stuck
        | some (values, _) => advance s { f with code := after, vals := values } rest
      | .LOCAL_GET (.mk_uN i) =>
        match f.locals[i]? with
        | none => .stuck
        | some value => advance s { f with code := after, vals := f.vals ++ [value] } rest
      | .LOCAL_SET (.mk_uN i) | .LOCAL_TEE (.mk_uN i) =>
        match pop f.vals, f.locals[i]? with
        | some (values, value), some old =>
          if valueType value = valueType old then
            advance s { f with code := after, locals := f.locals.set i value, vals := if instruction = .LOCAL_SET (.mk_uN i) then values else f.vals } rest
          else .stuck
        | _, _ => .stuck
      | .BINOP ty (.mk_binop__0 ity op) =>
        match pop f.vals with
        | some (values, rhs) =>
          match pop values with
          | some (values, lhs) =>
            match integer ty lhs, integer ty rhs with
            | some a, some b =>
              if ty = numtype_Inn ity then
                match integerBinary op (if ty = .I32 then 32 else 64) a b with
                | some bits => advance s { f with code := after, vals := values ++ [integerVal ity bits] } rest
                | none => Itasca.SourceMachine.Numeric.transition s f rest after (.binary ity op)
              else .stuck
            | _, _ => .stuck
          | none => .stuck
        | none => .stuck
      | .TESTOP ty (.mk_testop__0 ity .EQZ) =>
        match pop f.vals with
        | some (values, value) =>
          match integer ty value with
          | some bits =>
            if ty = numtype_Inn ity then advance s { f with code := after, vals := values ++ [integerVal .I32 (if bits = 0 then 1 else 0)] } rest
            else .stuck
          | none => .stuck
        | none => .stuck
      | .RELOP ty (.mk_relop__0 ity op) =>
        match pop f.vals with
        | some (values, rhs) =>
          match pop values with
          | some (values, lhs) =>
            match integer ty lhs, integer ty rhs with
            | some a, some b =>
              if ty = numtype_Inn ity then
                let answer := match op with
                  | .EQ => some (decide (a = b))
                  | .LT .U => some (decide (a < b))
                  | _ => none
                match answer with
                | some yes => advance s { f with code := after, vals := values ++ [integerVal .I32 (if yes then 1 else 0)] } rest
                | none => Itasca.SourceMachine.Numeric.transition s f rest after (.compare ity op)
              else .stuck
            | _, _ => .stuck
          | none => .stuck
        | none => .stuck
      | .BLOCK bt body => enterLabel s f rest bt body after false
      | .LOOP bt body => enterLabel s f rest bt body after true
      | .IFELSE bt yes no =>
        match pop f.vals with
        | some (values, condition) =>
          match integer .I32 condition with
          | some bits => advance s { f with vals := values, code := .BLOCK bt (if bits = 0 then no else yes) :: after } rest
          | none => .stuck
        | none => .stuck
      | .BR (.mk_uN depth) => branch s f rest depth
      | .BR_IF (.mk_uN depth) =>
        match pop f.vals with
        | some (values, condition) =>
          match integer .I32 condition with
          | some bits => advance s { f with vals := values, code := if bits = 0 then after else .BR (.mk_uN depth) :: after } rest
          | none => .stuck
        | none => .stuck
      | .CALL (.mk_uN index) => call s f rest index after
      | .RETURN => returnFrame s f rest
      | _ =>
        match Itasca.SourceMachine.Numeric.decodeInstruction instruction with
        | some op => Itasca.SourceMachine.Numeric.transition s f rest after op
        | none => .stuck

end Itasca.SourceMachine

end

/-! ## Typing -/

section

/-! Local typing facts for the integer abstract machine. These lemmas use the
generated value/instruction predicates; whole-state preservation and progress
require the label/caller typing invariant and are not asserted here. -/

namespace Itasca.SourceMachine
open WebAssembly Itasca.Spec

def integerWidth : Inn → Nat
  | .I32 => 32
  | .I64 => 64

theorem integer_u_n_wf (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    wf_uN (integerWidth ty) (.mk_uN bits) := by
  apply wf_uN.uN_case_0
  cases ty <;> norm_num [integerWidth] at h ⊢ <;> omega

theorem integer_num_wf (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    wf_num_ (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits)) := by
  apply wf_num_.num__case_0 _ _ _ ?_ ?_ rfl
  · cases ty <;> decide
  · cases ty <;> exact integer_u_n_wf _ bits h

theorem integer_val_wf (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    wf_val (integerVal ty bits) :=
  .val_case_0 _ _ (integer_num_wf ty bits h)

theorem integer_val_typed {s : store} (hs : wf_store s) (ty : Inn) (bits : Nat)
    (h : bits < 2 ^ integerWidth ty) :
    Val_ok s (integerVal ty bits) (valtype_numtype (numtype_Inn ty)) :=
  .numtype s _ _ hs (integer_val_wf ty bits h)

/-- The dynamic integer check accepts every well-formed integer encoding. -/
theorem integer_accepts (ty : Inn) (bits : Nat) (h : bits < 2 ^ integerWidth ty) :
    integer (numtype_Inn ty) (integerVal ty bits) = some bits := by
  cases ty <;> simp_all [integer, integerVal, numtype_Inn, integerWidth]

theorem code_stack_height_bound {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results) :
    ∀ label ∈ labels, label.height ≤ stack.length := by
  cases h with
  | outer => simp
  | label height nesting _ _ _ =>
    intro label hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp only [List.length_append]; omega
    · have hh := nesting label hm
      simp only [List.length_append]; omega

theorem frame_typed_heights {s : store} {f : AFrame} (h : FrameTyped s f []) : FrameHeights f := by
  cases h with
  | mk C _ _ _ _ _ code _ =>
    intro label hm
    simpa only [List.length_append, List.length_nil, Nat.add_zero, List.length_map] using
      code_stack_height_bound code label hm

theorem replace_frame_heights {f f' : AFrame} {rest : List AFrame}
    (h : Forall FrameHeights (f :: rest)) (hf' : FrameHeights f') :
    Forall FrameHeights (f' :: rest) := by
  intro frame hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact hf'
  · exact h frame (by simp [hm])

/-- A concrete value can never have the bottom stack type. -/
theorem value_type_ne_bot (value : val) : valueType value ≠ .BOT := by
  cases value <;> simp only [valueType]
  · rename_i ty value
    cases ty <;> decide
  · decide
  · rename_i ty
    cases ty <;> decide
  · decide
  · decide

/-- Subtyping cannot change any actual operand type. -/
theorem concrete_result_sub_eq {actual expected : List valtype}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) actual)
    (h : Resulttype_sub (.mk_list actual) (.mk_list expected)) : actual = expected := by
  have rel := Itasca.Spec.Completeness.result_sub_iff.mp h
  clear h
  induction rel with
  | nil => rfl
  | @cons a b tailA tailB hab hs ih =>
    have ha := concrete a (by simp)
    have hab' : a = b := by cases hab <;> simp_all
    subst b
    have htail : Forall (fun ty => ty ≠ valtype.BOT) tailA := fun t ht => concrete t (by simp [ht])
    rw [ih htail]

theorem value_type_of_typed {s : store} {value : val} {ty : valtype}
    (h : Val_ok s value ty) : valueType value = ty := by
  cases h with
  | numtype => rfl
  | vectype ty _ _ _ => cases ty; rfl
  | reftype _ _ hr _ => cases hr <;> rfl

theorem results_type_of_typed {s : store} {values : List val} {types : List valtype}
    (h : ResultsTyped s types values) : values.map valueType = types := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, value_type_of_typed h, ih]

theorem integer_num_inv {ty : Inn} {number : num_}
    (h : wf_num_ (numtype_Inn ty) number) :
    ∃ bits, number = .mk_num__0 ty (.mk_uN bits) ∧ bits < 2 ^ integerWidth ty := by
  cases h with
  | num__case_0 ity bits _ hw heq =>
    have same : ity = ty := by cases ty <;> cases ity <;> simp_all [numtype_Inn]
    subst ity
    cases bits with
    | mk_uN bits =>
      refine ⟨bits, rfl, ?_⟩
      cases hw with
      | uN_case_0 _ hb =>
        cases ty <;> norm_num [integerWidth, size, valtype_Inn] at hb ⊢ <;> omega
  | num__case_1 fty _ _ heq =>
    cases ty <;> cases fty <;> simp_all [numtype_Inn, numtype_Fnn]

/-- Generated integer value typing supplies exactly the dynamic check's domain. -/
theorem integer_val_inv {s : store} {ty : Inn} {value : val}
    (h : Val_ok s value (valtype_numtype (numtype_Inn ty))) :
    ∃ bits, value = integerVal ty bits ∧ bits < 2 ^ integerWidth ty := by
  have hw := val_ok_wf h
  have ht := value_type_of_typed h
  cases hw with
  | val_case_0 nt number hn =>
    have same : nt = numtype_Inn ty := by cases nt <;> cases ty <;> simp_all [valueType, valtype_numtype, numtype_Inn]
    subst nt
    obtain ⟨bits, rfl, hb⟩ := integer_num_inv hn
    exact ⟨bits, rfl, hb⟩
  | val_case_1 vt bits _ => cases ty <;> simp_all [valueType, valtype_numtype, numtype_Inn]
  | val_case_2 rt => cases ty <;> cases rt <;> simp_all [valueType, valtype_numtype, valtype_reftype, numtype_Inn]
  | val_case_3 address => cases ty <;> simp_all [valueType, valtype_numtype, numtype_Inn]
  | val_case_4 address => cases ty <;> simp_all [valueType, valtype_numtype, numtype_Inn]

end Itasca.SourceMachine

end

end

/-! ## MemoryDecoding -/

section

/-! ## Descriptor -/

section

namespace Itasca.SourceMachine.Memory

def Load.bytes : Load → Nat
  | .full ty => sizenn ty / 8
  | .packed _ width _ => width.bits / 8

def Store.bytes : Store → Nat
  | .full ty => sizenn ty / 8
  | .packed _ width => width.bits / 8

end Itasca.SourceMachine.Memory

end

/-! ## Semantics -/

section

namespace Itasca.SourceMachine.Memory
open WebAssembly

def PackedWidth.spec {ty : Inn} (width : PackedWidth ty) : Spec.PackedMemory :=
  match ty,width with
  | .I32,.byte => .i32x8
  | .I32,.half => .i32x16
  | .I64,.byte => .i64x8
  | .I64,.half => .i64x16
  | .I64,.word => .i64x32

theorem PackedWidth.spec_type {ty} (width : PackedWidth ty) : width.spec.type = ty := by
  cases ty <;> cases width <;> rfl

theorem PackedWidth.spec_bytes {ty} (width : PackedWidth ty) : width.spec.bytes = width.bits / 8 := by
  cases ty <;> cases width <;> rfl

def Load.value (op : Load) (payload : List byte) : val :=
  match op with
  | .full ty => .CONST ty (inv_nbytes_ ty payload)
  | .packed ty width sign => .CONST (numtype_Inn ty) (width.spec.loaded sign payload)

def Store.payload (op : Store) (value : num_) : List byte :=
  match op with
  | .full ty => nbytes_ ty value
  | .packed _ width => WebAssembly.Builtins.integerBytes (width.bits / 8)
      (proj_uN_0 (Option.get! (proj_num__0 value)))

theorem Load.value_wf (op : Load) (payload : List byte)
    (valid : Forall wf_byte payload) (length : payload.length = op.bytes) : wf_val (op.value payload) := by
  cases op with
  | full ty =>
    apply wf_val.val_case_0
    exact Spec.numeric_bytes_wf ty payload valid (by cases ty <;> exact length)
  | packed ty width sign =>
    apply wf_val.val_case_0
    have numeric := width.spec.loaded_wf sign payload valid (by simpa only [PackedWidth.spec_bytes,Load.bytes] using length)
    simpa only [PackedWidth.spec_type] using numeric

theorem Load.value_type (op : Load) (payload : List byte) :
    valueType (op.value payload) = valtype_numtype op.type := by
  cases op <;> rfl

theorem Store.payload_wf (op : Store) (value : num_) : Forall wf_byte (op.payload value) := by
  cases op with
  | full ty => exact Spec.numeric_bytes_payload_wf ty value
  | packed ty width => exact Spec.integer_bytes_wf _ _

/-- Every scalar load descriptor has the generated source step, with exactly
its byte-width bounds test and canonical decoded value. -/
theorem Load.source_step (op : Load) (s : WebAssembly.store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (admininstr_instr (op.source argument)))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address,admininstr_instr (op.source argument)]⟩ []
      ⟨⟨s,f⟩,if address + proj_uN_0 argument.OFFSET + op.bytes ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        vals [op.value (((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take op.bytes)]
        else [.TRAP]⟩ := by
  cases op with
  | full ty =>
    have source := Spec.numeric_load_step s f ty argument address storeWf frameWf addressBound operationWf bytesWf
    cases ty <;> exact source
  | packed ty width sign =>
    have source := width.spec.load_step s f sign argument address storeWf frameWf addressBound
      (by cases ty <;> cases width <;> exact operationWf) bytesWf
    cases ty <;> cases width <;> exact source

/-- Scalar stores use the exact byte payload and generated bounds trap. -/
theorem Store.source_step (op : Store) (s : WebAssembly.store) (f : frame) (argument : memarg)
    (address : Nat) (value : num_) (storeWf : wf_store s) (frameWf : wf_frame f)
    (addressBound : address < 2^32) (operationWf : wf_admininstr (admininstr_instr (op.source argument)))
    (valueWf : wf_num_ op.type value) (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Spec.Segment.i32 address,.CONST op.type value,admininstr_instr (op.source argument)]⟩ []
      (if address + proj_uN_0 argument.OFFSET + op.bytes ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨Spec.memoryPayloadWrite s f (address+proj_uN_0 argument.OFFSET) (op.payload value),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  cases op with
  | full ty =>
    have source := Spec.numeric_store_step s f ty argument address value storeWf frameWf
      addressBound operationWf valueWf mapped
    cases ty <;> exact source
  | packed ty width =>
    have typed : Val_ok s (.CONST (numtype_Inn ty) value) (valtype_numtype (numtype_Inn ty)) :=
      .numtype _ _ _ storeWf (.val_case_0 _ _ valueWf)
    obtain ⟨bits,equal,bound⟩ := integer_val_inv typed
    have numbers : value = .mk_num__0 ty (.mk_uN bits) := by cases equal; rfl
    subst value
    have source := width.spec.store_step s f argument address bits storeWf frameWf addressBound
      (by cases ty <;> cases width <;> exact operationWf)
      (by simpa only [PackedWidth.spec_type,Store.type] using valueWf) mapped
    cases ty <;> cases width <;> exact source

end Itasca.SourceMachine.Memory

end

/-! ## Decode -/

section

namespace Itasca.SourceMachine.Memory

def decodeLoad (ty : numtype) : Option loadop_ → Option Load
  | none => some (.full ty)
  | some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) sign)) =>
    if ty = .I32 then some (.packed .I32 .byte sign) else none
  | some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 16) sign)) =>
    if ty = .I32 then some (.packed .I32 .half sign) else none
  | some (.mk_loadop__0 .I64 (.mk_loadop_Inn (.mk_sz 8) sign)) =>
    if ty = .I64 then some (.packed .I64 .byte sign) else none
  | some (.mk_loadop__0 .I64 (.mk_loadop_Inn (.mk_sz 16) sign)) =>
    if ty = .I64 then some (.packed .I64 .half sign) else none
  | some (.mk_loadop__0 .I64 (.mk_loadop_Inn (.mk_sz 32) sign)) =>
    if ty = .I64 then some (.packed .I64 .word sign) else none
  | _ => none

def decodeStore : numtype → Option sz → Option Store
  | ty,none => some (.full ty)
  | .I32,some (.mk_sz 8) => some (.packed .I32 .byte)
  | .I32,some (.mk_sz 16) => some (.packed .I32 .half)
  | .I64,some (.mk_sz 8) => some (.packed .I64 .byte)
  | .I64,some (.mk_sz 16) => some (.packed .I64 .half)
  | .I64,some (.mk_sz 32) => some (.packed .I64 .word)
  | _,_ => none

theorem decode_load_descriptor (op : Load) : decodeLoad op.type op.operation = some op := by
  cases op with
  | full ty => rfl
  | packed ty width sign => cases ty <;> cases width <;> rfl

theorem decode_store_descriptor (op : Store) : decodeStore op.type op.operation = some op := by
  cases op with
  | full ty => rfl
  | packed ty width => cases ty <;> cases width <;> rfl

end Itasca.SourceMachine.Memory

end

end
