import Itasca.Runtime.Abs.Decode
import Itasca.Runtime.Abs.Numeric.Decode

/-! Executable abstract transition for the integer vertical slice. Other
instruction families return `stuck` until their transition cases are added;
no total-Wasm progress claim is made by this definition. -/

namespace Itasca.Runtime.Abs

inductive AResult where
  | next (state : AState)
  | done (values : List val)
  | trap
  | host (address : funcaddr) (args : List val) (resultTypes : List valtype) (resume : AState)
  | stuck

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

def integerVal (ty : Inn) (bits : Nat) : val :=
  .CONST (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits))

def valueType : val → valtype
  | .CONST ty _ => valtype_numtype ty
  | .VCONST _ _ => .V128
  | .REF_NULL rt => valtype_reftype rt
  | .REF_FUNC_ADDR _ => .FUNCREF
  | .REF_HOST_ADDR _ => .EXTERNREF

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

def defaultValue : valtype → Option val
  | .I32 => some (integerVal .I32 0)
  | .I64 => some (integerVal .I64 0)
  | .F32 => some (.CONST .F32 (.mk_num__1 .F32 (.POS (.SUBNORM 0))))
  | .F64 => some (.CONST .F64 (.mk_num__1 .F64 (.POS (.SUBNORM 0))))
  | .V128 => some (.VCONST .V128 (.mk_uN 0))
  | .FUNCREF => some (.REF_NULL .FUNCREF)
  | .EXTERNREF => some (.REF_NULL .EXTERNREF)
  | .BOT => none

def defaultLocals : List «local» → Option (List val)
  | [] => some []
  | .LOCAL ty :: rest => do
      let value ← defaultValue ty
      let values ← defaultLocals rest
      pure (value :: values)

/-- Calls resolve through the active module's address map. Host calls suspend
with a typed expected result list, ready for the checked host-extension boundary. -/
def call (s : AState) (f : AFrame) (rest : List AFrame) (index : Nat)
    (after : List instr) : AResult :=
  match f.module.FUNCS[index]? with
  | none => .stuck
  | some address =>
    match s.store.FUNCS[address]? with
    | none => .stuck
    | some function =>
      let ⟨.mk_list params, .mk_list results⟩ := function.TYPE
      if params.length ≤ f.vals.length then
        let args := f.vals.drop (f.vals.length - params.length)
        if args.map valueType = params then
          let caller := { f with vals := f.vals.take (f.vals.length - params.length), code := after }
          match function.CODE with
          | .HOST _ => .host address args results { s with frames := caller :: rest }
          | .FUNC _ locals body =>
            match defaultLocals locals with
            | none => .stuck
            | some defaults =>
              let label : Label := {
                branchTypes := results
                resultTypes := results
                cont := []
                height := 0
                after := [] }
              let callee : AFrame := {
                fa := address
                resultTypes := results
                locals := args ++ defaults
                module := function.MODULE
                labels := [label]
                code := body
                vals := [] }
              .next { s with frames := callee :: caller :: rest }
        else .stuck
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
                | none => Numeric.transition s f rest after (.binary ity op)
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
                | none => Numeric.transition s f rest after (.compare ity op)
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
        match Numeric.decodeInstruction instruction with
        | some op => Numeric.transition s f rest after op
        | none => .stuck

end Itasca.Runtime.Abs
