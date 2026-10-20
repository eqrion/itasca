import Exec.Abs.Float.ChosenSimulation
import Exec.Spec.NumericPureWitness
namespace Exec.Abs.Float
open SpecExt Exec.Spec

/-- The active scalar numeric request is determined by source syntax and its
operand words; comparisons use the ordinary choice-free pure relation. -/
def Instruction.numericRequest (op : Instruction) (a b : Nat) : Option NumericRequest :=
  match op.source with
  | .UNOP type operation => some (.unary type operation (numberOfBits op.input a))
  | .BINOP type operation => some (.binary type operation (numberOfBits op.input a) (numberOfBits op.input b))
  | .CVTOP target source operation => some (.convert source target operation (numberOfBits op.input a))
  | _ => none

theorem Instruction.numeric_request_code {op : Instruction} {a b : Nat} {request : NumericRequest}
    (read : op.numericRequest a b=some request) :
    request.instructions=vals (op.operands a b)++[admininstr_instr op.source] := by
  cases op
  all_goals simp only [Instruction.numericRequest,Instruction.source,Option.some.injEq] at read
  all_goals cases read
  all_goals rfl

theorem Instruction.numeric_request_type {op : Instruction} {a b : Nat} {request : NumericRequest}
    (read : op.numericRequest a b=some request) : request.type=op.output := by
  cases op
  all_goals simp only [Instruction.numericRequest,Instruction.source,Option.some.injEq] at read
  all_goals cases read
  all_goals rfl

def Instruction.forcedNumeric : Instruction → Bool
  | .unary _ .ABS | .unary _ .NEG | .binary _ .COPYSIGN | .compare _ _
  | .convert _ _ _ | .truncate _ _ _ _ | .reinterpretFloat _ | .reinterpretInt _ => true
  | _ => false

theorem Instruction.numeric_request_forced {op : Instruction} {a b : Nat} {request : NumericRequest}
    (read : op.numericRequest a b=some request) (forced : op.forcedNumeric=true) : request.Forced := by
  cases op
  case unary type operation =>
    cases type <;> cases operation
    all_goals simp_all [Instruction.numericRequest,Instruction.source,Instruction.input,Instruction.forcedNumeric,numberOfBits]
    all_goals cases read
    all_goals apply float_sign_unary_request_forced <;> simp
  case binary type operation =>
    cases type <;> cases operation
    all_goals simp_all [Instruction.numericRequest,Instruction.source,Instruction.input,Instruction.forcedNumeric,numberOfBits]
    all_goals cases read
    all_goals exact float_copysign_request_forced _ _ _
  all_goals try { simp [Instruction.forcedNumeric] at forced }
  all_goals simp only [Instruction.numericRequest,Instruction.source,Instruction.input,Option.some.injEq] at read
  all_goals cases read
  all_goals apply conversion_request_forced
  all_goals rfl

/-- Sign operations, comparisons and non-resizing conversions have no genuine
reply alternatives. Their generated result refines every admissible policy. -/
theorem Instruction.chosen_result_forced {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) {op : Instruction} {a b : Nat} {result : Option Nat}
    (source : op.Result a b result) (forced : op.forcedNumeric=true) : op.ChosenResult choices occurrence a b result := by
  cases read : op.numericRequest a b with
  | none =>
    have free : ChoiceFreePureRedex (vals (op.operands a b)++[admininstr_instr op.source]) := by
      cases op
      all_goals simp [Instruction.numericRequest,Instruction.source] at read
      rfl
    cases result with
    | none => exact .ordinary source free
    | some bits => exact ⟨source.1,.ordinary source.2 free⟩
  | some request =>
    have canonicalInput := Instruction.numeric_request_code read
    have canonicalType := Instruction.numeric_request_type read
    have requestForced := Instruction.numeric_request_forced read forced
    cases result with
    | none =>
      have chosen := chosen_numeric_of_forced_pure admissible.numeric occurrence source request none canonicalInput.symm rfl requestForced
      have reduction : ChosenPure choices occurrence request.instructions (numericOutput request.type none) := .numeric chosen
      simpa only [Instruction.ChosenResult,canonicalInput,numericOutput] using reduction
    | some bits =>
      have output : [admininstr_val (.CONST op.output (numberOfBits op.output bits))]=
          numericOutput request.type (some (numberOfBits op.output bits)) := by
        simp only [canonicalType,numericOutput,admininstr_val]
      have chosen := chosen_numeric_of_forced_pure admissible.numeric occurrence source.2 request
        (some (numberOfBits op.output bits)) canonicalInput.symm output requestForced
      refine ⟨source.1,?_⟩
      have reduction : ChosenPure choices occurrence request.instructions
          (numericOutput request.type (some (numberOfBits op.output bits))) := .numeric chosen
      simpa only [canonicalInput,canonicalType,numericOutput,admininstr_val] using reduction

/-- A concrete numeric reply refines the scalar descriptor without changing the
policy or the occurrence at which that reply is consumed. -/
theorem Instruction.chosen_result_of_numeric {op : Instruction} {choices : SourceChoices}
    {occurrence a b : Nat} {result : Option Nat} {request : NumericRequest}
    (source : op.Result a b result) (read : op.numericRequest a b = some request)
    (chosen : ChosenNumeric choices.numeric occurrence request
      (result.map (numberOfBits op.output))) : op.ChosenResult choices occurrence a b result := by
  have canonicalInput := Instruction.numeric_request_code read
  have canonicalType := Instruction.numeric_request_type read
  cases result with
  | none =>
    have reduction := ChosenPure.numeric (choices := choices) chosen
    simpa only [Instruction.ChosenResult,Option.map_none,canonicalInput,numericOutput] using reduction
  | some bits =>
    refine ⟨source.1, ?_⟩
    have reduction := ChosenPure.numeric (choices := choices) chosen
    simpa only [Option.map_some,canonicalInput,canonicalType,numericOutput,admininstr_val] using reduction
end Exec.Abs.Float
