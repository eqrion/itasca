import Exec.Code.Body.Reader.Acceptance.BodyReaderAcceptance
import Itasca.Wasm2.Trace.ControlRecords

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Checked metadata-producing profile readers, excluding the streamed table
reader, which has a separate source-count replay proof. -/
inductive ControlReaderKind where
  | block
  | loop
  | if_
  | else_
  | end_
  | br
  | br_if
  | return_
  | call
  | call_indirect

namespace ControlReaderKind

def opcode : ControlReaderKind → U8
  | .block => 2#u8
  | .loop => 3#u8
  | .if_ => 4#u8
  | .else_ => 5#u8
  | .end_ => 11#u8
  | .br => 12#u8
  | .br_if => 13#u8
  | .return_ => 15#u8
  | .call => 16#u8
  | .call_indirect => 17#u8

/-- Every control opcode belongs to the shared reader inventory. -/
theorem of_opcode_mem (opcode : U8)
    (member : opcode.val ∈ [2,3,4,5,11,12,13,15,16,17]) : ∃ kind : ControlReaderKind, opcode = kind.opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal | equal | equal | equal | equal
  · exact ⟨.block,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.loop,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.if_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.else_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.end_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.br,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.br_if,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.return_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.call,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.call_indirect,UScalar.eq_of_val_eq equal⟩

def Parameter : ControlReaderKind → Type
  | .block => signature.BlockType
  | .loop => signature.BlockType
  | .if_ => signature.BlockType
  | .else_ => code.LabelKind × signature.BlockType
  | .end_ => code.LabelKind × signature.BlockType
  | .br => U32 × signature.ResultType
  | .br_if => U32 × signature.ResultType
  | .return_ => Unit
  | .call => U32
  | .call_indirect => U32 × U32

def read (kind : ControlReaderKind) (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (index : U32) : Result (core.result.Result kind.Parameter error.OpError × code.BodyState) :=
  match kind with
  | .block => code.enter_info st data env .Wasm2 .Block
  | .loop => code.enter_info st data env .Wasm2 .Loop
  | .if_ => code.enter_info st data env .Wasm2 .Then
  | .else_ => code.end_frame_info st env true
  | .end_ => code.end_frame_info st env false
  | .br => code.branch_info st data env false
  | .br_if => code.branch_info st data env true
  | .return_ => Wasm2.returnStep st env index
  | .call => code.call_info st data env
  | .call_indirect => code.call_indirect_info st data env .Wasm2

def action : (kind : ControlReaderKind) → kind.Parameter → Action
  | .block => .block
  | .loop => .loop
  | .if_ => .if_
  | .else_ => fun arg => .else_ arg.2
  | .end_ => fun arg => .end_ arg.1 arg.2
  | .br => fun arg => .br arg.1 arg.2
  | .br_if => fun arg => .br_if arg.1 arg.2
  | .return_ => fun _ => .return_
  | .call => .call
  | .call_indirect => fun arg => .call_indirect arg.1 arg.2

/-- Every inventory entry agrees with actual complete-profile dispatch. -/
theorem dispatch {V : Type} (kind : ControlReaderKind) (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (before : V) :
    code.step_profile visitor st data env ctx index .Wasm2 kind.opcode before =
      Wasm2.CallbackTrace.bodyRun (kind.read st data env index) visitor kind.action before := by
  cases kind
  · exact Wasm2.CallbackTrace.dispatch_block visitor st data env ctx index .Wasm2 before
  · exact Wasm2.CallbackTrace.dispatch_loop visitor st data env ctx index .Wasm2 before
  · exact Wasm2.CallbackTrace.dispatch_if visitor st data env ctx index .Wasm2 before
  · exact Wasm2.CallbackTrace.dispatch_else visitor st data env ctx index .Wasm2 before
  · exact Wasm2.CallbackTrace.dispatch_end visitor st data env ctx index .Wasm2 before
  · exact Wasm2.CallbackTrace.dispatch_br visitor st data env ctx index .Wasm2 before
  · exact Wasm2.CallbackTrace.dispatch_br_if visitor st data env ctx index .Wasm2 before
  · exact Wasm2.CallbackTrace.dispatch_return visitor st data env ctx index .Wasm2 before
  · exact Wasm2.CallbackTrace.dispatch_call visitor st data env ctx index .Wasm2 before
  · exact Wasm2.CallbackTrace.dispatch_call_indirect visitor st data env ctx index .Wasm2 before

/-- Source byte provenance for every metadata-producing reader in this
inventory. This also bounds its accepted final cursor by input length. -/
theorem records {data env locals index st} (kind : ControlReaderKind)
    (pending : Wasm2.Pending data env .Wasm2 locals index st) {V : Type}
    (visitor : code.OpVisitor V) (observe : V → List Observation)
    (recorded : Records visitor observe) (ctx : code.Context)
    (byte : data.val[pending.start.val]'pending.inbounds = kind.opcode) :
    Wasm2.CallbackTrace.ProfileStepRecords pending visitor observe ctx kind.opcode := by
  cases kind
  · exact Wasm2.CallbackTrace.step_block pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_loop pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_if pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_else pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_end pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_br pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_br_if pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_return pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_call pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_call_indirect pending visitor observe recorded ctx byte

end ControlReaderKind
end Exec.Code
