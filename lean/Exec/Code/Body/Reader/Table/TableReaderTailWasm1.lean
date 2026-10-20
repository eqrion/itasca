import Itasca.Handler.BrTable

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Visitor-independent fallback and operand checks after Wasm 1 vector labels. -/
def tableReaderTailWasm1 (st : code.OpIterState) (data : Slice U8) (expect : Option code.BlockType) :
    Result (core.result.Result (U32 × code.BlockType) error.OpError × code.OpIterState) := do
  let (reply,next) ← code.read_label st data
  match reply with
  | .Err error => .ok (.Err error,next)
  | .Ok (fallback,target) =>
    let bt ← code.branch_target_bt target
    let merged ← code.merge_target expect bt
    match merged with
    | .Err error => .ok (.Err error,next)
    | .Ok common =>
      let (reply,popped) ← code.pop_with_type next .I32
      match reply with
      | .Err error => .ok (.Err error,popped)
      | .Ok _ =>
        let types ← code.block_results common
        let (reply,args) ← code.pop_types popped (alloc.vec.Vec.deref types)
        match reply with
        | .Err error => .ok (.Err error,args)
        | .Ok _ =>
          let marked ← code.mark_unreachable args
          .ok (.Ok (fallback,common),marked)

/-- Exact source parser factorization around the only visitor-bearing label
collector. This adapter has no additional parsing or acceptance rule. -/
def tableReaderFactoredWasm1 {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (before : V) :
    Result (core.result.Result (U32 × code.BlockType) error.OpError × code.OpIterState × V) := do
  let read ← reader.read_u32_leb data st.pos
  match read with
  | .Err error => .ok (.Err error,st,before)
  | .Ok (count,first) =>
    let (reply,collected,middle) ← code.read_table_labels visitor {st with pos := first} data count before
    match reply with
    | .Err error => .ok (.Err error,collected,middle)
    | .Ok common =>
      let (reply,final) ← tableReaderTailWasm1 collected data common
      .ok (reply,final,middle)

/-- The factorization is the actual extracted Wasm 1 table reader. -/
theorem table_reader_factored_wasm1 {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (before : V) :
    code.read_br_table visitor st data before = tableReaderFactoredWasm1 visitor st data before := by
  unfold code.read_br_table tableReaderFactoredWasm1 tableReaderTailWasm1
  congr 1
  funext read
  cases read with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨count,first⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry,Std.bind_assoc]
    congr 1
    funext result
    obtain ⟨reply,state,middle⟩ := result
    cases reply with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok common =>
      simp only [Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.bind_assoc]
      congr 1
      funext result
      obtain ⟨reply,next⟩ := result
      cases reply with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨fallback,target⟩ := pair
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry,Std.bind_assoc]
        congr 1
        funext bt
        congr 1
        funext merged
        cases merged with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok common =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.bind_assoc]
          congr 1
          funext result
          obtain ⟨reply,popped⟩ := result
          cases reply with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok value =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry,Std.bind_assoc]
            congr 1
            funext types
            congr 1
            funext result
            obtain ⟨reply,args⟩ := result
            cases reply with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok unit =>
              cases unit
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry,Std.bind_assoc]

end Exec.Code
