import Itasca.Wasm1.Complete.Program
import Itasca.Wasm1.Complete.Scalar
import Itasca.Wasm1.Complete.BrTable
import Itasca.Wasm1.Complete.Control
import Itasca.Wasm1.Complete.Env

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

/-- Separate family interface for the independently enumerated load/store map. -/
def MemoryContract (data : Slice U8) (env : module.Env) (ctx : code.Context) : Prop :=
  ∀ (C : context) (st : code.OpIterState) (f : Frame st) (opcode : U8)
    (op : MemoryMeaning.Operation) (arg : code.MemArg) (alignment offset : List U8)
    (next : Usize) (front input output : List valtype),
    EnvTranslation.Matches env ctx C → st.vals.val.length < Usize.max →
    MemoryMeaning.opcodeMeaning opcode = some op →
    Leb128.Encoding alignment arg.align.val → Leb128.Encoding offset arg.offset.val →
    Wasm1.BytesAt data st.pos (alignment ++ offset) next →
    Sequence.Realizes f.current.polymorphic_base f.operands (front ++ input) →
    Instr_ok C (op.op arg) (.mk_functype (.mk_list input) (.mk_list output)) →
    StepResult f data env ctx opcode next (front ++ output)

theorem memory_contract (data : Slice U8) (env : module.Env) (ctx : code.Context) :
    MemoryContract data env ctx := by
  intro C st f opcode op arg alignment offset next front input output hc hsize hmap ha ho hb hr ht
  exact memory f data env ctx C hc opcode op hmap arg alignment offset next ha ho hb
    front input output ht hr hsize

/-- Exhaust the independent Wasm 1.0 leaf encoding relation. Every branch uses
a proved actual-dispatch success theorem and a primitive generated typing rule. -/
theorem leaf_contract (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (henv : Wasm1.Environment env) :
    LeafContract data env ctx := by
  intro C st f opcode op bytes next front input output hc hl hsize hi hb hr ht hp
  cases hi with
  | unreachable => exact unreachable f hb ht
  | nop => exact nop f hb ht hr
  | br idx he =>
      simpa [code.OP_BR] using step_br f data env ctx C idx _ next front input output hb he hl ht hr
  | brIf idx he =>
      simpa [code.OP_BR_IF] using step_br_if f data env ctx C idx _ next front input output
        hb he hl hsize ht hr
  | brTable depths fallback hcount hentries hdefault =>
      exact f.step_brTable data env ctx depths fallback _ _ _ next C front input output
        hcount hentries hdefault hb hl (Wasm1.Instruction.br_table_iff.mp hp) ht hr
  | return_ =>
      simpa [code.OP_RETURN] using step_return f data env ctx C next front input output hb hc.ret ht hr
  | call idx he => exact call f data env ctx C hc henv idx _ next he hb front input output ht hr hsize
  | callIndirect idx he =>
      exact callIndirect f data env ctx C hc henv idx _ next he hb front input output ht hr hsize
  | drop => exact f.step_drop data env ctx next C front input output hb ht hr
  | select => exact f.step_select data env ctx next C front input output hb hsize ht hr
  | localGet idx he => exact localGet f data env ctx C hc idx _ next he hb front input output ht hr hsize
  | localSet idx he => exact localSet f data env ctx C hc idx _ next he hb front input output ht hr
  | localTee idx he => exact localTee f data env ctx C hc idx _ next he hb front input output ht hr hsize
  | globalGet idx he => exact globalGet f data env ctx C hc idx _ next he hb front input output ht hr hsize
  | globalSet idx he => exact globalSet f data env ctx C hc idx _ next he hb front input output ht hr
  | memory opcode operation arg hmap ha ho =>
      exact memory_contract data env ctx C st f opcode operation arg _ _ next front input output
        hc hsize hmap ha ho hb hr ht
  | memorySize => exact memorySize f data env ctx C hc next hb front input output ht hr hsize
  | memoryGrow => exact memoryGrow f data env ctx C hc next hb front input output ht hr hsize
  | i32Const value he => exact f.step_i32Const data env ctx value _ next C front input output he hb hsize ht hr
  | i64Const value he => exact f.step_i64Const data env ctx value _ next C front input output he hb hsize ht hr
  | f32Const value he => exact f.step_f32Const data env ctx value _ next C front input output he hb hsize ht hr
  | f64Const value he => exact f.step_f64Const data env ctx value _ next C front input output he hb hsize ht hr
  | numeric opcode operation hmap =>
      exact f.step_numeric data env ctx opcode operation next C front input output hmap hb hsize ht hr

end Itasca.Wasm1.Completeness
