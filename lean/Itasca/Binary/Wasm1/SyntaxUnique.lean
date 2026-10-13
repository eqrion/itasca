import Itasca.Binary.Wasm1.Syntax

/-!
# Uniqueness of Wasm 1.0 instruction syntax

`Emits.unique` and `BodyTokens.unique` show that a token list spells at most one instruction
list. The proof folds the tokens with a stack of open structured instructions
(`SyntaxDecode.run`).
-/

namespace Itasca.Wasm1

namespace SyntaxDecode

/-- An open structured instruction awaiting its `end`, with the instructions emitted before it. -/
inductive Frame where
  | block (bt : code.BlockType) (prior : List instr)
  | loop (bt : code.BlockType) (prior : List instr)
  | then_ (bt : code.BlockType) (prior : List instr)
  | else_ (bt : code.BlockType) (prior yes : List instr)

/-- The instructions emitted at the current nesting level and the stack of open frames. -/
structure State where
  ops : List instr
  parents : List Frame

/-- Processes one token, failing on an `else` or `end` with no matching open frame. -/
def step (s : State) : Token → Option State
  | .plain op => some { s with ops := s.ops ++ [op] }
  | .block bt => some ⟨[], .block bt s.ops :: s.parents⟩
  | .loop bt => some ⟨[], .loop bt s.ops :: s.parents⟩
  | .if_ bt => some ⟨[], .then_ bt s.ops :: s.parents⟩
  | .else_ => match s.parents with
    | .then_ bt prior :: parents => some ⟨[], .else_ bt prior s.ops :: parents⟩
    | _ => none
  | .end_ => match s.parents with
    | .block bt prior :: parents =>
        some ⟨prior ++ [.BLOCK (Control.blockType bt) s.ops], parents⟩
    | .loop bt prior :: parents =>
        some ⟨prior ++ [.LOOP (Control.blockType bt) s.ops], parents⟩
    | .then_ bt prior :: parents =>
        some ⟨prior ++ [.IFELSE (Control.blockType bt) s.ops []], parents⟩
    | .else_ bt prior yes :: parents =>
        some ⟨prior ++ [.IFELSE (Control.blockType bt) yes s.ops], parents⟩
    | [] => none

/-- Processes a token list from a state. -/
def run : List Token → State → Option State
  | [], s => some s
  | t :: ts, s => (step s t).bind (run ts)

theorem run_append (xs ys : List Token) (s : State) :
    run (xs ++ ys) s = (run xs s).bind (run ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, run]
    cases step s x <;> simp_all

end SyntaxDecode

/-- `SyntaxDecode.run` on an emitting token list appends the emitted instructions. -/
theorem Emits.decode {tokens ops} (h : Emits tokens ops) (s : SyntaxDecode.State) :
    SyntaxDecode.run tokens s = some { s with ops := s.ops ++ ops } := by
  induction h generalizing s with
  | nil => simp [SyntaxDecode.run]
  | simple _ hs ih =>
    cases hs
    simp [SyntaxDecode.run_append, ih, SyntaxDecode.run, SyntaxDecode.step, List.append_assoc]
  | block bt _ _ ih ihb | loop bt _ _ ih ihb | ifEnd bt _ _ ih ihb =>
    simp [SyntaxDecode.run_append, ih, SyntaxDecode.run, SyntaxDecode.step, ihb, List.append_assoc]
  | ifElse bt _ _ _ ih ihy ihn =>
    simp [SyntaxDecode.run_append, ih, SyntaxDecode.run, SyntaxDecode.step, ihy, ihn, List.append_assoc]

/-- A token list determines the structured instructions it spells. -/
theorem Emits.unique {tokens xs ys} (hx : Emits tokens xs) (hy : Emits tokens ys) : xs = ys := by
  have h := (hx.decode ⟨[], []⟩).symm.trans (hy.decode ⟨[], []⟩)
  simpa using congrArg (fun s => s.map SyntaxDecode.State.ops) h

/-- A body's tokens determine its instructions. -/
theorem BodyTokens.unique {tokens xs ys}
    (hx : BodyTokens tokens xs) (hy : BodyTokens tokens ys) : xs = ys := by
  obtain ⟨left, hl, hx⟩ := hx
  obtain ⟨right, hr, hy⟩ := hy
  have he : left = right := List.append_cancel_right (hl.symm.trans hr)
  subst right
  exact hx.unique hy

end Itasca.Wasm1
