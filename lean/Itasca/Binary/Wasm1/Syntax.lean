import Itasca.Handler.Numeric
import Itasca.Handler.Block

open Aeneas Aeneas.Std

namespace Itasca.Wasm

/-- The flat instruction stream for the full Wasm 1.0 body proof.
Block types retain all four Wasm 1.0 value types. Delimiters are explicit. -/
inductive Token where
  | plain (op : instr)
  | block (bt : code.BlockType)
  | loop (bt : code.BlockType)
  | if_ (bt : code.BlockType)
  | else_ | end_

/-- Leaf syntax is separate from binary encoding. The independent binary
relation restricts these leaves to the Wasm 1.0 opcode and immediate forms. -/
inductive Simple : Token → instr → Prop where
  | plain (op : instr) : wf_instr op → Simple (.plain op) op

theorem Simple.wellFormed {token : Token} {op : instr} (h : Simple token op) :
    wf_instr op := by
  cases h with
  | plain _ hwf => exact hwf

/-- Flat tokens spell these generated SpecTec instructions. This local syntax
relation permits both binary spellings of an if with an empty else branch. -/
inductive Emits : List Token → List instr → Prop where
  | nil : Emits [] []
  | simple {tokens ops token op} : Emits tokens ops → Simple token op →
      Emits (tokens ++ [token]) (ops ++ [op])
  | block {tokens ops bodyTokens body} (bt : code.BlockType) :
      Emits tokens ops → Emits bodyTokens body →
      Emits (tokens ++ [.block bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.BLOCK (Control.blockType bt) body])
  | loop {tokens ops bodyTokens body} (bt : code.BlockType) :
      Emits tokens ops → Emits bodyTokens body →
      Emits (tokens ++ [.loop bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.LOOP (Control.blockType bt) body])
  | ifElse {tokens ops thenTokens thenOps elseTokens elseOps} (bt : code.BlockType) :
      Emits tokens ops → Emits thenTokens thenOps → Emits elseTokens elseOps →
      Emits (tokens ++ [.if_ bt] ++ thenTokens ++ [.else_] ++ elseTokens ++ [.end_])
        (ops ++ [.IFELSE (Control.blockType bt) thenOps elseOps])
  | ifEnd {tokens ops bodyTokens body} (bt : code.BlockType) :
      Emits tokens ops → Emits bodyTokens body →
      Emits (tokens ++ [.if_ bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.IFELSE (Control.blockType bt) body []])

theorem Emits.append {xs ys : List Token} {is js : List instr}
    (hx : Emits xs is) (hy : Emits ys js) : Emits (xs ++ ys) (is ++ js) := by
  induction hy with
  | nil => simpa using hx
  | simple _ hop ih => simpa [List.append_assoc] using Emits.simple ih hop
  | block bt _ hb ih _ => simpa [List.append_assoc] using Emits.block bt ih hb
  | loop bt _ hb ih _ => simpa [List.append_assoc] using Emits.loop bt ih hb
  | ifElse bt _ ht he ih _ _ =>
      simpa [List.append_assoc] using Emits.ifElse bt ih ht he
  | ifEnd bt _ hb ih _ => simpa [List.append_assoc] using Emits.ifEnd bt ih hb

theorem Emits.wellFormed {tokens : List Token} {ops : List instr}
    (h : Emits tokens ops) : Forall wf_instr ops := by
  induction h with
  | nil => simp [Forall]
  | simple _ hs ih => simpa [Forall, or_imp, forall_and] using And.intro ih hs.wellFormed
  | block bt _ _ ih hb =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_4 _ _ (Control.blockType_wf bt) hb)
  | loop bt _ _ ih hb =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_5 _ _ (Control.blockType_wf bt) hb)
  | ifElse bt _ _ _ ih ht he =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_6 _ _ _ (Control.blockType_wf bt) ht he)
  | ifEnd bt _ _ ih hb =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_6 _ _ [] (Control.blockType_wf bt) hb (by simp [Forall]))

/-- The function's final end is outside the generated instruction list. -/
def BodyTokens (tokens : List Token) (ops : List instr) : Prop :=
  ∃ inner, tokens = inner ++ [.end_] ∧ Emits inner ops

end Itasca.Wasm
