import Itasca.Support.ControlTranslation

/-!
# Wasm 2.0 instruction syntax

The instruction syntax shared by both profiles: flat tokens (`Token`) whose block types are
`signature.BlockType` values, the relation `Emits` between tokens and the structured SpecTec
instructions they spell, and `BodyTokens` for a function body with its final `end`.
`Emits.wellFormed` shows that the emitted instructions satisfy `wf_instr`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A flat instruction stream element: a plain instruction, a structured instruction header or
`else` or `end`. Block types may be type-section indices; the Wasm 1.0 grammar admits only
`ScalarBlockByte` ones. -/
inductive Token where
  | plain (op : instr)
  | block (bt : signature.BlockType)
  | loop (bt : signature.BlockType)
  | if_ (bt : signature.BlockType)
  | else_ | end_

/-- A plain token spells a well-formed instruction. The binary relation `Immediate` restricts
which plain tokens occur. -/
inductive Simple : Token → instr → Prop where
  | plain (op : instr) : wf_instr op → Simple (.plain op) op

/-- A plain token spells a well-formed instruction. -/
theorem Simple.wellFormed {token : Token} {op : instr} (h : Simple token op) :
    wf_instr op := by
  cases h with
  | plain _ hwf => exact hwf

/-- A flat token list spells a list of SpecTec instructions. An `if` with an empty else branch has
two spellings, with and without `else`. -/
inductive Emits : List Token → List instr → Prop where
  | nil : Emits [] []
  | simple {tokens ops token op} : Emits tokens ops → Simple token op →
      Emits (tokens ++ [token]) (ops ++ [op])
  | block {tokens ops bodyTokens body} (bt : signature.BlockType) :
      Emits tokens ops → Emits bodyTokens body →
      Emits (tokens ++ [.block bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.BLOCK (blockType bt) body])
  | loop {tokens ops bodyTokens body} (bt : signature.BlockType) :
      Emits tokens ops → Emits bodyTokens body →
      Emits (tokens ++ [.loop bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.LOOP (blockType bt) body])
  | ifElse {tokens ops thenTokens thenOps elseTokens elseOps} (bt : signature.BlockType) :
      Emits tokens ops → Emits thenTokens thenOps → Emits elseTokens elseOps →
      Emits (tokens ++ [.if_ bt] ++ thenTokens ++ [.else_] ++ elseTokens ++ [.end_])
        (ops ++ [.IFELSE (blockType bt) thenOps elseOps])
  | ifEnd {tokens ops bodyTokens body} (bt : signature.BlockType) :
      Emits tokens ops → Emits bodyTokens body →
      Emits (tokens ++ [.if_ bt] ++ bodyTokens ++ [.end_])
        (ops ++ [.IFELSE (blockType bt) body []])

/-- `Emits` is closed under concatenation. -/
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

/-- Emitted instructions are well formed. -/
theorem Emits.wellFormed {tokens : List Token} {ops : List instr}
    (h : Emits tokens ops) : Forall wf_instr ops := by
  induction h with
  | nil => simp [Forall]
  | simple _ hs ih => simpa [Forall, or_imp, forall_and] using And.intro ih hs.wellFormed
  | block bt _ _ ih hb =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_4 _ _ (blockType_wf bt) hb)
  | loop bt _ _ ih hb =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_5 _ _ (blockType_wf bt) hb)
  | ifElse bt _ _ _ ih ht he =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_6 _ _ _ (blockType_wf bt) ht he)
  | ifEnd bt _ _ ih hb =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_6 _ _ [] (blockType_wf bt) hb (by simp [Forall]))

/-- A function body: tokens that spell the instructions, followed by the final `end`. -/
def BodyTokens (tokens : List Token) (ops : List instr) : Prop :=
  ∃ inner, tokens = inner ++ [.end_] ∧ Emits inner ops

end Itasca.Wasm2
