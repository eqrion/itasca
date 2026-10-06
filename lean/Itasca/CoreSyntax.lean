import Itasca.Numeric
import Itasca.Block

open Aeneas Aeneas.Std

namespace Itasca.Core

/-- The flat instruction stream for the first whole-body Lean milestone.
Block types retain all four Wasm 1.0 value types. Delimiters are explicit. -/
inductive Token where
  | nop | unreachable | drop | i32Add
  | i32Const (value : I32)
  | block (bt : code.BlockType)
  | loop (bt : code.BlockType)
  | if_ (bt : code.BlockType)
  | else_ | end_
  | br (depth : U32)
  | brIf (depth : U32)
  | return_

def Token.opcode : Token → U8
  | .nop => code.OP_NOP
  | .unreachable => code.OP_UNREACHABLE
  | .drop => code.OP_DROP
  | .i32Add => code.OP_I32_ADD
  | .i32Const _ => code.OP_I32_CONST
  | .block _ => code.OP_BLOCK
  | .loop _ => code.OP_LOOP
  | .if_ _ => code.OP_IF
  | .else_ => code.OP_ELSE
  | .end_ => code.OP_END
  | .br _ => code.OP_BR
  | .brIf _ => code.OP_BR_IF
  | .return_ => code.OP_RETURN

/-- SpecTec represents an i32 constant by its unsigned 32-bit bit pattern. -/
def i32Const (value : I32) : instr :=
  .CONST .I32 (.mk_num__0 .I32 (.mk_uN (value.val % 4294967296).toNat))

theorem i32Const_wf (value : I32) : wf_instr (i32Const value) := by
  apply wf_instr.instr_case_13
  apply wf_num_.num__case_0 _ .I32 _ (by decide) _ rfl
  apply wf_uN.uN_case_0
  have hmod := Int.emod_lt_of_pos value.val (by decide : (0 : Int) < 4294967296)
  have hnonneg := Int.emod_nonneg value.val (by decide : (4294967296 : Int) ≠ 0)
  norm_num [size, valtype_Inn] at hmod hnonneg ⊢
  omega

theorem label_wf (depth : U32) : wf_uN 32 (.mk_uN depth.val) := by
  apply wf_uN.uN_case_0
  have h := depth.hmax
  norm_num at h ⊢
  omega

/-- Translation for instructions without nested instruction lists. -/
inductive Simple : Token → instr → Prop where
  | nop : Simple .nop .NOP
  | unreachable : Simple .unreachable .UNREACHABLE
  | drop : Simple .drop .DROP
  | i32Add : Simple .i32Add Numeric.i32Add
  | i32Const (value : I32) : Simple (.i32Const value) (i32Const value)
  | br (depth : U32) : Simple (.br depth) (.BR (.mk_uN depth.val))
  | brIf (depth : U32) : Simple (.brIf depth) (.BR_IF (.mk_uN depth.val))
  | return_ : Simple .return_ .RETURN

theorem Simple.wellFormed {token : Token} {op : instr} (h : Simple token op) :
    wf_instr op := by
  cases h with
  | nop => exact .instr_case_0
  | unreachable => exact .instr_case_1
  | drop => exact .instr_case_2
  | i32Add => exact Numeric.i32Add_wf
  | i32Const v => exact i32Const_wf v
  | br d => exact .instr_case_7 _ (label_wf d)
  | brIf d => exact .instr_case_8 _ (label_wf d)
  | return_ => exact .instr_case_12

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

end Itasca.Core
