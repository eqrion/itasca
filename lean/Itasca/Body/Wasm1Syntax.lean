import Itasca.Binary.WasmSyntax

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- The body API consults these two signature tables directly. Wasm 1.0
permits at most one result in each signature; cache coherence is a separate
module obligation. -/
structure Environment (env : module.Env) : Prop where
  funcs : ∀ ft ∈ env.func_types.val, ft.results.val.length ≤ 1
  types : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1

/-- Wasm 1.0 branch tables require identical target signatures. Wasm 2.0's
generated typing rule only requires a common subtype, which is strictly weaker
in unreachable code. Bounds are supplied separately by declarative typing. -/
def SameTargets (C : context) (targets : List labelidx) (fallback : labelidx) : Prop :=
  ∀ target ∈ targets,
    C.LABELS[proj_uN_0 target]! = C.LABELS[proj_uN_0 fallback]!

/-- Conditions for a leaf. Binary provenance already restricts the opcode
set; structured instructions must use the recursive constructors below. -/
def Leaf (C : context) : instr → Prop
  | .BR_TABLE targets fallback => SameTargets C targets fallback
  | .BLOCK _ _ | .LOOP _ _ | .IFELSE _ _ _ => False
  | _ => True

mutual
/-- Independent, context-sensitive Wasm 1.0 semantic restrictions on the
generated instruction tree. This predicate does not mention execution. -/
inductive Instruction : context → instr → Prop where
  | leaf (C : context) (op : instr) : Leaf C op → Instruction C op
  | block (C : context) (bt : code.BlockType) (body : List instr) :
      Instructions (Control.labelContext (Control.resultTypes bt) ++ C) body →
      Instruction C (.BLOCK (Control.blockType bt) body)
  | loop (C : context) (bt : code.BlockType) (body : List instr) :
      Instructions (Control.labelContext [] ++ C) body →
      Instruction C (.LOOP (Control.blockType bt) body)
  | ifElse (C : context) (bt : code.BlockType) (yes no : List instr) :
      Instructions (Control.labelContext (Control.resultTypes bt) ++ C) yes →
      Instructions (Control.labelContext (Control.resultTypes bt) ++ C) no →
      Instruction C (.IFELSE (Control.blockType bt) yes no)

inductive Instructions : context → List instr → Prop where
  | nil (C : context) : Instructions C []
  | cons {C : context} {op : instr} {ops : List instr} :
      Instruction C op → Instructions C ops → Instructions C (op :: ops)
end

theorem Instructions.append {C : context} {xs ys : List instr}
    (hx : Instructions C xs) (hy : Instructions C ys) :
    Instructions C (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
    cases hx with
    | cons h ht => exact .cons h (ih ht)

theorem Instructions.append_iff {C : context} {xs ys : List instr} :
    Instructions C (xs ++ ys) ↔ Instructions C xs ∧ Instructions C ys := by
  constructor
  · intro h
    induction xs with
    | nil => exact ⟨.nil C, h⟩
    | cons x xs ih =>
      cases h with
      | cons hx ht =>
        obtain ⟨hs, hy⟩ := ih ht
        exact ⟨.cons hx hs, hy⟩
  · rintro ⟨hx, hy⟩
    exact hx.append hy

theorem Instructions.singleton_iff {C : context} {op : instr} :
    Instructions C [op] ↔ Instruction C op := by
  constructor
  · intro h; cases h with | cons hop _ => exact hop
  · intro h; exact .cons h (.nil C)

theorem Instruction.br_table_iff {C : context} {targets : List labelidx}
    {fallback : labelidx} :
    Instruction C (.BR_TABLE targets fallback) ↔ SameTargets C targets fallback := by
  constructor
  · intro h; cases h with | leaf _ _ ht => exact ht
  · intro h; exact .leaf C _ h

end Itasca.Wasm1
