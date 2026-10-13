import Itasca.Binary.Wasm1.Syntax

/-!
# Wasm 1.0 semantic profile

The Wasm 1.0 restriction on instruction trees that the SpecTec Wasm 2.0 typing rules do not
state. `Wasm1.Instruction` and `Wasm1.Instructions` require every `br_table` to have identical
target signatures, and `Wasm1.Environment` bounds the result counts of the signature tables the
body validator consults. The predicates depend on the label context only
(`Wasm1.Instructions.congr_labels`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- The body API consults the function and type signature tables of `env` directly. Wasm 1.0
permits at most one result in each signature. Coherence of these tables with the module is a
separate module-level obligation. -/
structure Environment (env : module.Env) : Prop where
  funcs : ∀ ft ∈ env.func_types.val, ft.results.val.length ≤ 1
  types : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1

/-- Wasm 1.0 branch tables require identical target signatures. The generated Wasm 2.0 typing
rule only requires a common subtype, which is weaker in unreachable code. Label bounds are
supplied separately by declarative typing. -/
def SameTargets (C : context) (targets : List labelidx) (fallback : labelidx) : Prop :=
  ∀ target ∈ targets,
    C.LABELS[proj_uN_0 target]! = C.LABELS[proj_uN_0 fallback]!

/-- Conditions on a non-structured instruction. Binary provenance already restricts the opcode
set. Structured instructions are excluded and must use the recursive constructors below. -/
def Leaf (C : context) : instr → Prop
  | .BR_TABLE targets fallback => SameTargets C targets fallback
  | .BLOCK _ _ | .LOOP _ _ | .IFELSE _ _ _ => False
  | _ => True

mutual
/-- The context-sensitive Wasm 1.0 restrictions on a generated instruction tree. It does not
mention execution. -/
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

/-- The Wasm 1.0 restrictions hold for every instruction of a sequence. -/
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

namespace Itasca.Wasm1

/-- The profile observes label signatures only, so it is independent of the other context
fields. -/
theorem Instructions.congr_labels {C : context} {ops : List instr}
    (h : Instructions C ops) : ∀ D, C.LABELS = D.LABELS → Instructions D ops := by
  induction h using Instructions.rec
    (motive_1 := fun C op _ => ∀ D, C.LABELS = D.LABELS → Instruction D op)
  case leaf C op hp D he =>
    apply Instruction.leaf
    cases op <;> simp_all [Leaf, SameTargets]
  case block C bt body hb ih D he =>
    apply Instruction.block
    apply ih
    simp [Control.labelContext_labels, he]
  case loop C bt body hb ih D he =>
    apply Instruction.loop
    apply ih
    simp [Control.labelContext_labels, he]
  case ifElse C bt yes no hy hn ihy ihn D he =>
    apply Instruction.ifElse
    · apply ihy; simp [Control.labelContext_labels, he]
    · apply ihn; simp [Control.labelContext_labels, he]
  case nil C => intro D _; exact .nil D
  case cons C op ops hop hops ih ihs =>
    intro D he
    exact .cons (ih D he) (ihs D he)

theorem Instruction.congr_labels {C D : context} {op : instr}
    (h : Instruction C op) (he : C.LABELS = D.LABELS) : Instruction D op :=
  Instructions.singleton_iff.mp ((Instructions.singleton_iff.mpr h).congr_labels D he)

end Itasca.Wasm1
