import Itasca.Wasm2.Frames
import Itasca.Binary.Wasm1.Subset

/-!
# Wasm 1.0 restrictions on the frame zipper

`ProfileFrames profile root frames` holds the Wasm 1.0 restrictions of `Wasm1.Instructions` for the
open frames of the zipper when `profile` is Wasm 1.0: each frame's instructions in a context with
its own label stack, the `then` arm of an `else_` frame, and a one-byte block type for every frame
but the body. `start`, `advance`, `enter`, `else_`, `close` and `finish` follow the frame
operations of `Frames`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

theorem Instruction.congr_labels {C : context} {op : instr} (h : Instruction C op) (D : context)
    (he : C.LABELS = D.LABELS) : Instruction D op := by
  have hs := (Instructions.cons h (.nil C)).congr_labels D he
  cases hs with
  | cons hop _ => exact hop

private theorem numeric_leaf {opcode : U8} {op : Numeric.Operation}
    (h : Numeric.opcodeMeaning opcode = some op) (C : context) : Leaf C op.instruction := by
  unfold Numeric.opcodeMeaning at h
  split at h <;> cases h <;> trivial

private theorem memory_leaf {opcode : U8} {op : MemoryMeaning.Operation}
    (h : MemoryMeaning.opcodeMeaning opcode = some op) (C : context) (arg : code.MemArg) :
    Leaf C (op.op arg) := by
  unfold MemoryMeaning.opcodeMeaning at h
  split at h <;> cases h <;> trivial

theorem Instruction.block_inv {C : context} {bt : blocktype} {body : List instr}
    (h : Instruction C (.BLOCK bt body)) : ∃ result, bt = ._RESULT result ∧
      Instructions (Control.labelContext result.toList ++ C) body := by
  cases h with
  | leaf _ _ hl => exact absurd hl id
  | block _ result _ hb => exact ⟨result, rfl, hb⟩

theorem Instruction.loop_inv {C : context} {bt : blocktype} {body : List instr}
    (h : Instruction C (.LOOP bt body)) : ∃ result, bt = ._RESULT result ∧
      Instructions (Control.labelContext [] ++ C) body := by
  cases h with
  | leaf _ _ hl => exact absurd hl id
  | loop _ result _ hb => exact ⟨result, rfl, hb⟩

theorem Instruction.ifElse_inv {C : context} {bt : blocktype} {yes no : List instr}
    (h : Instruction C (.IFELSE bt yes no)) : ∃ result, bt = ._RESULT result ∧
      Instructions (Control.labelContext result.toList ++ C) yes ∧
      Instructions (Control.labelContext result.toList ++ C) no := by
  cases h with
  | leaf _ _ hl => exact absurd hl id
  | ifElse _ result _ _ hy hn => exact ⟨result, rfl, hy, hn⟩

/-- Every plain Wasm 1.0 token other than `br_table` meets the Wasm 1.0 leaf restriction. -/
theorem Immediate.leaf {opcode : U8} {op : instr} {bytes : List U8}
    (h : Immediate opcode (.plain op) bytes) (hbr : opcode ≠ 0x0E#u8) (C : context) :
    Instruction C op := by
  apply Instruction.leaf
  cases h with
  | brTable => exact absurd rfl hbr
  | memory _ _ _ meaning => exact memory_leaf meaning C _
  | numeric _ _ meaning => exact numeric_leaf meaning C
  | _ => trivial

/-- A plain Wasm 1.0 token other than `br_table` meets the Wasm 1.0 leaf restriction. -/
theorem At.leaf {data start op next} (h : At data start (.plain op) next)
    (hp : start.val < data.length) (hbr : data.val[start.val]'hp ≠ 0x0E#u8) (C : context) :
    Instruction C op := by
  obtain ⟨_, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  have hb := hs.suffix
  rw [List.drop_eq_getElem_cons hp] at hb
  have he : data.val[start.val] = opcode := (List.cons.inj hb).1
  exact hi.leaf (he ▸ hbr) C

end Itasca.Wasm1

namespace Itasca.Wasm2.Frames

/-- A context with the label stack of `frames` on top of `root`'s. -/
def frameContext (root : context) (frames : List Saved) : context :=
  { root with LABELS := labels frames ++ root.LABELS }

theorem labels_snoc (frames : List Saved) (f : Saved) :
    labels (frames ++ [f]) = .mk_list (f.form.label f.ins f.outs) :: labels frames := by
  simp [labels]

/-- The Wasm 1.0 restrictions on one frame in a context `C` that includes its own label. -/
structure Saved.Wasm1Ok (C : context) (f : Saved) : Prop where
  ops : Wasm1.Instructions C f.ops
  prior : ∀ tokens ops, f.form = .else_ tokens ops → Wasm1.Instructions C ops
  block : f.form ≠ .body → ∃ b, Wasm1.ScalarBlockByte f.bt b

/-- `Saved.Wasm1Ok` for every open frame, each in the context of its own and enclosing labels. -/
inductive Wasm1Frames (root : context) : List Saved → Prop where
  | nil : Wasm1Frames root []
  | snoc {frames f} : Wasm1Frames root frames → f.Wasm1Ok (frameContext root (frames ++ [f])) →
      Wasm1Frames root (frames ++ [f])

/-- The profile restrictions on the open frames: `Wasm1Frames` for Wasm 1.0, none for Wasm 2.0. -/
def ProfileFrames (profile : ValidationProfile) (root : context) (frames : List Saved) : Prop :=
  profile = .Wasm1 → Wasm1Frames root frames

theorem Wasm1Frames.unsnoc {root frames f} (h : Wasm1Frames root (frames ++ [f])) :
    Wasm1Frames root frames ∧ f.Wasm1Ok (frameContext root (frames ++ [f])) := by
  generalize hl : frames ++ [f] = all at h
  cases h with
  | nil => simp at hl
  | snoc hfs hf =>
    obtain ⟨rfl, he⟩ := List.append_inj' hl rfl
    injection he with he
    subst he
    exact ⟨hfs, hf⟩

theorem ProfileFrames.start (profile : ValidationProfile) (root : context) (base : Usize)
    (bt : signature.BlockType) (ins outs : List wasm_types.ValueType) :
    ProfileFrames profile root [Saved.fresh base .body bt ins outs] := fun _ =>
  .snoc (frames := []) .nil ⟨.nil _, (fun _ _ h => nomatch h), fun h => absurd rfl h⟩

/-- Appending a Wasm 1.0 instruction to the current frame. -/
theorem ProfileFrames.advance {profile root parents current} (h : ProfileFrames profile root
    (parents ++ [current])) (C : context) (hC : C.LABELS = labels (parents ++ [current]) ++ root.LABELS)
    (token : Token) (op : instr) (poly : Bool) (vals : List code.StackType)
    (hop : profile = .Wasm1 → Wasm1.Instruction C op) :
    ProfileFrames profile root (parents ++ [current.advance token op poly vals]) := by
  intro hp
  obtain ⟨hfs, hf⟩ := (h hp).unsnoc
  have hctx : frameContext root (parents ++ [current.advance token op poly vals]) =
      frameContext root (parents ++ [current]) := by simp [frameContext, labels_snoc, Saved.advance]
  refine .snoc hfs ?_
  rw [hctx]
  exact ⟨hf.ops.append (.cons ((hop hp).congr_labels _ (by rw [hC]; rfl)) (.nil _)), hf.prior,
    hf.block⟩

/-- Opening a `block`, `loop` or `if` with a one-byte block type. -/
theorem ProfileFrames.enter {profile root parents current} (h : ProfileFrames profile root
    (parents ++ [current])) (form : Form) (hi : form.Initial) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (base : Usize) (remaining : List code.StackType)
    (hb : profile = .Wasm1 → ∃ b, Wasm1.ScalarBlockByte bt b) :
    ProfileFrames profile root ((parents ++ [{ current with vals := remaining }]) ++
      [Saved.fresh base form bt ins outs]) := by
  intro hp
  obtain ⟨hfs, hf⟩ := (h hp).unsnoc
  have hctx : frameContext root (parents ++ [{ current with vals := remaining }]) =
      frameContext root (parents ++ [current]) := by simp [frameContext, labels_snoc]
  refine .snoc (.snoc hfs (hctx ▸ ⟨hf.ops, hf.prior, hf.block⟩)) ⟨.nil _, ?_, fun _ => hb hp⟩
  intro tokens ops he
  rcases hi with hi | hi | hi <;> simp [Saved.fresh, hi] at he

/-- Switching from the `then` arm to the `else` arm keeps the frame's label. -/
theorem ProfileFrames.else_ {profile root parents current} (h : ProfileFrames profile root
    (parents ++ [current])) (hform : current.form = .then_) :
    ProfileFrames profile root (parents ++ [current.nextElse]) := by
  intro hp
  obtain ⟨hfs, hf⟩ := (h hp).unsnoc
  have hctx : frameContext root (parents ++ [current.nextElse]) =
      frameContext root (parents ++ [current]) := by
    simp [frameContext, labels_snoc, Saved.nextElse, Form.label, hform]
  refine .snoc hfs ⟨.nil _, ?_, ?_⟩
  · intro tokens ops he
    simp only [Saved.nextElse, Form.else_.injEq] at he
    rw [hctx, ← he.2]
    exact hf.ops
  · intro _
    exact hf.block (by simp [hform])

theorem Closed.wasm1 {env form bt ops op C ins outs}
    (closed : Closed form bt ops op) (hb : ∃ b, Wasm1.ScalarBlockByte bt b)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (D : context) (hD : D.LABELS = .mk_list (form.label ins outs) :: C.LABELS)
    (hops : Wasm1.Instructions D ops)
    (hprior : ∀ tokens thenOps, form = .else_ tokens thenOps → Wasm1.Instructions D thenOps) :
    Wasm1.Instruction C op := by
  obtain ⟨b, hb⟩ := hb
  have hins : ins = [] := by cases hb <;> simpa [inputs, resolve] using hin.symm
  subst hins
  obtain ⟨result, hbt, houts⟩ : ∃ result : Option valtype, blockType bt = ._RESULT result ∧
      outs.map Translate.valueType = result.toList := by
    cases hb <;> simp only [outputs, resolve, Option.some.injEq] at hout <;> subst hout <;>
      exact ⟨_, rfl, rfl⟩
  have hl : form ≠ .loop → D.LABELS = (Control.labelContext result.toList ++ C).LABELS := by
    intro hf
    rw [hD, Control.labelContext_labels, ← houts]
    cases form <;> simp_all [Form.label]
  cases closed with
  | block => rw [hbt]; exact .block C result ops (hops.congr_labels _ (hl (by simp)))
  | loop =>
    rw [hbt]
    exact .loop C result ops (hops.congr_labels _ (by simpa [Form.label] using hD))
  | then_ =>
    rw [hbt]
    exact .ifElse C result ops [] (hops.congr_labels _ (hl (by simp))) (.nil _)
  | else_ _ thenTokens thenOps =>
    rw [hbt]
    exact .ifElse C result thenOps ops ((hprior _ _ rfl).congr_labels _ (hl (by simp)))
      (hops.congr_labels _ (hl (by simp)))

/-- Closing the current frame appends its structured instruction to the parent. -/
theorem ProfileFrames.close {env profile root grandparents parent current op}
    (h : ProfileFrames profile root (grandparents ++ [parent] ++ [current]))
    (closed : Closed current.form current.bt current.ops op)
    (hin : resolve env (inputs current.bt) = some current.ins)
    (hout : resolve env (outputs current.bt) = some current.outs)
    (vals : List code.StackType) (tokens : List Token) :
    ProfileFrames profile root (grandparents ++
      [{ parent with ops := parent.ops ++ [op], vals := vals, tokens := tokens }]) := by
  intro hp
  obtain ⟨hps, hc⟩ := (h hp).unsnoc
  obtain ⟨hgs, hpar⟩ := hps.unsnoc
  have hop := closed.wasm1 (C := frameContext root (grandparents ++ [parent]))
    (hc.block closed.not_body) hin hout _
    (by simp only [frameContext]; rw [labels_snoc]; rfl) hc.ops hc.prior
  refine .snoc hgs ?_
  have hctx : frameContext root (grandparents ++
      [{ parent with ops := parent.ops ++ [op], vals := vals, tokens := tokens }]) =
      frameContext root (grandparents ++ [parent]) := by simp [frameContext, labels_snoc]
  rw [hctx]
  exact ⟨hpar.ops.append (.cons (hop.congr_labels _ (by simp [frameContext])) (.nil _)),
    hpar.prior, hpar.block⟩

/-- Closing the body frame gives the Wasm 1.0 restrictions in the function context. -/
theorem ProfileFrames.finish {profile root current} (h : ProfileFrames profile root [current])
    (hform : current.form = .body) (hp : profile = .Wasm1) :
    Wasm1.Instructions (Control.labelContext (current.outs.map Translate.valueType) ++ root)
      current.ops := by
  obtain ⟨_, hf⟩ := (h hp).unsnoc (frames := [])
  exact hf.ops.congr_labels _ (by simp [frameContext, labels, hform, Form.label])

end Itasca.Wasm2.Frames
