import Itasca.Support.Translation
import Itasca.Binary.LebReaders
import Itasca.Results.Definitions.Validation

open WebAssembly

/-!
Proofs for Handler.

This module collects Environment, StackModel.
Each section documents its contracts and consumers.
-/

/-! ## Environment -/

section

/-!
# Environment and control-stack readers

Control bases, polymorphic stacks and environment/index lookups supply the shared reader
contracts. Reserved-zero and memory-alignment checks retain their exact extracted effects.
-/

/-! ## Control -/

section

/-!
# Control frames

Control-frame vocabulary over the extracted `code.OpIterState`: `base`, `polymorphic`, and the
structural invariant `Body.Control.Shape`, with specifications for `code.cur_base` and
`code.cur_polymorphic`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Control

/-- The operand stack base of the innermost frame, or `0` with no frames. -/
def base (st : code.OpIterState) : Usize :=
  match st.ctrls.val.getLast? with
  | none => 0#usize
  | some c => c.value_stack_base

/-- Whether the innermost frame is unreachable; `false` with no frames. -/
def polymorphic (st : code.OpIterState) : Bool :=
  match st.ctrls.val.getLast? with
  | none => false
  | some c => c.polymorphic_base

/-- The structural invariant of the control stack: frame stack bases are ordered and within the
operand stack. -/
structure Shape (st : code.OpIterState) : Prop where
  ordered : st.ctrls.val.Pairwise (fun c d => c.value_stack_base.val ≤ d.value_stack_base.val)
  bounded : ∀ c ∈ st.ctrls.val, c.value_stack_base.val ≤ st.vals.val.length

/-- The current frame base is within the operand stack. -/
theorem Shape.base_le {st : code.OpIterState} (h : Shape st) :
    (base st).val ≤ st.vals.val.length := by
  unfold base
  split
  · simp
  · rename_i c hc
    exact h.bounded c (List.mem_of_getLast? hc)

/-- Truncating the operands to the innermost frame base and marking it polymorphic preserves
`Shape`. -/
theorem Shape.unreachable {st st' : code.OpIterState} (h : Shape st)
    (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c])
    (hctrls' : st'.ctrls.val = cs ++ [{ c with polymorphic_base := true }])
    (hlen : st'.vals.val.length = c.value_stack_base.val) : Shape st' := by
  have hord := h.ordered
  rw [hctrls, List.pairwise_append] at hord
  constructor
  · simpa [hctrls', List.pairwise_append] using hord
  · intro d hd
    rw [hctrls'] at hd
    rcases List.mem_append.mp hd with hd | hd
    · rw [hlen]
      exact hord.2.2 d hd c (by simp)
    · have heq : d = { c with polymorphic_base := true } := by simpa using hd
      simp [heq, hlen]

end Itasca.Body.Control

namespace Itasca

@[step]
theorem code.cur_base.spec (st : code.OpIterState) :
    code.cur_base st ⦃ (b : Usize) => b = Body.Control.base st ⦄ := by
  rcases List.eq_nil_or_concat' st.ctrls.val with h | ⟨cs, c, h⟩
  · unfold code.cur_base
    have hn : alloc.vec.Vec.len st.ctrls = 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    simp [Body.Control.base, h]
  · unfold code.cur_base
    have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    step*
    simp_all [Body.Control.base]

@[step]
theorem code.cur_polymorphic.spec (st : code.OpIterState) :
    code.cur_polymorphic st ⦃ (b : Bool) => b = Body.Control.polymorphic st ⦄ := by
  rcases List.eq_nil_or_concat' st.ctrls.val with h | ⟨cs, c, h⟩
  · unfold code.cur_polymorphic
    have hn : alloc.vec.Vec.len st.ctrls = 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    simp [Body.Control.polymorphic, h]
  · unfold code.cur_polymorphic
    have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    step*
    simp_all [Body.Control.polymorphic]

end Itasca

end

/-! ## Unreachable -/

section

/-!
# Unreachable code handling

Specifications of `code.mark_unreachable_loop` and `code.mark_unreachable`, which truncate the
operand stack to the innermost frame base and make that frame polymorphic. In such a frame
`code.pop_stack_type` and `code.pop_with_type` return `Bot` at the base without consuming
operands.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `Vec.pop` returns the last element and removes it. -/
@[step]
theorem _root_.Aeneas.Std.alloc.vec.Vec.pop.spec {T : Type} (allocator : Type) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.pop allocator v ⦃ (r : Option T × alloc.vec.Vec T) =>
      r.1 = v.val.getLast? ∧ r.2.val = v.val.dropLast ⦄ := by
  simp [alloc.vec.Vec.pop]

/-- `code.mark_unreachable_loop` terminates and removes exactly the operands above `base`. -/
@[step]
theorem code.mark_unreachable_loop.spec (st : code.OpIterState) (base : Usize)
    (hbase : base.val ≤ st.vals.val.length) :
    code.mark_unreachable_loop st base ⦃ r =>
      r.1.val = st.vals.val.take base.val ∧ r.1.val.length = base.val ∧
      r.2.1 = st.ctrls ∧ r.2.2 = st.pos ⦄ := by
  unfold code.mark_unreachable_loop
  apply loop.spec_decr_nat (fun s => s.vals.val.length)
    (fun s => base.val ≤ s.vals.val.length ∧
      s.vals.val.take base.val = st.vals.val.take base.val ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos)
  · intro s ⟨hlen, htake, hctrls, hpos⟩
    unfold code.mark_unreachable_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : s.vals.val.length = base.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨by simpa [← heq] using htake, heq, hctrls, hpos⟩
    · rename_i hmore
      have hlt : base.val < s.vals.val.length := by scalar_tac
      step*
      simp_all only [List.length_dropLast]
      refine ⟨by omega, ?_, trivial, trivial, by omega⟩
      simpa [List.dropLast_eq_take, List.take_take,
        Nat.min_eq_left (by omega : base.val ≤ s.vals.val.length - 1)] using htake
  · exact ⟨hbase, rfl, rfl, rfl⟩

/-- `code.mark_unreachable` drops the operands above the innermost frame base and makes only that
frame polymorphic. -/
@[step]
theorem code.mark_unreachable.spec (st : code.OpIterState) (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c])
    (hbase : c.value_stack_base.val ≤ st.vals.val.length) :
    code.mark_unreachable st ⦃ st' =>
      st'.vals.val = st.vals.val.take c.value_stack_base.val ∧
      st'.vals.val.length = c.value_stack_base.val ∧
      st'.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      st'.pos = st.pos ⦄ := by
  unfold code.mark_unreachable
  have hb : Body.Control.base st = c.value_stack_base := by simp [Body.Control.base, hctrls]
  step*
  simp_all

/-- With no operands above the frame base, `code.pop_stack_type` returns `Bot` in a polymorphic
frame and `EmptyStack` otherwise, leaving the state unchanged. -/
theorem code.pop_stack_type.at_base (st : code.OpIterState)
    (hbase : alloc.vec.Vec.len st.vals = Body.Control.base st) :
    code.pop_stack_type st = .ok
      (if Body.Control.polymorphic st then (.Ok .Bot, st) else (.Err .EmptyStack, st)) := by
  obtain ⟨_, hb, rfl⟩ := WP.spec_imp_exists (code.cur_base.spec st)
  obtain ⟨_, hp, rfl⟩ := WP.spec_imp_exists (code.cur_polymorphic.spec st)
  cases h : Body.Control.polymorphic st <;> simp [code.pop_stack_type, hb, hbase, hp, h]

end Itasca

end

/-! ## EnvReaders -/

section

/-!
# Environment readers

Specifications of extracted lookups, reserved-zero checks and memory arguments:
`code.local_type`, `code.global_type`, `code.take_local`, `code.take_global`,
`code.take_index`, `code.read_reserved_zero`, `code.require_memory`,
`code.read_memarg` and `code.check_memory_and_alignment`. Their contracts record
byte provenance, stack preservation and rejection cases.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.local_type` returns the local's type, or `UnknownLocal` for an out-of-range index. -/
theorem code.local_type.spec (ctx : code.Context) (idx : U32) :
    code.local_type ctx idx ⦃ r =>
      match r with
      | .Ok t => ∃ hi : idx.val < ctx.locals.val.length, ctx.locals.val[idx.val] = t
      | .Err e => e = .UnknownLocal ∧ ctx.locals.val.length ≤ idx.val ⦄ := by
  unfold code.local_type
  step*

/-- `code.global_type` returns the global's type, or `UnknownGlobal` for an out-of-range index. -/
theorem code.global_type.spec (env : metadata.CodeMetadata) (idx : U32) :
    code.global_type env idx ⦃ r =>
      match r with
      | .Ok gt => ∃ hi : idx.val < env.globals.val.length, env.globals.val[idx.val].gtype = gt
      | .Err e => e = .UnknownGlobal ∧ env.globals.val.length ≤ idx.val ⦄ := by
  unfold code.global_type
  step*

/-- `code.take_local` decodes a local index with exact byte provenance and leaves both stacks
alone. It rejects with the LEB128 error or `UnknownLocal`. -/
theorem code.take_local.spec (st : code.OpIterState) (data : Slice U8) (ctx : code.Context) :
    code.take_local st data ctx ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok (idx, t) => Binary.Leb128.Decoded data st.pos idx r.2.pos ∧
          ∃ hi : idx.val < ctx.locals.val.length, ctx.locals.val[idx.val] = t
      | .Err e => (Binary.Leb128.Rejected data st.pos e ∧ r.2.pos = st.pos) ∨
          (e = .UnknownLocal ∧ ∃ idx, Binary.Leb128.Decoded data st.pos idx r.2.pos ∧
            ctx.locals.val.length ≤ idx.val) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases r with
  | Err e =>
      simp [code.take_local, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact Or.inl hp
  | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      obtain ⟨r, ht, htype⟩ := WP.spec_imp_exists (code.local_type.spec ctx idx)
      cases r with
      | Ok t =>
          simp [code.take_local, hr, ht, core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨hp, htype⟩
      | Err e =>
          simp [code.take_local, hr, ht, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact Or.inr ⟨htype.1, idx, hp, htype.2⟩

/-- `code.take_global` decodes a global index with exact byte provenance and leaves both stacks
alone. It rejects with the LEB128 error or `UnknownGlobal`. -/
theorem code.take_global.spec (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) :
    code.take_global st data env ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok (idx, gt) => Binary.Leb128.Decoded data st.pos idx r.2.pos ∧
          ∃ hi : idx.val < env.globals.val.length, env.globals.val[idx.val].gtype = gt
      | .Err e => (Binary.Leb128.Rejected data st.pos e ∧ r.2.pos = st.pos) ∨
          (e = .UnknownGlobal ∧ ∃ idx, Binary.Leb128.Decoded data st.pos idx r.2.pos ∧
            env.globals.val.length ≤ idx.val) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases r with
  | Err e =>
      simp [code.take_global, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact Or.inl hp
  | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      obtain ⟨r, ht, htype⟩ := WP.spec_imp_exists (code.global_type.spec env idx)
      cases r with
      | Ok gt =>
          simp [code.take_global, hr, ht, core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨hp, htype⟩
      | Err e =>
          simp [code.take_global, hr, ht, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact Or.inr ⟨htype.1, idx, hp, htype.2⟩

/-- `code.take_index` decodes an unsigned immediate with exact byte provenance and leaves both
stacks alone. -/
theorem code.take_index.spec (st : code.OpIterState) (data : Slice U8) :
    code.take_index st data ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok idx => Binary.Leb128.Decoded data st.pos idx r.2.pos
      | .Err e => Binary.Leb128.Rejected data st.pos e ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases r with
  | Err e =>
      simpa [code.take_index, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (show Binary.Leb128.Rejected data st.pos e from hp)
  | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      simpa [code.take_index, hr, core.result.Result.Insts.CoreOpsTry.branch] using (show Binary.Leb128.Decoded data st.pos idx next from hp)

/-- `code.read_reserved_zero` consumes one byte that is `0`, and otherwise rejects with
`UnexpectedEof` or `ReservedByteNotZero`. -/
theorem code.read_reserved_zero.spec (st : code.OpIterState) (data : Slice U8) :
    code.read_reserved_zero st data ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok _ => ∃ hp : st.pos.val < data.length,
          data.val[st.pos.val] = 0#u8 ∧ r.2.pos.val = st.pos.val + 1
      | .Err e => r.2 = st ∧
          ((e = .UnexpectedEof ∧ data.length ≤ st.pos.val) ∨
            (e = .ReservedByteNotZero ∧ ∃ hp : st.pos.val < data.length,
              data.val[st.pos.val] ≠ 0#u8)) ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    by_cases hz : data.val[st.pos.val] = 0#u8
    · simp [code.read_reserved_zero, hr, core.result.Result.Insts.CoreOpsTry.branch, hz]
      exact ⟨hp, hn⟩
    · have hzval : (data.val[st.pos.val]).val ≠ 0 := by scalar_tac
      simp [code.read_reserved_zero, hr, core.result.Result.Insts.CoreOpsTry.branch, hz, hzval]
      exact hp
  · have heof := reader.read_byte.eof data st.pos (by omega)
    simp [code.read_reserved_zero, heof, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    simpa using Nat.le_of_not_gt hp

/-- `code.require_memory` succeeds exactly when the environment has a memory. -/
theorem code.require_memory.spec (env : metadata.CodeMetadata) :
    code.require_memory env ⦃ r =>
      match r with
      | .Ok _ => 0 < env.memories.val.length
      | .Err e => e = .UnknownMemory ∧ env.memories.val = [] ⦄ := by
  unfold code.require_memory alloc.vec.Vec.is_empty
  step*
  all_goals simp_all
  exact List.length_pos_iff.mpr (by assumption)

/-- `code.read_memarg` decodes the alignment and offset together. A malformed offset leaves the
state unchanged, even after a successfully decoded alignment. -/
theorem code.read_memarg.spec (st : code.OpIterState) (data : Slice U8) :
    code.read_memarg st data ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok arg => ∃ middle, Binary.Leb128.Decoded data st.pos arg.align middle ∧
          Binary.Leb128.Decoded data middle arg.offset r.2.pos
      | .Err e => r.2 = st ∧ (Binary.Leb128.Rejected data st.pos e ∨
          ∃ align middle, Binary.Leb128.Decoded data st.pos align middle ∧ Binary.Leb128.Rejected data middle e) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases r with
  | Err e =>
      simp [code.read_memarg, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact Or.inl hp
  | Ok pair =>
      obtain ⟨align, middle⟩ := pair
      obtain ⟨r, hr', hp'⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data middle)
      cases r with
      | Err e =>
          simp [code.read_memarg, hr, hr', core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact Or.inr ⟨align, middle, hp, hp'⟩
      | Ok pair =>
          obtain ⟨offset, next⟩ := pair
          simp [code.read_memarg, hr, hr', core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨middle, hp, hp'⟩

/-- `code.check_memory_and_alignment` requires a memory and an alignment at most `natural`, and
rejects with `UnknownMemory` or `InvalidAlignment`. -/
theorem code.check_memory_and_alignment.spec (env : metadata.CodeMetadata) (arg : code.MemArg)
    (natural : U32) :
    code.check_memory_and_alignment env arg natural ⦃ r =>
      match r with
      | .Ok _ => 0 < env.memories.val.length ∧ arg.align.val ≤ natural.val
      | .Err e => (e = .UnknownMemory ∧ env.memories.val = []) ∨
          (e = .InvalidAlignment ∧ 0 < env.memories.val.length ∧ natural.val < arg.align.val) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.require_memory.spec env)
  cases r with
  | Err e =>
      simp [code.check_memory_and_alignment, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact Or.inl hp
  | Ok u =>
      simp only [code.check_memory_and_alignment, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      split <;> simp only [WP.spec_ok] <;> scalar_tac

end Itasca

end

end

/-! ## StackModel -/

section

/-!
# Internal validator stack model

Signature descriptors and polymorphic stack realizations support instruction
handler proofs. They do not define source validity or public resource budgets.
-/

/-! ## Body / Signatures -/

section BodySignatures

/-!
### Branch-target signatures

`resolve`, `inputs` and `outputs` interpret block signatures and table targets for public body relations.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- Logical list denoted by a descriptor; no such list is allocated by Rust. -/
def resolve (env : metadata.CodeMetadata) : signature.ResultType → Option (List wasm_types.ValueType)
  | .Empty => some []
  | .One t => some [t]
  | .Type index part => (env.types.val[index.val]?).map fun ft =>
      match part with
      | .Params => ft.params.val
      | .Results => ft.results.val

/-- The parameter descriptor of a block type. Only an indexed block type has parameters. -/
def inputs : signature.BlockType → signature.ResultType
  | .TypeIndex i => .Type i .Params
  | _ => .Empty

/-- The result descriptor of a block type. -/
def outputs : signature.BlockType → signature.ResultType
  | .Empty => .Empty
  | .Value t => .One t
  | .TypeIndex i => .Type i .Results

end Itasca.Body

end BodySignatures

/-! ## Body / Stack -/

section BodyStack

/-!
### Operand stack interpretation

Stack acceptance and realization relate concrete operand slots, including polymorphic
bottom values, to declarative value types. These predicates describe the common stack
vocabulary used by validation contracts.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Stack

/-- A concrete operand has its translated type, and a `Bot` operand has any type. -/
def Accepts : code.StackType → valtype → Prop
  | .Val t, t' => t' = Translation.valueType t
  | .Bot, _ => True

/-- A declarative stack `ts` realizes the validator stack `vals` of a frame. If the frame is
polymorphic (unreachable), `ts` may have an arbitrary prefix below the known operands. -/
def Realizes (polymorphic : Bool) (vals : List code.StackType) (ts : List valtype) : Prop :=
  ∃ front suffix, (polymorphic = false → front = []) ∧
    List.Forall₂ Accepts vals suffix ∧ ts = front ++ suffix

end Itasca.Body.Stack

end BodyStack

/-! ## Body / TypedPrefix -/

section BodyTypedPrefix

/-!
### Typed instruction prefixes

`TypedPrefix` and `ResumePrefix` relate the consumed instruction tree to the current operand/control state through continuation of the body loop.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- A frame starts with its parameter vector. Function bodies use the empty
vector because function parameters are locals, not initial operands. -/
structure TypedPrefix (C : context) (inputs : List valtype) (ops : List instr)
    (poly : Bool) (vals : List code.StackType) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Body.Stack.Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list inputs) (.mk_list ts))

/-- A suspended parent remembers the child's parameters and, for if, its i32
condition, even though those operands have been popped from the physical stack. -/
structure ResumePrefix (C : context) (inputs : List valtype) (ops : List instr)
    (poly : Bool) (vals : List code.StackType) (args : List valtype) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Body.Stack.Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list inputs) (.mk_list (ts ++ args)))

end Itasca.Body

end BodyTypedPrefix

end
