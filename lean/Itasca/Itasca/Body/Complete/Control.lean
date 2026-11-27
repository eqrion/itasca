import Itasca.Body.Complete.Frame
import Itasca.Body.SoundLoop
import Itasca.Binary.Body.Encoding
import Itasca.Body.NumericExt.Sound
import Itasca.Body.Scalar.Readers
import Itasca.Body.Control.BranchComplete
import Itasca.Body.Control.EnterSound
import Itasca.Body.Bulk.Complete
import Itasca.Body.Simd.Sound
import Itasca.Support.Translation
import Itasca.Body.References.Complete

/-!
Proofs for Body / Complete.

This module collects Control, LeafContracts.
Each section documents its contracts and consumers.
-/

/-! ## Control -/

section

/-!
Proofs for Body / Complete.

This module collects Leaf, Control.
Each section documents its contracts and consumers.
-/

/-! ## Leaf -/

section

namespace Itasca.CodeEntry

open Aeneas Aeneas.Std

/-- The shared signature-limit predicate gives the fixed parameter/result caps
used by leaf and structured-control completeness. -/
theorem FuncTypeWithinLimits.bounds {ft : wasm_types.FuncType}
    (bounded : FuncTypeWithinLimits ft) :
    ft.params.val.length ≤ 1000 ∧ ft.results.val.length ≤ 1000 := by
  simpa [FuncTypeWithinLimits, limits.MAX_MULTI_VALUE_PARAMS,
    limits.MAX_MULTI_VALUE_RESULTS] using bounded

end Itasca.CodeEntry

/-! ## Program -/

section

/-!
# Programs and atoms for completeness

`Program` says that every typed instruction list emitted from a token list in the Wasm 2.0 grammar
executes under the actual body loop within a concrete
control frame, and `AtomProgram` says the same for one normalized head instruction. `program_of_atoms` derives `Program` from `AtomProgram` by
induction on the token list, following an arbitrary declarative derivation (sequence, framing and
subsumption rules included).
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Completeness

/-- Execution of a typed instruction list within one concrete control frame. -/
def Program (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (tokens : List Token) (ops : List instr) : Prop :=
  ∀ (C : context) (st : code.BodyState) (f : Frame st) (next : Usize)
    (input output : List valtype),
    Translation.Environment.Matches env ctx C → Labels env st C →
    Bounds data st → Consumed data st.core.pos tokens next →
    Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands input →
    Instrs_ok C ops (.mk_functype (.mk_list input) (.mk_list output)) →
    Spec.DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops →
    ∃ s, BoundedExecution data env ctx index st s ∧ s.core.pos = next ∧ f.Output output s ∧
      Bounds data s

/-- The normalized head instruction has a primitive generated typing rule
and a preserved prefix on its operand stack. -/
def AtomProgram (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (tokens : List Token) (op : instr) : Prop :=
  ∀ (C : context) (st : code.BodyState) (f : Frame st) (next : Usize)
    (front input output : List valtype),
    Translation.Environment.Matches env ctx C → Labels env st C →
    Bounds data st → Consumed data st.core.pos tokens next →
    Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    Spec.DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op →
    ∃ s, BoundedExecution data env ctx index st s ∧ s.core.pos = next ∧
      f.Output (front ++ output) s ∧ Bounds data s

/-- `Program` holds for every emitted token list shorter than `n`. -/
def SmallerPrograms (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (n : Nat) : Prop :=
  ∀ tokens ops, tokens.length < n → Emits tokens ops → Program data env ctx index tokens ops

/-- Left-to-right execution follows a declarative derivation even when that
derivation uses arbitrary sequence, framing, and subsumption rules. The atom
obligation recursively receives only strictly smaller nested bodies. -/
theorem program_of_atoms (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (hatom : ∀ tokens op, Atom tokens op →
      SmallerPrograms data env ctx index tokens.length →
      AtomProgram data env ctx index tokens op)
    (tokens : List Token) (ops : List instr) (hemits : Emits tokens ops) :
    Program data env ctx index tokens ops := by
  generalize hn : tokens.length = n
  induction n using Nat.strong_induction_on generalizing tokens ops with
  | h n ih =>
    intro C st f next input output hmatch hlabels hbounds hbytes hreal htyped hdecl
    cases ops with
    | nil =>
      have hnil := Emits.empty_iff.mp hemits
      subst tokens
      have he := hbytes.empty_eq rfl
      subst next
      exact ⟨st, .nil st, rfl,
        f.output_self (Spec.Completeness.empty_realizes hreal htyped), hbounds⟩
    | cons op ops =>
      obtain ⟨first, rest, he, hfirst, hrest⟩ := Emits.cons_iff.mp hemits
      subst tokens
      have hfirst_len : first.length ≤ n := by simp only [List.length_append] at hn; omega
      have hrest_len : rest.length < n := by
        have hnonempty := hfirst.nonempty
        have hpos : 0 < first.length := List.length_pos_iff.mpr hnonempty
        simp only [List.length_append] at hn
        omega
      obtain ⟨middle, hfirstbytes, hrestbytes⟩ := hbytes.split
      obtain ⟨front, ins, outs, hop, hinput, htail⟩ :=
        Spec.Completeness.head_realizes hreal htyped
      have hsmaller : SmallerPrograms data env ctx index first.length := by
        intro ts es hlen he
        exact ih ts.length (by omega) ts es he rfl
      obtain ⟨mid, hrun, hpos, hout, hbound⟩ :=
        hatom first op hfirst hsmaller C st f middle front ins outs hmatch hlabels
          hbounds hfirstbytes hinput hop (Spec.DeclaredReferences.Instructions.cons_iff.mp hdecl).1
      obtain ⟨g, _, _, hgp, hgo, hgk, hgba, hgr⟩ := hout.next
      have hrestbytes' : Consumed data mid.core.pos rest next := by
        simpa [hpos] using hrestbytes
      have hlabels' : Labels env mid C := hout.labels hlabels
      obtain ⟨last, hrun', hpos', hout', hbound'⟩ :=
        ih rest.length hrest_len rest ops hrest rfl C mid g next _ _
          hmatch hlabels' hbound hrestbytes' hgr htail (Spec.DeclaredReferences.Instructions.cons_iff.mp hdecl).2
      exact ⟨last, hrun.append hrun', hpos',
        hout'.transfer hout.2 hgp hgo hgk hgba, hbound'⟩

end Itasca.Body.Completeness

end

/-! ## Leaf -/

section

/-!
# Leaf contracts and scalar completeness

`LeafContract` is the interface a leaf instruction family must meet: given an independent
encoding and a generated typing, `Body.step` accepts with a byte-weighted capacity bound.
`atom_of_leaf` turns a `LeafContract` into an `AtomProgram`. This file discharges the contract for
the scalar family (`Frame.scalar`, `scalar_leaf`, `scalar_atom`); `classify_plain` splits plain
instructions into scalar and control cases.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- Reads the opcode of an independent token encoding with the byte reader used by the Wasm 2.0
body loop. -/
theorem At.read_byte {data start token next} (h : At data start token next) :
    ∃ opcode pos immediate,
      reader.read_byte data start = .ok (.Ok (opcode, pos)) ∧
      pos.val = start.val + 1 ∧ Immediate opcode token immediate ∧
      Body.Scalar.BytesAt data pos immediate next ∧
      ∃ hp : start.val < data.length, data.val[start.val] = opcode := by
  have hb : start.val < data.length := by have := h.span; omega
  obtain ⟨_, hr, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data start hb)
  obtain ⟨opcode, imm, hi, ⟨hp, hbyte⟩, hs⟩ := h.immediate pos hpos
  exact ⟨opcode, pos, imm, by simpa [hbyte] using hr, hpos, hi, hs, hp, hbyte⟩

/-- The control cases of the leaf grammar are branches, `return` and calls. Structured control
(`block`, `loop`, `if`) is handled through `Token` in `Body/Complete/Body.Control`. -/
inductive ControlImmediate : U8 → instr → List U8 → Prop where
  | br (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      ControlImmediate 0x0C#u8 (.BR (.mk_uN idx.val)) bytes
  | brIf (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      ControlImmediate 0x0D#u8 (.BR_IF (.mk_uN idx.val)) bytes
  | brTable (indices : List U32) (default : U32) {count entries final} :
      Binary.Leb128.Encoding count indices.length → Body.Scalar.IndicesEncoding indices entries →
      Binary.Leb128.Encoding final default.val →
      ControlImmediate 0x0E#u8 (.BR_TABLE (indices.map (fun i => .mk_uN i.val)) (.mk_uN default.val))
        (count ++ entries ++ final)
  | return_ : ControlImmediate 0x0F#u8 .RETURN []
  | call (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      ControlImmediate 0x10#u8 (.CALL (.mk_uN idx.val)) bytes
  | callIndirect (idx : U32) {bytes} : Binary.Leb128.Encoding bytes idx.val →
      ControlImmediate 0x11#u8 (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val)) (bytes ++ [0#u8])

/-- Exhaustive scalar/control classification of the independent plain grammar. -/
theorem classify_plain {opcode op bytes} (h : Body.Scalar.Immediate opcode (.plain op) bytes) :
    opcode.val ∉ controlOpcodes ∨ ControlImmediate opcode op bytes := by
  cases h with
  | br idx he => exact .inr (.br idx he)
  | brIf idx he => exact .inr (.brIf idx he)
  | brTable ids fallback hc hi hf => exact .inr (.brTable ids fallback hc hi hf)
  | return_ => exact .inr .return_
  | call idx he => exact .inr (.call idx he)
  | callIndirect idx he => exact .inr (.callIndirect idx he)
  | memory opcode operation arg hmap ha ho =>
    left
    intro hm
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with he | he | he | he | he | he | he | he | he | he | he <;>
      simp [Body.MemoryMeaning.opcodeMeaning, he] at hmap
  | numericInstruction opcode source hmap =>
    rw [Body.Numeric.opcodeInstruction_eq] at hmap
    obtain ⟨operation, decoded, rfl⟩ := Option.map_eq_some_iff.mp hmap
    left
    have hb := Body.Numeric.NumericOp.bounds decoded
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  | _ => exact .inl (by decide)

end Itasca.Body

namespace Itasca.Body.Completeness

/-- Scalar dispatch accepts an independently encoded principal typing and
preserves the current block descriptor. The semantic return vector can
differ from the runtime scalar context's unused return vector. -/
theorem Frame.scalar {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx semantic : code.Context) (index : U32) (C : context)
    (opcode : U8) (op : instr) (bytes : List U8) (next : Usize)
    (front input output : List valtype)
    (hmatch : Translation.Environment.Matches env semantic C) (hlocals : ctx.locals = semantic.locals)
    (hscalar : opcode.val ∉ controlOpcodes) (hsize : st.core.vals.val.length < Usize.max)
    (hi : Body.Scalar.Immediate opcode (.plain op) bytes)
    (hb : Body.Scalar.BytesAt data st.core.pos bytes next)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧
      s.core.pos = next ∧ f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨out, hrun, hpos, hout, hlen⟩ := scalar_complete data env semantic C st.core f.core
    opcode op bytes next front input output hmatch hsize hscalar hi hb hr ht
  refine ⟨{st with core := out}, ?_, hpos, ⟨hout, ?_⟩, hlen⟩
  · rw [step.scalar_eq st data env ctx index opcode hscalar]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn, code.step_wasm2.base _ _ _ _ _ _ _ (scalar_excludes_extended_opcodes hi),
      code.step_extended.base _ _ _ _ _ _ _ (scalar_excludes_numeric_extensions hi).1 (scalar_excludes_numeric_extensions hi).2,
      scalar_context _ st.core data env ctx semantic opcode () hscalar hlocals, hrun]
    simp
  · obtain ⟨poly, operands, hctrls, _, _⟩ := hout
    simp [hctrls, f.core.ctrls]

/-- A leaf contract uses a principal generated typing and an independent
Wasm 2.0 immediate encoding.
Growth is bounded by the full token's encoded byte count. -/
def LeafContract (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) : Prop :=
  ∀ (C : context) (st : code.BodyState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype),
    Translation.Environment.Matches env ctx C → Labels env st C →
    st.core.vals.val.length + 1000 < Usize.max →
    Immediate opcode (.plain op) bytes → Body.Scalar.BytesAt data st.core.pos bytes next →
    Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    Spec.DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op →
    ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (bytes.length + 1)

/-- Reading the opcode and running a leaf contract produces an actual execution
and preserves the byte-weighted capacity bound for the surrounding program. -/
theorem atom_of_leaf (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (hstep : LeafContract data env ctx index) (op : instr) :
    AtomProgram data env ctx index [.plain op] op := by
  intro C st f next front input output hmatch hlabels hbounds hbytes hreal htyped hdecl
  have hat := hbytes.single
  obtain ⟨opcode, pos, bytes, hread, hpos, himmediate, hspan, hp, hbyte⟩ := hat.read_byte
  let decoded : code.BodyState := {st with core := {st.core with pos := pos}}
  let g : Frame decoded :=
    ⟨⟨f.core.parents, f.core.current, f.core.outer, f.core.operands,
      f.core.ctrls, f.core.vals, f.core.base⟩, f.parents, f.current, f.blocks, f.aligned⟩
  have hcap : decoded.core.vals.val.length + 1000 < Usize.max := hbounds.val_capacity
  obtain ⟨s, hrun, hcursor, hout, hlen⟩ :=
    hstep C decoded g opcode op bytes next front input output hmatch hlabels hcap
      himmediate hspan hreal htyped hdecl
  have hout' : f.Output (front ++ output) s := hout
  refine ⟨s, .single hbounds f.nonempty hread hrun, hcursor, hout', ?_⟩
  apply bounds_after hbounds hat hcursor
  · have hlenbytes : bytes.length + 1 = next.val - st.core.pos.val := by
      have := hspan.length
      omega
    simpa [decoded, hlenbytes] using hlen
  · have hb := hout'.2
    simp [hb]

/-- The scalar family discharges the shared leaf growth contract. -/
theorem scalar_leaf (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (C : context) (st : code.BodyState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : Translation.Environment.Matches env ctx C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes)
    (hi : Body.Scalar.Immediate opcode (.plain op) bytes) (hb : Body.Scalar.BytesAt data st.core.pos bytes next)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (bytes.length + 1) := by
  obtain ⟨s, hs, hp, ho, hl⟩ := f.scalar data env ctx ctx index C opcode op bytes next front input output
    hmatch rfl hscalar (by omega) hi hb hr ht
  exact ⟨s, hs, hp, ho, by omega⟩

end Itasca.Body.Completeness

end

end

/-! ## Control -/

section

/-!
# Completeness of structured control

Executes `block`, `loop` and `if` (with and without `else`) from independent encodings and
generated typing. `execute_enter`, `execute_else` and `execute_end` run the delimiters,
`execute_body` and `run_closed_child` run nested bodies with the parent frame suspended, and
`atom_block`, `atom_loop`, `atom_if_end` and `atom_if_else` yield an `AtomProgram` for each form.
`blocktype_signature` and `labels_push` connect block descriptors to the SpecTec label context.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Completeness

theorem blocktype_signature {env : metadata.Env} {ctx : code.Context} {C : context}
    (hm : Translation.Environment.Matches env ctx C) (bt : signature.BlockType) {input output : List valtype}
    (h : Blocktype_ok C (blockType bt) (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ ins outs, resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs ∧
      input = ins.map Translation.valueType ∧ output = outs.map Translation.valueType := by
  cases bt with
  | Empty => cases h; exact ⟨[], [], rfl, rfl, rfl, rfl⟩
  | Value t => cases h; exact ⟨[], [t], rfl, rfl, rfl, rfl⟩
  | TypeIndex index =>
    cases h with
    | typeidx _ _ _ hi he _ _ =>
      have hib : index.val < env.types.val.length := by simpa [hm.types, proj_uN_0] using hi
      have he' : Translation.Environment.funcType env.types.val[index.val] =
          .mk_functype (.mk_list input) (.mk_list output) := by
        simpa [hm.types, proj_uN_0, getElem!_pos, List.getElem_map, List.getElem?_eq_getElem hib] using he
      have hie : input = env.types.val[index.val].params.val.map Translation.valueType := by
        simpa [Translation.Environment.funcType] using congrArg (fun t => match t with | .mk_functype (.mk_list a) _ => a) he'.symm
      have hoe : output = env.types.val[index.val].results.val.map Translation.valueType := by
        simpa [Translation.Environment.funcType] using congrArg (fun t => match t with | .mk_functype _ (.mk_list a) => a) he'.symm
      exact ⟨_, _, by simp [resolve, inputs, hib], by simp [resolve, outputs, hib], hie, hoe⟩

theorem signature_limits {env : metadata.Env} (limits : CodeEntry.EnvironmentWithinLimits env)
    (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs) :
    ins.length ≤ 1000 ∧ outs.length ≤ 1000 := by
  cases bt with
  | Empty => simp [inputs, outputs, resolve] at hin hout; simp_all
  | Value t => simp [inputs, outputs, resolve] at hin hout; subst ins; subst outs; simp
  | TypeIndex index =>
    have hi : index.val < env.types.val.length := by
      by_contra he; simp [inputs, resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hin
    have h := (limits.types _ (List.getElem_mem hi)).bounds
    simp [inputs, outputs, resolve, List.getElem?_eq_getElem hi] at hin hout
    simpa [← hin, ← hout] using h

theorem labels_push {env : metadata.Env} {C : context} {st s : code.BodyState}
    (hl : Labels env st C) (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (frame : code.Ctrl) (bt : signature.BlockType) (ts : List wasm_types.ValueType)
    (hc : s.core.ctrls.val = st.core.ctrls.val ++ [frame])
    (hb : s.blocks.val = st.blocks.val ++ [bt])
    (ht : resolve env (target frame.kind bt) = some ts) :
    Labels env s (Body.Control.labelContext (ts.map Translation.valueType) ++ C) := by
  intro depth
  cases depth with
  | zero => simp [Body.Control.label_context_labels, labelTypes, labelAt, hc, hb, ht]
  | succ depth =>
    rw [Body.Control.label_context_labels]
    simp only [List.getElem?_cons_succ, hl depth]
    unfold labelTypes labelAt
    by_cases hd : depth < st.blocks.val.length
    · have hs : depth + 1 < (st.blocks.val ++ [bt]).length := by simp; omega
      have he : (st.blocks.val ++ [bt]).length - 1 - (depth + 1) = st.blocks.val.length - 1 - depth := by simp; omega
      have hbnd : st.blocks.val.length - 1 - depth < st.blocks.val.length := by omega
      have he' : st.blocks.val.length - (depth + 1) = st.blocks.val.length - 1 - depth := by omega
      simp only [code.BodyState.blocks_length] at hd hs he hbnd he'
      simp [hb, hc, hd, he', hbnd, List.getElem?_append]
    · have hs : ¬ depth + 1 < (st.blocks.val ++ [bt]).length := by simp; omega
      simp only [code.BodyState.blocks_length] at hd
      simp [hb, hd]

/-- A delimiter execution, with exact effects and no post-delimiter capacity
estimate; callers derive bounds from the enclosing entry. -/
theorem execute_end {st : code.BodyState} (f : Frame st) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (next : Usize)
    (ins outs : List wasm_types.ValueType) (bound : Bounds data st)
    (hat : At data st.core.pos .end_ next)
    (hin : resolve env (inputs f.current) = some ins) (hout : resolve env (outputs f.current) = some outs)
    (hthen : f.core.current.kind = .Then → ins = outs)
    (ht : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (outs.map Translation.valueType))
    (hcap : f.core.outer.length + outs.length ≤ Usize.max) :
    ∃ s, BoundedExecution data env ctx index st s ∧ s.core.pos = next ∧
      s.core.ctrls.val = f.core.parents ∧ s.blocks.val = f.parents ∧
      s.core.vals.val = if f.parents = [] then f.core.outer else f.core.outer ++ outs.map code.StackType.Val := by
  have hs := hat.span
  have hinbounds : st.core.pos.val < data.length := by omega
  obtain ⟨_, hread, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hinbounds)
  obtain ⟨opcode, bytes, himm, ⟨_, hbyte⟩, hspan⟩ := hat.immediate pos hpos
  cases himm
  have hnext := hspan.empty
  obtain ⟨⟨r, s⟩, hr, hok, hp, hc, hb, hv⟩ := WP.spec_imp_exists
    (code.end_frame.complete { st with core := { st.core with pos := pos } } env false
      f.core.parents f.parents f.core.current f.current ins outs f.core.outer f.core.operands
      f.core.ctrls f.blocks f.aligned f.core.vals f.core.base hin hout ht hthen hcap)
  dsimp only at hok
  subst r
  have hstep : step { st with core := { st.core with pos := pos } } data env ctx index 0x0B#u8 =
      .ok (.Ok (), s) := by simpa [step] using hr
  exact ⟨s, .single bound f.nonempty (by simpa [hbyte] using hread)
    hstep,
    hp.trans hnext.symm, hc, hb, hv⟩

theorem execute_else {st : code.BodyState} (f : Frame st) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (next : Usize)
    (ins outs : List wasm_types.ValueType) (bound : Bounds data st)
    (hat : At data st.core.pos .else_ next)
    (hin : resolve env (inputs f.current) = some ins) (hout : resolve env (outputs f.current) = some outs)
    (hthen : f.core.current.kind = .Then)
    (ht : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (outs.map Translation.valueType))
    (hcap : f.core.outer.length + ins.length ≤ Usize.max) :
    ∃ s, BoundedExecution data env ctx index st s ∧ s.core.pos = next ∧
      s.core.ctrls.val = f.core.parents ++ [{ f.core.current with kind := .Else, polymorphic_base := false }] ∧
      s.blocks = st.blocks ∧ s.core.vals.val = f.core.outer ++ ins.map code.StackType.Val := by
  have hs := hat.span
  have hinbounds : st.core.pos.val < data.length := by omega
  obtain ⟨_, hread, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hinbounds)
  obtain ⟨opcode, bytes, himm, ⟨_, hbyte⟩, hspan⟩ := hat.immediate pos hpos
  cases himm
  have hnext := hspan.empty
  obtain ⟨⟨r, s⟩, hr, hok, hp, hc, hb, hv⟩ := WP.spec_imp_exists
    (code.end_frame.complete { st with core := { st.core with pos := pos } } env true
      f.core.parents f.parents f.core.current f.current ins outs f.core.outer f.core.operands
      f.core.ctrls f.blocks f.aligned f.core.vals f.core.base hin hout ht hthen hcap)
  dsimp only at hok
  subst r
  have hstep : step { st with core := { st.core with pos := pos } } data env ctx index 0x05#u8 =
      .ok (.Ok (), s) := by simpa [step] using hr
  exact ⟨s, .single bound f.nonempty (by simpa [hbyte] using hread)
    hstep,
    hp.trans hnext.symm, hc, hb, hv⟩

theorem execute_enter {st : code.BodyState} (f : Frame st) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (next : Usize)
    (form : Frames.Form) (initial : form.Initial) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (front : List valtype)
    (limits : CodeEntry.EnvironmentWithinLimits env) (hb : Bounds data st)
    (hat : At data st.core.pos (form.token bt) next)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (ht : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ form.args ins)) :
    ∃ s, BoundedExecution data env ctx index st s ∧ s.core.pos = next ∧
      EnterForward st s form bt ins outs f.core.outer f.core.operands front ∧ Bounds data s := by
  have hs := hat.span
  have hinbounds : st.core.pos.val < data.length := by omega
  obtain ⟨_, hread, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hinbounds)
  obtain ⟨opcode, bytes, himm, ⟨_, hbyte⟩, hspan⟩ := hat.immediate pos hpos
  have hop : opcode = form.opcode ∧ BlockEncoding bt bytes := by
    rcases initial with rfl | rfl | rfl <;> cases himm <;> exact ⟨rfl, by assumption⟩
  have hd : BlockDecoded data pos bt next := block_decoded_iff.mpr ⟨bytes, hop.2, hspan⟩
  obtain ⟨hins, houts⟩ := signature_limits limits bt ins outs hin hout
  obtain ⟨⟨r, s⟩, hr, hok, hp, heffect⟩ := WP.spec_imp_exists
    (code.enter.complete { st with core := { st.core with pos := pos } } data env form initial
      bt next ins outs f.core.outer f.core.operands front hd hin hout hins houts f.core.vals
      f.core.base_eq hb.ctrl_capacity
      (by change st.core.vals.val.length + ins.length ≤ Usize.max; have := hb.val_capacity; omega) (by simpa [Body.Control.polymorphic, f.core.ctrls] using ht))
  dsimp only at hok
  subst r
  have hstep : step { st with core := { st.core with pos := pos } } data env ctx index opcode =
      .ok (.Ok (), s) := by
    rw [hop.1]
    rcases initial with rfl | rfl | rfl <;> simpa [step, Frames.Form.opcode, Frames.Form.kind] using hr
  refine ⟨s, .single hb f.nonempty (by simpa [hbyte] using hread) hstep, hp, heffect, ?_⟩
  obtain ⟨remaining, base, hlen, hbase, hreal, hctrls, hblocks, hvals⟩ := heffect
  apply bounds_after hb hat hp
  · have htwo := hd.span.1
    have hstart : st.core.pos.val + 2 ≤ next.val := by omega
    simp only [hvals, f.core.vals, List.length_append, List.length_map]
    omega
  · simp [hblocks]

private theorem restore_bounds {data : Slice U8} {st s : code.BodyState}
    (hb : Bounds data st) (hp : st.core.pos.val ≤ s.core.pos.val) (hpos : s.core.pos.val ≤ data.length)
    (hv : s.core.vals.val.length ≤ st.core.vals.val.length)
    (hc : s.blocks.val.length ≤ st.blocks.val.length) : Bounds data s := by
  have := hb.vals; have := hb.ctrls
  exact ⟨hb.size, hpos, by omega, by omega⟩

/-- Execute a child list and its end, preserving the original suspended
parent stack and result descriptor. -/
theorem execute_body {data : Slice U8} {env : metadata.Env}
    {ctx : code.Context} {index : U32} {tokens : List Token} {ops : List instr}
    (program : Program data env ctx index tokens ops) (C : context)
    (st : code.BodyState) (f : Frame st) (next : Usize)
    (ins outs : List wasm_types.ValueType)
    (hm : Translation.Environment.Matches env ctx C) (hl : Labels env st C)
    (hb : Bounds data st)
    (hbytes : Consumed data st.core.pos (tokens ++ [Token.end_]) next)
    (hin : resolve env (inputs f.current) = some ins) (hout : resolve env (outputs f.current) = some outs)
    (ht : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (ins.map Translation.valueType))
    (hbody : Instrs_ok C ops (.mk_functype (.mk_list (ins.map Translation.valueType))
      (.mk_list (outs.map Translation.valueType))))
    (hthen : f.core.current.kind = .Then → ins = outs)
    (hcap : f.core.outer.length + outs.length ≤ Usize.max)
    (hdecl : Spec.DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops) :
    ∃ s, BoundedExecution data env ctx index st s ∧ s.core.pos = next ∧
      s.core.ctrls.val = f.core.parents ∧ s.blocks.val = f.parents ∧
      s.core.vals.val = if f.parents = [] then f.core.outer else f.core.outer ++ outs.map code.StackType.Val := by
  obtain ⟨middle, hinner, hend⟩ := hbytes.split
  obtain ⟨mid, hrun, hpos, hout', hbounds⟩ :=
    program C st f middle _ _ hm hl hb hinner ht hbody hdecl
  obtain ⟨g, hgp, hgc, hp, ho, hk, hbase, hreal⟩ := hout'.next
  obtain ⟨s, hclose, hp', hc', hb', hv'⟩ := execute_end g data env ctx index next ins outs hbounds
    (by simpa [hpos] using hend.single) (by simpa [hgc] using hin) (by simpa [hgc] using hout)
    (by simpa [hk] using hthen) hreal (by simpa [ho] using hcap)
  exact ⟨s, hrun.append hclose, hp', by simpa [hp] using hc', by simpa [hgp] using hb',
    by simpa [hgp, ho] using hv'⟩

private theorem concrete_realizes (ts : List wasm_types.ValueType) :
    Body.Stack.Realizes false (ts.map code.StackType.Val) (ts.map Translation.valueType) := by
  apply (Body.Stack.realizes_append_concrete false [] ts _).mpr
  exact ⟨[], by simp [Body.Stack.Realizes], rfl⟩

private theorem resume_parent {st s : code.BodyState} (f : Frame st)
    (remaining : List code.StackType) (front : List valtype) (outs : List wasm_types.ValueType)
    (hreal : Body.Stack.Realizes f.core.current.polymorphic_base remaining front)
    (hc : s.core.ctrls.val = st.core.ctrls.val) (hb : s.blocks.val = st.blocks.val)
    (hv : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val) :
    f.Output (front ++ outs.map Translation.valueType) s := by
  constructor
  · apply f.core.output_of_same_ctrls (alloc.vec.Vec.ext _ _ hc)
      (operands := remaining ++ outs.map code.StackType.Val) (by simpa [List.append_assoc] using hv)
    apply (Body.Stack.realizes_append_concrete _ _ _ _).mpr
    exact ⟨front, by simpa [f.core.poly_eq] using hreal, rfl⟩
  · exact alloc.vec.Vec.ext _ _ hb

private theorem closed_bounds {data : Slice U8} {st s : code.BodyState}
    (f : Frame st) (hb : Bounds data st) (next : Usize)
    (remaining : List code.StackType) (outs : List wasm_types.ValueType)
    (hp : s.core.pos = next) (hend : next.val ≤ data.length)
    (hlen : st.core.pos.val + 2 ≤ next.val) (hrem : remaining.length ≤ f.core.operands.length)
    (houts : outs.length ≤ 1000) (hblocks : s.blocks.val = st.blocks.val)
    (hvals : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val) :
    Bounds data s := by
  have hv := hb.vals; have hc := hb.ctrls
  rw [f.core.vals, List.length_append] at hv
  refine ⟨hb.size, by simpa [hp] using hend, ?_, ?_⟩
  · rw [hp, hvals, List.length_append, List.length_append, List.length_map]
    omega
  · simp only [hp, hblocks]; omega

/-- Common structured execution for blocks, loops, and omitted-else ifs. -/
theorem run_closed_child {data : Slice U8} {env : metadata.Env}
    {ctx : code.Context} {index : U32}
    (limits : CodeEntry.EnvironmentWithinLimits env) (form : Frames.Form) (initial : form.Initial)
    (bt : signature.BlockType) (tokens : List Token) (ops : List instr)
    (program : Program data env ctx index tokens ops)
    (C : context) (st : code.BodyState) (f : Frame st) (next : Usize)
    (front : List valtype) (ins outs : List wasm_types.ValueType)
    (hm : Translation.Environment.Matches env ctx C) (hl : Labels env st C) (hb : Bounds data st)
    (hbytes : Consumed data st.core.pos ([form.token bt] ++ tokens ++ [Token.end_]) next)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (ht : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ form.args ins))
    (hbody : Instrs_ok (Frames.enter C form ins outs) ops
      (.mk_functype (.mk_list (ins.map Translation.valueType)) (.mk_list (outs.map Translation.valueType))))
    (hthen : form = .then_ → ins = outs)
    (hdecl : Spec.DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops) :
    ∃ s, BoundedExecution data env ctx index st s ∧ s.core.pos = next ∧
      f.Output (front ++ outs.map Translation.valueType) s ∧ Bounds data s := by
  obtain ⟨header, hheadc, hrest⟩ :=
    (show Consumed data st.core.pos ([form.token bt] ++ (tokens ++ [Token.end_])) next by
      simpa [List.append_assoc] using hbytes).split
  have hhead := hheadc.single
  obtain ⟨entered, henter, hpos, heffect, hbounds⟩ :=
    execute_enter f data env ctx index header form initial bt ins outs front limits hb hhead
      hin hout ht
  obtain ⟨remaining, base, hlen, hbase, hreal, hc, hblocks, hv⟩ := heffect
  let child : Frame entered :=
    ⟨⟨st.core.ctrls.val, (Frames.Saved.fresh base form bt ins outs).ctrl,
      f.core.outer ++ remaining, ins.map code.StackType.Val, hc, hv, by
        simpa [Frames.Saved.fresh] using hbase⟩,
      st.blocks.val, bt, hblocks, by simp [f.blocks, f.core.ctrls, f.aligned]⟩
  have hlabel : Labels env entered (Frames.enter C form ins outs) := by
    rcases initial with rfl | rfl | rfl
    · exact labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        (Frames.Saved.fresh base .block bt ins outs).ctrl bt outs hc hblocks hout
    · exact labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        (Frames.Saved.fresh base .loop bt ins outs).ctrl bt ins hc hblocks hin
    · exact labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        (Frames.Saved.fresh base .then_ bt ins outs).ctrl bt outs hc hblocks hout
  have hcap : (f.core.outer ++ remaining).length + outs.length ≤ Usize.max := by
    have hlimits := signature_limits limits bt ins outs hin hout
    have hvCap := hb.val_capacity
    rw [f.core.vals, List.length_append] at hvCap
    simp only [List.length_append]
    omega
  obtain ⟨s, hrun, hp', hc', hb', hv'⟩ := execute_body program _ entered child next ins outs
    (hm.enter _) hlabel hbounds (by simpa [hpos] using hrest) hin hout
    (concrete_realizes ins) hbody (by
      intro he
      apply hthen
      rcases initial with rfl | rfl | rfl <;> simp_all [child, Frames.Saved.fresh, Frames.Form.kind]) hcap hdecl
  have hvals : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val := by
    have hne : st.core.ctrls.val ≠ [] := by simpa using f.nonempty
    simpa [child, hne] using hv'
  refine ⟨s, henter.append hrun, hp', resume_parent f remaining front outs
    (by simpa [f.core.poly_eq] using hreal) hc' hb' hvals, ?_⟩
  apply closed_bounds f hb next remaining outs hp' hbytes.span.2 _ hlen
    (signature_limits limits bt ins outs hin hout).2 hb' hvals
  have hfirst := hhead.span.1
  have hlast : header.val < next.val := by
    obtain ⟨middle, hi, he⟩ := hrest.split
    have hfinal := he.single.span.1
    have hmid := hi.span.1
    omega
  omega

theorem empty_identity {C : context} (ins outs : List wasm_types.ValueType)
    (h : Instrs_ok C [] (.mk_functype (.mk_list (ins.map Translation.valueType))
      (.mk_list (outs.map Translation.valueType)))) : ins = outs := by
  have hreal := Spec.Completeness.empty_realizes (concrete_realizes ins) h
  obtain ⟨pre, hp, he⟩ := (Body.Stack.realizes_append_concrete false [] ins _).mp hreal
  have hp' := (Body.Stack.realizes_empty _).mp hp
  have hm : ins.map Translation.valueType = outs.map Translation.valueType := by simpa [hp'] using he.symm
  clear h hreal he hp hp' pre
  induction ins generalizing outs with
  | nil => cases outs <;> simp_all
  | cons i ins ih =>
    cases outs with
    | nil => simp at hm
    | cons o outs =>
      have hs := List.cons.inj hm
      have hio := Translation.value_type_injective hs.1
      simp [hio, ih outs hs.2]

theorem atom_block {data : Slice U8} {env : metadata.Env}
    {ctx : code.Context} {index : U32}
    (limits : CodeEntry.EnvironmentWithinLimits env) (bt : signature.BlockType)
    {tokens : List Token} {ops : List instr} (he : Emits tokens ops)
    (smaller : SmallerPrograms data env ctx index
      ([Token.block bt] ++ tokens ++ [Token.end_]).length) :
    AtomProgram data env ctx index ([.block bt] ++ tokens ++ [Token.end_])
      (.BLOCK (blockType bt) ops) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hdecl
  cases htyped with
  | block _ _ _ input output hbt hbody _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    exact run_closed_child limits .block (Or.inl rfl) bt tokens ops (smaller tokens ops (by simp) he)
      C st f next front ins outs hm hl hb hbytes hin hout (by simpa [Frames.Form.args] using ht)
      hbody (by simp) hdecl

theorem atom_loop {data : Slice U8} {env : metadata.Env}
    {ctx : code.Context} {index : U32}
    (limits : CodeEntry.EnvironmentWithinLimits env) (bt : signature.BlockType)
    {tokens : List Token} {ops : List instr} (he : Emits tokens ops)
    (smaller : SmallerPrograms data env ctx index
      ([Token.loop bt] ++ tokens ++ [Token.end_]).length) :
    AtomProgram data env ctx index ([.loop bt] ++ tokens ++ [Token.end_])
      (.LOOP (blockType bt) ops) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hdecl
  cases htyped with
  | loop _ _ _ input output hbt hbody _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    exact run_closed_child limits .loop (Or.inr (Or.inl rfl)) bt tokens ops (smaller tokens ops (by simp) he)
      C st f next front ins outs hm hl hb hbytes hin hout (by simpa [Frames.Form.args] using ht)
      hbody (by simp) hdecl

theorem atom_if_end {data : Slice U8} {env : metadata.Env}
    {ctx : code.Context} {index : U32}
    (limits : CodeEntry.EnvironmentWithinLimits env) (bt : signature.BlockType)
    {tokens : List Token} {ops : List instr} (he : Emits tokens ops)
    (smaller : SmallerPrograms data env ctx index
      ([Token.if_ bt] ++ tokens ++ [Token.end_]).length) :
    AtomProgram data env ctx index ([.if_ bt] ++ tokens ++ [Token.end_])
      (.IFELSE (blockType bt) ops []) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hdecl
  cases htyped with
  | «if» _ _ _ _ input output hbt hbody hempty _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    exact run_closed_child limits .then_ (Or.inr (Or.inr rfl)) bt tokens ops (smaller tokens ops (by simp) he)
      C st f next front ins outs hm hl hb hbytes hin hout ht hbody (fun _ => empty_identity ins outs hempty)
      (Spec.DeclaredReferences.Instruction.if_else_iff.mp hdecl).1

theorem atom_if_else {data : Slice U8} {env : metadata.Env}
    {ctx : code.Context} {index : U32}
    (limits : CodeEntry.EnvironmentWithinLimits env) (bt : signature.BlockType)
    {yesTokens noTokens : List Token} {yes no : List instr}
    (hyes : Emits yesTokens yes) (hno : Emits noTokens no)
    (smaller : SmallerPrograms data env ctx index
      ([Token.if_ bt] ++ yesTokens ++ [Token.else_] ++ noTokens ++ [Token.end_]).length) :
    AtomProgram data env ctx index ([.if_ bt] ++ yesTokens ++ [.else_] ++ noTokens ++ [.end_])
      (.IFELSE (blockType bt) yes no) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hdecl
  cases htyped with
  | «if» _ _ _ _ input output hbt hyesBody hnoBody _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    obtain ⟨header, hheadc, hrest⟩ :=
      (show Consumed data st.core.pos
          ([.if_ bt] ++ (yesTokens ++ [.else_] ++ noTokens ++ [.end_])) next by
        simpa [List.append_assoc] using hbytes).split
    have hhead := hheadc.single
    obtain ⟨entered, henter, hpos, heffect, hbounds⟩ :=
      execute_enter f data env ctx index header .then_ (Or.inr (Or.inr rfl)) bt ins outs front
        limits hb hhead hin hout ht
    obtain ⟨remaining, base, hlen, hbase, hreal, hc, hblocks, hv⟩ := heffect
    let child : Frame entered :=
      ⟨⟨st.core.ctrls.val, (Frames.Saved.fresh base .then_ bt ins outs).ctrl,
        f.core.outer ++ remaining, ins.map code.StackType.Val, hc, hv, by
          simpa [Frames.Saved.fresh] using hbase⟩,
        st.blocks.val, bt, hblocks, by simp [f.blocks, f.core.ctrls, f.aligned]⟩
    have hlabel : Labels env entered (Frames.enter C .then_ ins outs) :=
      labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        child.core.current bt outs hc hblocks hout
    obtain ⟨yesEnd, hybytes, hnbytes⟩ := Consumed.split
      (show Consumed data entered.core.pos
          (yesTokens ++ ([.else_] ++ noTokens ++ [.end_])) next by
        simpa [hpos, List.append_assoc] using hrest)
    obtain ⟨yesState, hyesRun, hyesPos, hyesOut, hyesBounds⟩ :=
      smaller yesTokens yes (by simp) hyes _ entered child yesEnd
        (ins.map Translation.valueType) (outs.map Translation.valueType) (hm.enter _) hlabel hbounds
        hybytes (concrete_realizes ins) hyesBody (Spec.DeclaredReferences.Instruction.if_else_iff.mp hdecl).1
    obtain ⟨yesPoly, yesOperands, hyc, hyv, hyr⟩ := hyesOut.1
    let yesFrame : Frame yesState :=
      ⟨⟨child.core.parents, {child.core.current with polymorphic_base := yesPoly},
        child.core.outer, yesOperands, hyc, hyv, child.core.base⟩,
        child.parents, child.current, by rw [hyesOut.2]; exact child.blocks, child.aligned⟩
    obtain ⟨elseStart, hatElsec, hnoBytes⟩ := Consumed.split
      (show Consumed data yesState.core.pos ([.else_] ++ (noTokens ++ [.end_])) next by
        simpa [hyesPos, List.append_assoc] using hnbytes)
    have hatElse := hatElsec.single
    have hcapIns : (f.core.outer ++ remaining).length + ins.length ≤ Usize.max := by
      have hvc := entered.core.vals.property
      simpa [hv, List.length_append, List.length_map, Nat.add_assoc] using hvc
    have hcapOuts : (f.core.outer ++ remaining).length + outs.length ≤ Usize.max := by
      have hlimits := signature_limits limits bt ins outs hin hout
      have hvc := hb.val_capacity
      rw [f.core.vals, List.length_append] at hvc
      simp only [List.length_append]; omega
    obtain ⟨elseState, helseRun, helsePos, hec, heb, hev⟩ :=
      execute_else yesFrame data env ctx index elseStart ins outs hyesBounds hatElse hin hout rfl hyr hcapIns
    let elseFrame : Frame elseState :=
      ⟨⟨yesFrame.core.parents, {yesFrame.core.current with kind := .Else, polymorphic_base := false},
        yesFrame.core.outer, ins.map code.StackType.Val, hec, hev, yesFrame.core.base⟩,
        yesFrame.parents, yesFrame.current, by rw [heb]; exact yesFrame.blocks, yesFrame.aligned⟩
    have hlabelElse : Labels env elseState (Frames.enter C .then_ ins outs) := by
      apply labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        elseFrame.core.current bt outs hec _ hout
      rw [heb, hyesOut.2]
      exact hblocks
    have heBounds : Bounds data elseState := by
      refine restore_bounds hbounds ?_ (by rw [helsePos]; exact hatElse.span.2) ?_ ?_
      · have hh := hybytes.span.1
        have he := hatElse.span.1
        rw [helsePos]
        rw [hyesPos] at he
        omega
      · simp [hev, yesFrame, child, hv]
      · simp [heb, hyesOut.2]
    obtain ⟨s, hnoRun, hp', hc', hb', hv'⟩ := execute_body
      (smaller noTokens no (by simp; omega) hno) _ elseState elseFrame next ins outs
      (hm.enter _) hlabelElse heBounds (by simpa [helsePos] using hnoBytes) hin hout
      (concrete_realizes ins) hnoBody (by simp [elseFrame]) hcapOuts (Spec.DeclaredReferences.Instruction.if_else_iff.mp hdecl).2
    have hvals : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val := by
      have hne : st.core.ctrls.val ≠ [] := by simpa using f.nonempty
      simpa [elseFrame, yesFrame, child, hne] using hv'
    refine ⟨s, ((henter.append hyesRun).append helseRun).append hnoRun, hp',
      resume_parent f remaining front outs (by simpa [f.core.poly_eq] using hreal) hc' hb' hvals, ?_⟩
    apply closed_bounds f hb next remaining outs hp' hbytes.span.2 _ hlen
      (signature_limits limits bt ins outs hin hout).2 hb' hvals
    have hf := hhead.span.1
    have hrest' := hnbytes.span.2
    have hy := hybytes.span.1
    have hel := hatElse.span.1
    rw [hyesPos] at hel
    have hn := hnoBytes.span.1
    rw [hpos] at hy
    omega

end Itasca.Body.Completeness

end

end

/-! ## LeafContracts -/

section

/-!
# Leaf contracts for every plain instruction

Proves `LeafContract` for control leaves (`Frame.call`, `Frame.call_indirect`, `Frame.branch`,
`Frame.branch_if`, `Frame.return_`, `Frame.branch_table`), reference leaves and bulk leaves, and
combines them with the scalar, sign extension, saturating and SIMD families in `leaf_contract`.
The result covers every plain instruction of the independent Wasm 2.0 grammar.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

theorem _root_.Itasca.CodeEntry.EnvironmentWithinLimits.resolve_bound {env} (h : CodeEntry.EnvironmentWithinLimits env)
    (view : signature.ResultType) (ts : List wasm_types.ValueType) (ht : resolve env view = some ts) :
    ts.length ≤ 1000 := by
  cases view with
  | Empty => simp [resolve] at ht; subst ts; simp
  | One t => simp [resolve] at ht; subst ts; simp
  | «Type» idx part =>
    cases hi : env.types.val[idx.val]? with
    | none => simp [resolve, hi] at ht
    | some ft =>
      have hm : ft ∈ env.types.val := List.mem_of_getElem? hi
      cases part <;> simp [resolve, hi] at ht <;> subst ts
      · exact (h.types ft hm).bounds.1
      · exact (h.types ft hm).bounds.2

theorem Labels.lookup {env st C} (hl : Labels env st C) (depth : U32)
    (hi : depth.val < C.LABELS.length) :
    ∃ view ts, labelAt st depth.val = some view ∧ resolve env view = some ts ∧
      C.LABELS[depth.val]! = .mk_list (ts.map Translation.valueType) := by
  have he := hl depth.val
  rw [List.getElem?_eq_getElem hi] at he
  unfold labelTypes at he
  cases hv : labelAt st depth.val with
  | none => simp [hv] at he
  | some view =>
    cases ht : resolve env view with
    | none => simp [hv, ht] at he
    | some ts =>
      refine ⟨view, ts, rfl, ht, ?_⟩
      rw [getElem!_pos C.LABELS depth.val hi]
      simpa [hv, ht] using he

namespace Completeness

/-- Conclusion of a leaf contract: `Body.step` accepts, ends at `next` with output `out`, and
grows the operand stack by at most 500 per encoded byte. -/
def LeafResult {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
     (ctx : code.Context) (index : U32) (opcode : U8)
    (bytes : List U8) (next : Usize) (out : List valtype) : Prop :=
  ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
    f.Output out s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (bytes.length + 1)

private theorem encoding_nonempty {bytes n} (h : Binary.Leb128.Encoding bytes n) : 1 ≤ bytes.length := by
  obtain ⟨bs, hb, _, _⟩ := h
  cases bs <;> simp_all

theorem Frame.call {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (C : context) (hmatch : Translation.Environment.Matches env ctx C)
    (henv : CodeEntry.EnvironmentWithinLimits env) (idx : U32) (bytes : List U8) (next : Usize)
    (he : Binary.Leb128.Encoding bytes idx.val) (hb : Body.Scalar.BytesAt data st.core.pos bytes next)
    (front input output : List valtype)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.CALL (.mk_uN idx.val)) (.mk_functype (.mk_list input) (.mk_list output)))
    (hcap : st.core.vals.val.length + 1000 < Usize.max) :
    LeafResult f data env ctx index 0x10#u8 bytes next (front ++ output) := by
  cases ht with
  | call _ _ params results hi ht _ _ =>
    obtain ⟨ft, hi, ht, hv⟩ := hmatch.func_lookup idx _ hi ht
    have hparams : ft.params.val.map Translation.valueType = input :=
      list.mk_list.inj (functype.mk_functype.inj hv).1
    have hresults : ft.results.val.map Translation.valueType = output :=
      list.mk_list.inj (functype.mk_functype.inj hv).2
    have hlimits := (henv.funcs ft (ht ▸ List.getElem_mem hi)).bounds
    obtain ⟨⟨_, s⟩, hrun, rfl, hc, hblocks, hp, rest, hvals, hlen, hreal⟩ := WP.spec_imp_exists
      (code.call.direct_complete st data env idx next ft ⟨bytes, hb.suffix, hb.length, hb.bound, he⟩
        hi ht hlimits.1 hlimits.2 f.core.outer f.core.operands front f.core.vals f.core.base_eq
        (by omega) (by simpa [f.core.poly_eq, hparams] using hr))
    dsimp only at hc hblocks hp hvals hlen hreal
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨f.core.output_of_same_ctrls hc hvals (by simpa [hresults] using hreal), hblocks⟩, ?_⟩
    have hbytes := encoding_nonempty he
    simp only [hvals, f.core.vals, List.length_append]
    omega

theorem Frame.call_indirect_indexed {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (C : context) (hmatch : Translation.Environment.Matches env ctx C)
    (henv : CodeEntry.EnvironmentWithinLimits env) (idx table : U32) (bytes tableBytes : List U8) (next : Usize)
    (he : Binary.Leb128.Encoding bytes idx.val) (hte : Binary.Leb128.Encoding tableBytes table.val)
    (hb : Body.Scalar.BytesAt data st.core.pos (bytes ++ tableBytes) next)
    (front input output : List valtype)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val))
      (.mk_functype (.mk_list input) (.mk_list output)))
    (hcap : st.core.vals.val.length + 1000 < Usize.max) :
    LeafResult f data env ctx index 0x11#u8 (bytes ++ tableBytes) next (front ++ output) := by
  cases ht with
  | call_indirect _ _ _ params results lim htable htabletype hi ht _ _ _ =>
    obtain ⟨ft, hi, ht, hv⟩ := hmatch.type_lookup idx _ hi ht
    have hparams : ft.params.val.map Translation.valueType = params :=
      list.mk_list.inj (functype.mk_functype.inj hv).1
    have hresults : ft.results.val.map Translation.valueType = output :=
      list.mk_list.inj (functype.mk_functype.inj hv).2
    have hlimits := (henv.types ft (ht ▸ List.getElem_mem hi)).bounds
    obtain ⟨middle, hindex, htablespan⟩ := hb.split
    obtain ⟨htableenv, hfun⟩ := hmatch.table_funcref table lim htable htabletype
    obtain ⟨⟨_, s⟩, hrun, rfl, hc, hblocks, hp, rest, hvals, hlen, hreal⟩ := WP.spec_imp_exists
      (code.call.indirect_complete st data env idx table middle next ft
        ⟨bytes, hindex.suffix, hindex.length, hindex.bound, he⟩
        ⟨tableBytes, htablespan.suffix, htablespan.length, htablespan.bound, hte⟩ htableenv hfun hi ht hlimits.1 hlimits.2 f.core.outer f.core.operands front
        f.core.vals f.core.base_eq (by omega) (by simpa [f.core.poly_eq, hparams] using hr))
    dsimp only at hc hblocks hp hvals hlen hreal
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨f.core.output_of_same_ctrls hc hvals (by simpa [hresults] using hreal), hblocks⟩, ?_⟩
    have hbytes := encoding_nonempty he
    have htables := encoding_nonempty hte
    simp only [hvals, f.core.vals, List.length_append]
    omega

theorem Frame.call_indirect {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (C : context) (hmatch : Translation.Environment.Matches env ctx C)
    (henv : CodeEntry.EnvironmentWithinLimits env) (idx : U32) (bytes : List U8) (next : Usize)
    (he : Binary.Leb128.Encoding bytes idx.val) (hb : Body.Scalar.BytesAt data st.core.pos (bytes ++ [0#u8]) next)
    (front input output : List valtype)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val))
      (.mk_functype (.mk_list input) (.mk_list output)))
    (hcap : st.core.vals.val.length + 1000 < Usize.max) :
    LeafResult f data env ctx index 0x11#u8 (bytes ++ [0#u8]) next (front ++ output) := by
  apply f.call_indirect_indexed data env ctx index C hmatch henv idx 0#u32 bytes [0#u8]
    next he _ hb front input output hr ht hcap
  exact ⟨[], 0#u8, rfl, by simp, by simp, by decide, by simp, by simp [Binary.Leb128.payload]⟩

theorem Frame.branch {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (C : context) (hlabels : Labels env st C)
    (depth : U32) (bytes : List U8) (next : Usize)
    (he : Binary.Leb128.Encoding bytes depth.val) (hb : Body.Scalar.BytesAt data st.core.pos bytes next)
    (front input output : List valtype)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.BR (.mk_uN depth.val)) (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index 0x0C#u8 bytes next (front ++ output) := by
  cases ht with
  | br _ _ before args after hi ht _ _ =>
    obtain ⟨view, ts, hl, hts, hlookup⟩ := hlabels.lookup depth hi
    have hargs : ts.map Translation.valueType = args := by
      simpa [proj_uN_0, proj_list_0, hlookup] using ht
    obtain ⟨s, hrun, hc, hblocks, hp, hv⟩ := code.branch.complete st data env depth next view ts
      f.core.parents f.core.current f.core.outer f.core.operands (front ++ before)
      f.core.ctrls f.core.vals f.core.base
      (by simp [f.blocks, f.core.ctrls, f.aligned])
      ⟨bytes, hb.suffix, hb.length, hb.bound, he⟩ hl hts
      (by simpa [f.core.poly_eq, hargs, List.append_assoc] using hr)
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨⟨true, [], hc, by simpa using hv, Body.Stack.realizes_polymorphic_empty _⟩, hblocks⟩, ?_⟩
    simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.branch_if {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (C : context) (hlabels : Labels env st C) (henv : CodeEntry.EnvironmentWithinLimits env)
    (depth : U32) (bytes : List U8) (next : Usize)
    (he : Binary.Leb128.Encoding bytes depth.val) (hb : Body.Scalar.BytesAt data st.core.pos bytes next)
    (front input output : List valtype)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (.BR_IF (.mk_uN depth.val)) (.mk_functype (.mk_list input) (.mk_list output)))
    (hcap : st.core.vals.val.length + 1000 < Usize.max) :
    LeafResult f data env ctx index 0x0D#u8 bytes next (front ++ output) := by
  cases ht with
  | br_if _ _ args hi ht _ _ =>
    obtain ⟨view, ts, hl, hts, hlookup⟩ := hlabels.lookup depth hi
    have hargs : ts.map Translation.valueType = output := by simpa [proj_uN_0, proj_list_0, hlookup] using ht
    have hsize := henv.resolve_bound view ts hts
    obtain ⟨⟨_, s⟩, hrun, rfl, hc, hblocks, hp, rest, hv, hlen, hreal⟩ := WP.spec_imp_exists
      (code.branch.conditional_complete st data env depth next view ts
        f.core.outer f.core.operands front f.core.vals f.core.base_eq
        (by simp [f.blocks, f.core.ctrls, f.aligned])
        ⟨bytes, hb.suffix, hb.length, hb.bound, he⟩ hl hts (by omega)
        (by simpa [f.core.poly_eq, hargs] using hr))
    dsimp only at hc hblocks hp hv hlen hreal
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨f.core.output_of_same_ctrls hc hv (by simpa [hargs] using hreal), hblocks⟩, ?_⟩
    have hbytes := encoding_nonempty he
    simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.return_ {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (C : context) (hmatch : Translation.Environment.Matches env ctx C)
    (hroot : resolve env (.Type index .Results) = some ctx.results.val)
    (next : Usize) (hb : Body.Scalar.BytesAt data st.core.pos [] next)
    (front input output : List valtype)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C .RETURN (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index 0x0F#u8 [] next (front ++ output) := by
  cases ht with
  | «return» _ before args after hreturn _ _ =>
    have hargs : ctx.results.val.map Translation.valueType = args := by
      simpa [hmatch.ret] using hreturn
    obtain ⟨s, hrun, hc, hblocks, hp, hv⟩ := returnStep.complete st env index ctx.results.val
      f.core.parents f.core.current f.core.outer f.core.operands (front ++ before)
      f.core.ctrls f.core.vals f.core.base hroot
      (by simpa [f.core.poly_eq, hargs, List.append_assoc] using hr)
    refine ⟨s, by simpa [step] using hrun, hp.trans hb.empty.symm,
      ⟨⟨true, [], hc, by simpa using hv, Body.Stack.realizes_polymorphic_empty _⟩, hblocks⟩, ?_⟩
    simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.branch_table {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (C : context) (hlabels : Labels env st C)
    (depths : List U32) (default : U32) (count entries final : List U8) (next : Usize)
    (hcount : Binary.Leb128.Encoding count depths.length) (hentries : Body.Scalar.IndicesEncoding depths entries)
    (hdefault : Binary.Leb128.Encoding final default.val)
    (hb : Body.Scalar.BytesAt data st.core.pos (count ++ entries ++ final) next)
    (front input output : List valtype)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C (Body.BrTable.instruction depths default) (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index 0x0E#u8 (count ++ entries ++ final) next (front ++ output) := by
  cases ht with
  | br_table _ _ _ before common after hbound hsub hdefaultbound hdefaultsub _ _ =>
    have htargets : ∀ d ∈ depths ++ [default], ∃ view ts,
        labelAt st d.val = some view ∧ resolve env view = some ts ∧
        Resulttype_sub (.mk_list common) (.mk_list (ts.map Translation.valueType)) := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · have hm : uN.mk_uN d.val ∈ depths.map (fun d => uN.mk_uN d.val) := List.mem_map.mpr ⟨d, hd, rfl⟩
        obtain ⟨view, ts, hl, hts, hlookup⟩ := hlabels.lookup d (hbound _ hm)
        exact ⟨view, ts, hl, hts, by simpa [proj_uN_0, hlookup] using hsub _ hm⟩
      · have he : d = default := by simpa using hd
        subst d
        obtain ⟨view, ts, hl, hts, hlookup⟩ := hlabels.lookup default hdefaultbound
        exact ⟨view, ts, hl, hts, by simpa [proj_uN_0, hlookup] using hdefaultsub⟩
    obtain ⟨s, hrun, hc, hblocks, hp, hv⟩ := code.branch_table.complete st data env
      f.core.parents f.core.current f.core.outer f.core.operands (front ++ before) common depths default next
      f.core.ctrls f.core.vals f.core.base
      (hb.br_table_decoded depths default hcount hentries hdefault) htargets
      (by simpa [f.core.poly_eq, List.append_assoc] using hr)
    refine ⟨s, by simpa [step] using hrun, hp,
      ⟨⟨true, [], hc, by simpa using hv, Body.Stack.realizes_polymorphic_empty _⟩, hblocks⟩, ?_⟩
    simp only [hv, f.core.vals, List.length_append]
    omega

/-- All control leaves satisfy the shared byte-weighted execution
contract directly from independent encodings and generated primitive rules. -/
theorem control_leaf (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (henv : CodeEntry.EnvironmentWithinLimits env)
    (hroot : resolve env (.Type index .Results) = some ctx.results.val)
    (C : context) (st : code.BodyState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : Translation.Environment.Matches env ctx C) (hlabels : Labels env st C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (hi : ControlImmediate opcode op bytes) (hb : Body.Scalar.BytesAt data st.core.pos bytes next)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index opcode bytes next (front ++ output) := by
  cases hi with
  | br depth he => exact f.branch data env ctx index C hlabels depth _ next he hb front input output hr ht
  | brIf depth he => exact f.branch_if data env ctx index C hlabels henv depth _ next he hb front input output hr ht hcap
  | brTable depths default hc he hd =>
    exact f.branch_table data env ctx index C hlabels
      depths default _ _ _ next hc he hd hb front input output hr ht
  | return_ => exact f.return_ data env ctx index C hmatch hroot next hb front input output hr ht
  | call idx he => exact f.call data env ctx index C hmatch henv idx _ next he hb front input output hr ht hcap
  | callIndirect idx he => exact f.call_indirect data env ctx index C hmatch henv idx _ next he hb front input output hr ht hcap

/-- Reference immediates use ordinary generated typing together with the
independent declaration condition for `ref.func`. -/
theorem reference_leaf (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (henv : CodeEntry.EnvironmentWithinLimits env)
    (C : context) (st : code.BodyState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : Translation.Environment.Matches env ctx C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (hi : ReferencesBinary.Immediate opcode op bytes) (hb : Body.Scalar.BytesAt data st.core.pos bytes next)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)))
    (hdecl : Spec.DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op) :
    LeafResult f data env ctx index opcode bytes next (front ++ output) := by
  cases hi with
  | refNull rt =>
    cases ht with
    | ref_null =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.ref_null data env ctx index rt next front hb (by omega) (by simpa using hr)
      exact ⟨s, hs, hp, ho, by simp; omega⟩
  | refIsNull =>
    cases ht with
    | ref_is_null _ rt _ _ =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.ref_is_null data env ctx index rt next front hb (by omega) hr
      exact ⟨s, hs, hp, ho, by simp; omega⟩
  | refFunc idx he =>
    cases ht with
    | ref_func _ _ ft hbound hlookup _ _ =>
      have hidx : idx.val < env.func_types.val.length := by simpa [hmatch.funcs, proj_uN_0] using hbound
      obtain ⟨s, hs, hp, ho, hl⟩ := f.ref_func data env ctx index idx next front
        (hb.u32_decoded idx he) hidx hdecl (by omega) (by simpa using hr)
      exact ⟨s, hs, hp, ho, by omega⟩
  | selectTyped ty he =>
    cases ht with
    | select_expl =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.typed_select data env ctx index ty _ next front he hb (by omega) hr
      exact ⟨s, hs, hp, ho, by simp; omega⟩
  | tableGet idx he =>
    cases ht with
    | table_get _ _ rt lim hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_get data env ctx index idx next front
        (hb.u32_decoded idx he) hidx (by omega)
        (by simpa [Simd.inputTypes, Translation.valueType] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes, hty] using ho, by omega⟩
  | tableSet idx he =>
    cases ht with
    | table_set _ _ rt lim hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_set data env ctx index idx next front
        (hb.u32_decoded idx he) hidx (by omega)
        (by simpa [Simd.inputTypes, hty, show Translation.valueType .I32 = valtype.I32 from rfl] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes] using ho, by omega⟩
  | callIndirect idx table he hte =>
    exact f.call_indirect_indexed data env ctx index C hmatch henv idx table _ _ next he hte hb
      front input output hr ht hcap

private theorem reference_type_injective {a b : wasm_types.ElemType}
    (h : Translation.valueType (Module.Constants.referenceValueType a) =
      Translation.valueType (Module.Constants.referenceValueType b)) : a = b := by
  cases a <;> cases b <;> simp_all [Module.Constants.referenceValueType, Translation.valueType]

/-- Bulk memory and table instructions are complete for the Wasm 2.0
reserved-byte grammar and the actual segment and table contexts. -/
theorem bulk_leaf (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32)
    (C : context) (st : code.BodyState) (f : Frame st) (subopcode : U32)
    (op : instr) (prefixBytes bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : Translation.Environment.Matches env ctx C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (he : Binary.Leb128.Encoding prefixBytes subopcode.val)
    (hi : BulkBinary.Immediate subopcode op bytes)
    (hb : Body.Scalar.BytesAt data st.core.pos (prefixBytes ++ bytes) next)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index 252#u8 (prefixBytes ++ bytes) next (front ++ output) := by
  obtain ⟨middle, hprefixSpan, hpayload⟩ := hb.split
  have hprefix := hprefixSpan.u32_decoded subopcode he
  cases hi with
  | memoryInit idx hindex =>
    cases ht with
    | memory_init _ _ mt hmem hlookup hdata hdataLookup _ _ _ =>
      obtain ⟨count, hcount, hidx⟩ := hmatch.data_bound idx hdata
      obtain ⟨s, hs, hp, ho, hl⟩ := f.memory_init data env ctx index middle next front idx count _
        hindex hcount hidx hprefix hpayload (hmatch.memory_exists hmem) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | dataDrop idx hindex =>
    cases ht with
    | data_drop _ _ hdata hlookup _ _ =>
      obtain ⟨count, hcount, hidx⟩ := hmatch.data_bound idx hdata
      obtain ⟨s, hs, hp, ho, hl⟩ := f.data_drop data env ctx index idx middle next front count
        hcount hidx hprefix (hpayload.u32_decoded idx hindex) (by omega) (by simpa using hr)
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | memoryCopy =>
    cases ht with
    | memory_copy _ mt hmem hlookup _ _ _ =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.memory_copy data env ctx index middle next front hprefix
        hpayload (hmatch.memory_exists hmem) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | memoryFill =>
    cases ht with
    | memory_fill _ mt hmem hlookup _ _ _ =>
      obtain ⟨s, hs, hp, ho, hl⟩ := f.memory_fill data env ctx index middle next front hprefix
        hpayload (hmatch.memory_exists hmem) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | tableInit element table helement htable =>
    cases ht with
    | table_init _ _ _ lim rt htableBound htableLookup helementBound helementLookup _ _ _ =>
      obtain ⟨htb, htt⟩ := hmatch.table_reference table lim rt htableBound htableLookup
      obtain ⟨heb, het⟩ := hmatch.element_reference element rt helementBound helementLookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_init data env ctx index element table middle next front _ _
        helement htable hprefix hpayload heb htb (reference_type_injective (het.trans htt.symm)) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | elemDrop idx hindex =>
    cases ht with
    | elem_drop _ _ rt hbound hlookup _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.element_reference idx rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.elem_drop data env ctx index idx middle next front hidx
        hprefix (hpayload.u32_decoded idx hindex) (by omega) (by simpa using hr)
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | tableCopy destination source hdestination hsource =>
    cases ht with
    | table_copy _ _ _ limD rt limS hd hdl hs hsl _ _ _ _ =>
      obtain ⟨hdb, hdt⟩ := hmatch.table_reference destination limD rt hd hdl
      obtain ⟨hsb, hst⟩ := hmatch.table_reference source limS rt hs hsl
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_copy data env ctx index destination source middle next front _ _
        hdestination hsource hprefix hpayload hdb hsb (reference_type_injective (hdt.trans hst.symm)) (by omega) hr
      exact ⟨s, hs, hp, by simpa using ho, by omega⟩
  | tableGrow idx hindex =>
    cases ht with
    | table_grow _ _ rt lim hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_grow data env ctx index idx middle hprefix next front
        (hpayload.u32_decoded idx hindex) hidx (by omega)
        (by simpa [Simd.inputTypes, hty, show Translation.valueType .I32 = valtype.I32 from rfl] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes, Translation.valueType] using ho, by omega⟩
  | tableSize idx hindex =>
    cases ht with
    | table_size _ _ lim rt hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_size data env ctx index idx middle hprefix next front
        (hpayload.u32_decoded idx hindex) hidx (by omega) (by simpa [Simd.inputTypes] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes, Translation.valueType] using ho, by omega⟩
  | tableFill idx hindex =>
    cases ht with
    | table_fill _ _ rt lim hbound hlookup _ _ _ =>
      obtain ⟨hidx, hty⟩ := hmatch.table_reference idx lim rt hbound hlookup
      obtain ⟨s, hs, hp, ho, hl⟩ := f.table_fill data env ctx index idx middle hprefix next front
        (hpayload.u32_decoded idx hindex) hidx (by omega)
        (by simpa [Simd.inputTypes, hty, show Translation.valueType .I32 = valtype.I32 from rfl] using hr)
      exact ⟨s, hs, hp, by simpa [Simd.outputTypes] using ho, by omega⟩

/-- Every plain instruction of the independent Wasm 2.0 grammar has a
complete actual dispatch contract, including all shared scalar instructions. -/
theorem plain_leaf (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (henv : CodeEntry.EnvironmentWithinLimits env)
    (hroot : resolve env (.Type index .Results) = some ctx.results.val)
    (C : context) (st : code.BodyState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : Translation.Environment.Matches env ctx C) (hlabels : Labels env st C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (hi : Body.Scalar.Immediate opcode (.plain op) bytes) (hb : Body.Scalar.BytesAt data st.core.pos bytes next)
    (hr : Body.Stack.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    LeafResult f data env ctx index opcode bytes next (front ++ output) := by
  rcases classify_plain hi with hscalar | hcontrol
  · exact scalar_leaf data env ctx index C st f opcode op bytes next front input output
      hmatch hcap hscalar hi hb hr ht
  · exact control_leaf data env ctx index henv hroot C st f opcode op bytes next front
      input output hmatch hlabels hcap hcontrol hb hr ht

theorem leaf_contract (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (henv : CodeEntry.EnvironmentWithinLimits env)
    (hroot : resolve env (.Type index .Results) = some ctx.results.val) :
    LeafContract data env ctx index := by
  intro C st f opcode op bytes next front input output hmatch hlabels hcap hi hb hr ht hdecl
  cases hi with
  | plain hi =>
    exact plain_leaf data env ctx index henv hroot C st f opcode op bytes next front input
      output hmatch hlabels hcap hi hb hr ht
  | reference hi =>
    exact reference_leaf data env ctx index henv C st f opcode op bytes next front input
      output hmatch hcap hi hb hr ht hdecl
  | signExtensionInstruction opcode source hmap =>
    rw [Body.NumericExtensions.signInstruction_eq] at hmap
    obtain ⟨operation, decoded, rfl⟩ := Option.map_eq_some_iff.mp hmap
    obtain ⟨s, hs, hp, ho, hl⟩ := f.sign_extension data env ctx index opcode operation next C
      front input output decoded hb (by omega) ht hr
    exact ⟨s, hs, hp, ho, by simp; omega⟩
  | saturatingInstruction subopcode source hmap he =>
    rw [Body.NumericExtensions.saturatingInstruction_eq] at hmap
    obtain ⟨operation, decoded, rfl⟩ := Option.map_eq_some_iff.mp hmap
    obtain ⟨s, hs, hp, ho, hl⟩ := f.saturating data env ctx index subopcode operation _ next C
      front input output decoded he hb (by omega) ht hr
    exact ⟨s, hs, hp, ho, by omega⟩
  | bulk subopcode he hi =>
    exact bulk_leaf data env ctx index C st f subopcode op _ _ next front input output
      hmatch hcap he hi hb hr ht
  | simd subopcode he hi =>
    obtain ⟨s, hs, hp, ho, hl⟩ := f.simd data env ctx ctx index subopcode op _ _ next C
      front input output he hi hb hmatch (by omega) ht hr
    exact ⟨s, hs, hp, ho, by omega⟩

end Completeness
end Itasca.Body

end
