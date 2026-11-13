import Itasca.Wasm2.Complete.Frame
import Itasca.Wasm2.SoundLoop
import Itasca.Binary.Wasm2.SyntaxUnique
import Itasca.Wasm2.NumericExt.Complete
import Itasca.Wasm2.Scalar.Complete

/-!
Sections, each formerly its own module: Program, Leaf.
-/

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

namespace Itasca.Wasm2.Completeness

/-- Execution of a typed instruction list within one concrete control frame. -/
def Program (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (tokens : List Token) (ops : List instr) : Prop :=
  ∀ (C : context) (st : code.BodyState) (f : Frame st) (next : Usize)
    (input output : List valtype),
    EnvTranslation.Matches env ctx C → Labels env st C →
    Bounds data st → Consumed data st.core.pos tokens next →
    Sequence.Realizes f.core.current.polymorphic_base f.core.operands input →
    Instrs_ok C ops (.mk_functype (.mk_list input) (.mk_list output)) →
    DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops →
    ∃ s, Execution data env ctx index st s ∧ s.core.pos = next ∧ f.Output output s ∧
      Bounds data s

/-- The normalized head instruction has a primitive generated typing rule
and a preserved prefix on its operand stack. -/
def AtomProgram (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (tokens : List Token) (op : instr) : Prop :=
  ∀ (C : context) (st : code.BodyState) (f : Frame st) (next : Usize)
    (front input output : List valtype),
    EnvTranslation.Matches env ctx C → Labels env st C →
    Bounds data st → Consumed data st.core.pos tokens next →
    Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op →
    ∃ s, Execution data env ctx index st s ∧ s.core.pos = next ∧
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
        f.output_self (DeclarativeComplete.empty_realizes hreal htyped), hbounds⟩
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
        DeclarativeComplete.head_realizes hreal htyped
      have hsmaller : SmallerPrograms data env ctx index first.length := by
        intro ts es hlen he
        exact ih ts.length (by omega) ts es he rfl
      obtain ⟨mid, hrun, hpos, hout, hbound⟩ :=
        hatom first op hfirst hsmaller C st f middle front ins outs hmatch hlabels
          hbounds hfirstbytes hinput hop (DeclaredReferences.Instructions.cons_iff.mp hdecl).1
      obtain ⟨g, _, _, hgp, hgo, hgk, hgba, hgr⟩ := hout.next
      have hrestbytes' : Consumed data mid.core.pos rest next := by
        simpa [hpos] using hrestbytes
      have hlabels' : Labels env mid C := hout.labels hlabels
      obtain ⟨last, hrun', hpos', hout', hbound'⟩ :=
        ih rest.length hrest_len rest ops hrest rfl C mid g next _ _
          hmatch hlabels' hbound hrestbytes' hgr htail (DeclaredReferences.Instructions.cons_iff.mp hdecl).2
      exact ⟨last, hrun.append hrun', hpos',
        hout'.transfer hout.2 hgp hgo hgk hgba, hbound'⟩

end Itasca.Wasm2.Completeness

end

/-! ## Leaf -/

section

/-!
# Leaf contracts and scalar completeness

`LeafContract` is the interface a leaf instruction family must meet: given an independent
encoding and a generated typing, `Wasm2.step` accepts with a byte-weighted capacity bound.
`atom_of_leaf` turns a `LeafContract` into an `AtomProgram`. This file discharges the contract for
the scalar family (`Frame.scalar`, `scalar_leaf`, `scalar_atom`); `classify_plain` splits plain
instructions into scalar and control cases.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Reads the opcode of an independent token encoding with the byte reader used by the Wasm 2.0
body loop. -/
theorem At.read_byte {data start token next} (h : At data start token next) :
    ∃ opcode pos immediate,
      reader.read_byte data start = .ok (.Ok (opcode, pos)) ∧
      pos.val = start.val + 1 ∧ Immediate opcode token immediate ∧
      Wasm1.BytesAt data pos immediate next ∧
      ∃ hp : start.val < data.length, data.val[start.val] = opcode := by
  have hb : start.val < data.length := by have := h.span; omega
  obtain ⟨_, hr, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data start hb)
  obtain ⟨opcode, imm, hi, ⟨hp, hbyte⟩, hs⟩ := h.immediate pos hpos
  exact ⟨opcode, pos, imm, by simpa [hbyte] using hr, hpos, hi, hs, hp, hbyte⟩

/-- The control cases of the leaf grammar are branches, `return` and calls. Structured control
(`block`, `loop`, `if`) is handled through `Token` in `Wasm2/Complete/Control`. -/
inductive ControlImmediate : U8 → instr → List U8 → Prop where
  | br (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      ControlImmediate 0x0C#u8 (.BR (.mk_uN idx.val)) bytes
  | brIf (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      ControlImmediate 0x0D#u8 (.BR_IF (.mk_uN idx.val)) bytes
  | brTable (indices : List U32) (default : U32) {count entries final} :
      Leb128.Encoding count indices.length → Wasm1.IndicesEncoding indices entries →
      Leb128.Encoding final default.val →
      ControlImmediate 0x0E#u8 (.BR_TABLE (indices.map (fun i => .mk_uN i.val)) (.mk_uN default.val))
        (count ++ entries ++ final)
  | return_ : ControlImmediate 0x0F#u8 .RETURN []
  | call (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      ControlImmediate 0x10#u8 (.CALL (.mk_uN idx.val)) bytes
  | callIndirect (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      ControlImmediate 0x11#u8 (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val)) (bytes ++ [0#u8])

/-- Exhaustive scalar/control classification of the independent plain grammar. -/
theorem classify_plain {opcode op bytes} (h : Wasm1.Immediate opcode (.plain op) bytes) :
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
      simp [MemoryMeaning.opcodeMeaning, he] at hmap
  | numeric opcode operation hmap =>
    left
    have hb := Numeric.NumericOp.bounds hmap
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  | _ => exact .inl (by decide)

end Itasca.Wasm2

namespace Itasca.Wasm2.Completeness

/-- Scalar dispatch accepts an independently encoded principal typing and
preserves the current block descriptor. The semantic return vector can
differ from the runtime scalar context's unused return vector. -/
theorem Frame.scalar {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx semantic : code.Context) (index : U32) (C : context)
    (opcode : U8) (op : instr) (bytes : List U8) (next : Usize)
    (front input output : List valtype)
    (hmatch : EnvTranslation.Matches env semantic C) (hlocals : ctx.locals = semantic.locals)
    (hscalar : opcode.val ∉ controlOpcodes) (hsize : st.core.vals.val.length < Usize.max)
    (hi : Wasm1.Immediate opcode (.plain op) bytes)
    (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧
      s.core.pos = next ∧ f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨out, hrun, hpos, hout, hlen⟩ := scalar_complete data env semantic C st.core f.core
    opcode op bytes next front input output hmatch hsize hscalar hi hb hr ht
  refine ⟨{st with core := out}, ?_, hpos, ⟨hout, ?_⟩, hlen⟩
  · rw [step.scalar_eq st data env ctx index opcode hscalar]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn, code.step_wasm2.base _ _ _ _ _ _ _ (wasm2_base_immediate hi),
      code.step_extended.base _ _ _ _ _ _ _ (base_immediate hi).1 (base_immediate hi).2,
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
    EnvTranslation.Matches env ctx C → Labels env st C →
    st.core.vals.val.length + 1000 < Usize.max →
    Immediate opcode (.plain op) bytes → Wasm1.BytesAt data st.core.pos bytes next →
    Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op →
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
  refine ⟨s, .single f.nonempty hread hrun, hcursor, hout', ?_⟩
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
    (hmatch : EnvTranslation.Matches env ctx C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes)
    (hi : Wasm1.Immediate opcode (.plain op) bytes) (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (bytes.length + 1) := by
  obtain ⟨s, hs, hp, ho, hl⟩ := f.scalar data env ctx ctx index C opcode op bytes next front input output
    hmatch rfl hscalar (by omega) hi hb hr ht
  exact ⟨s, hs, hp, ho, by omega⟩

end Itasca.Wasm2.Completeness

end
