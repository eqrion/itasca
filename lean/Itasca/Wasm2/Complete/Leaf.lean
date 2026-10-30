import Itasca.Wasm2.NumericExt.Complete
import Itasca.Wasm2.Scalar.Complete
import Itasca.Wasm2.Complete.Program

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
theorem Frame.scalar {st} {profile : ValidationProfile} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx semantic : code.Context) (index : U32) (C : context)
    (opcode : U8) (op : instr) (bytes : List U8) (next : Usize)
    (front input output : List valtype)
    (hmatch : EnvTranslation.Matches env semantic C) (hlocals : ctx.locals = semantic.locals)
    (hscalar : opcode.val ∉ controlOpcodes) (hsize : st.core.vals.val.length < Usize.max)
    (hi : Wasm1.Immediate opcode (.plain op) bytes)
    (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ s, step st data env profile ctx index opcode = .ok (.Ok (), s) ∧
      s.core.pos = next ∧ f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨out, hrun, hpos, hout, hlen⟩ := scalar_complete data env semantic C st.core f.core
    opcode op bytes next front input output hmatch hsize hscalar hi hb hr ht
  refine ⟨{st with core := out}, ?_, hpos, ⟨hout, ?_⟩, hlen⟩
  · rw [step.scalar_eq st data env profile ctx index opcode hscalar]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn, code.step_wasm2.base _ _ _ _ _ _ _ (wasm2_base_immediate hi),
      code.step_extended.base _ _ _ _ _ _ _ (base_immediate hi).1 (base_immediate hi).2,
      scalar_context _ st.core data env ctx semantic opcode () hscalar hlocals, hrun]
    simp
  · obtain ⟨poly, operands, hctrls, _, _⟩ := hout
    simp [hctrls, f.core.ctrls]

/-- A leaf contract uses a principal generated typing and an independent
immediate encoding, which is a Wasm 1.0 immediate with the Wasm 1.0 restrictions under Wasm 1.0.
Growth is bounded by the full token's encoded byte count. -/
def LeafContract (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) : Prop :=
  ∀ (C : context) (st : code.BodyState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype),
    EnvTranslation.Matches env ctx C → Labels env st C →
    st.core.vals.val.length + 1000 < Usize.max →
    Immediate opcode (.plain op) bytes → Wasm1.BytesAt data st.core.pos bytes next →
    Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op →
    (profile = .Wasm1 → Wasm1.Immediate opcode (.plain op) bytes ∧ Wasm1.Instruction C op) →
    ∃ s, step st data env profile ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (bytes.length + 1)

/-- Reading the opcode and running a leaf contract produces an actual execution
and preserves the byte-weighted capacity bound for the surrounding program. -/
theorem atom_of_leaf (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32)
    (hstep : LeafContract data env profile ctx index) (op : instr) :
    AtomProgram data env profile ctx index [.plain op] op := by
  intro C st f next front input output hmatch hlabels hbounds hbytes hreal htyped hdecl hprofile
  obtain ⟨hat, hat1⟩ := hbytes.single
  obtain ⟨opcode, pos, bytes, hread, hpos, himmediate, hspan, hp, hbyte⟩ := hat.read_byte
  have hw1 : profile = .Wasm1 → Wasm1.Immediate opcode (.plain op) bytes ∧ Wasm1.Instruction C op :=
    fun h => ⟨(hat1 h).immediate_at hp hbyte hpos hspan, hprofile h⟩
  have hcheck : code.check_opcode profile opcode = .ok (.Ok ()) := by
    cases profile with
    | Wasm1 => exact code.check_opcode.complete _ _ (hw1 rfl).1.not_extension
    | Wasm2 => rfl
  let decoded : code.BodyState := {st with core := {st.core with pos := pos}}
  let g : Frame decoded :=
    ⟨⟨f.core.parents, f.core.current, f.core.outer, f.core.operands,
      f.core.ctrls, f.core.vals, f.core.base⟩, f.parents, f.current, f.blocks, f.aligned⟩
  have hcap : decoded.core.vals.val.length + 1000 < Usize.max := hbounds.val_capacity
  obtain ⟨s, hrun, hcursor, hout, hlen⟩ :=
    hstep C decoded g opcode op bytes next front input output hmatch hlabels hcap
      himmediate hspan hreal htyped hdecl hw1
  have hout' : f.Output (front ++ output) s := hout
  refine ⟨s, .single f.nonempty hread hcheck hrun, hcursor, hout', ?_⟩
  apply bounds_after hbounds hat hcursor
  · have hlenbytes : bytes.length + 1 = next.val - st.core.pos.val := by
      have := hspan.length
      omega
    simpa [decoded, hlenbytes] using hlen
  · have hb := hout'.2
    simp [hb]

/-- The scalar family discharges the shared leaf growth contract. -/
theorem scalar_leaf (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32)
    (C : context) (st : code.BodyState) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : EnvTranslation.Matches env ctx C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes)
    (hi : Wasm1.Immediate opcode (.plain op) bytes) (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ s, step st data env profile ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (bytes.length + 1) := by
  obtain ⟨s, hs, hp, ho, hl⟩ := f.scalar data env ctx ctx index C opcode op bytes next front input output
    hmatch rfl hscalar (by omega) hi hb hr ht
  exact ⟨s, hs, hp, ho, by omega⟩

end Itasca.Wasm2.Completeness
