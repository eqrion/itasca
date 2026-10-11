import Itasca.MultiValue.ScalarDispatch
import Itasca.MultiValue.CompletenessProgram

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Read the opcode of an independent token encoding with the actual byte
reader used by the multi-value body loop. -/
theorem At.read_byte {data start token next} (h : At data start token next) :
    ∃ opcode pos immediate,
      reader.read_byte data start = .ok (.Ok (opcode, pos)) ∧
      pos.val = start.val + 1 ∧ Immediate opcode token immediate ∧
      Wasm.BytesAt data pos immediate next := by
  have hb : start.val < data.length := by have := h.span; omega
  obtain ⟨_, hr, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data start hb)
  obtain ⟨opcode, imm, hi, ⟨_, hbyte⟩, hs⟩ := h.immediate pos hpos
  exact ⟨opcode, pos, imm, by simpa [hbyte] using hr, hpos, hi, hs⟩

/-- The shared leaf grammar's control cases are exactly branches, return, and
calls. Structured tokens belong to the separate multi-value grammar. -/
inductive ControlImmediate : U8 → instr → List U8 → Prop where
  | br (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      ControlImmediate 0x0C#u8 (.BR (.mk_uN idx.val)) bytes
  | brIf (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      ControlImmediate 0x0D#u8 (.BR_IF (.mk_uN idx.val)) bytes
  | brTable (indices : List U32) (default : U32) {count entries final} :
      Leb128.Encoding count indices.length → Wasm.IndicesEncoding indices entries →
      Leb128.Encoding final default.val →
      ControlImmediate 0x0E#u8 (.BR_TABLE (indices.map (fun i => .mk_uN i.val)) (.mk_uN default.val))
        (count ++ entries ++ final)
  | return_ : ControlImmediate 0x0F#u8 .RETURN []
  | call (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      ControlImmediate 0x10#u8 (.CALL (.mk_uN idx.val)) bytes
  | callIndirect (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      ControlImmediate 0x11#u8 (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val)) (bytes ++ [0#u8])

/-- Exhaustive scalar/control classification of the independent plain grammar. -/
theorem classify_plain {opcode op bytes} (h : Wasm.Immediate opcode (.plain op) bytes) :
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

end Itasca.MultiValue

namespace Itasca.MultiValue.Completeness

/-- Scalar dispatch accepts an independently encoded principal typing and
preserves the current multi-value descriptor. The semantic return vector can
differ from the runtime scalar context's unused return vector. -/
theorem Frame.scalar {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx semantic : code.Context) (index : U32) (C : context)
    (opcode : U8) (op : instr) (bytes : List U8) (next : Usize)
    (front input output : List valtype)
    (hmatch : EnvTranslation.Matches env semantic C) (hlocals : ctx.locals = semantic.locals)
    (hscalar : opcode.val ∉ controlOpcodes) (hsize : st.core.vals.val.length < Usize.max)
    (hi : Wasm.Immediate opcode (.plain op) bytes)
    (hb : Wasm.BytesAt data st.core.pos bytes next)
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
    rw [if_neg hn, scalar_context _ st.core data env ctx semantic opcode () hscalar hlocals, hrun]
    simp
  · obtain ⟨poly, operands, hctrls, _, _⟩ := hout
    simp [hctrls, f.core.ctrls]

/-- A leaf contract uses a principal generated typing and an independent
immediate encoding. Growth is bounded by the full token's encoded byte count. -/
def LeafContract (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) : Prop :=
  ∀ (C : context) (st : multi_value.State) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype),
    EnvTranslation.Matches env ctx C → Labels env st C →
    st.core.vals.val.length + 1000 < Usize.max →
    Wasm.Immediate opcode (.plain op) bytes → Wasm.BytesAt data st.core.pos bytes next →
    Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input) →
    Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output)) →
    ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (bytes.length + 1)

/-- Reading the opcode and running a leaf contract produces an actual execution
and preserves the byte-weighted capacity bound for the surrounding program. -/
theorem atom_of_leaf (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (hstep : LeafContract data env ctx index) (op : instr) :
    AtomProgram data env ctx index [.plain op] op := by
  intro C st f next front input output hmatch hlabels hbounds hbytes hreal htyped
  have hat := hbytes.single
  obtain ⟨opcode, pos, bytes, hread, hpos, himmediate, hspan⟩ := hat.read_byte
  cases himmediate with
  | plain hi =>
    let decoded : multi_value.State := {st with core := {st.core with pos := pos}}
    let g : Frame decoded :=
      ⟨⟨f.core.parents, f.core.current, f.core.outer, f.core.operands,
        f.core.ctrls, f.core.vals, f.core.base⟩, f.parents, f.current, f.blocks, f.aligned⟩
    have hcap : decoded.core.vals.val.length + 1000 < Usize.max := hbounds.val_capacity
    obtain ⟨s, hrun, hcursor, hout, hlen⟩ :=
      hstep C decoded g opcode op bytes next front input output hmatch hlabels hcap
        hi hspan hreal htyped
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
theorem scalar_leaf (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (C : context) (st : multi_value.State) (f : Frame st) (opcode : U8)
    (op : instr) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hmatch : EnvTranslation.Matches env ctx C)
    (hcap : st.core.vals.val.length + 1000 < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes)
    (hi : Wasm.Immediate opcode (.plain op) bytes) (hb : Wasm.BytesAt data st.core.pos bytes next)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ input))
    (ht : Instr_ok C op (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ s, step st data env ctx index opcode = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ output) s ∧
      s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (bytes.length + 1) := by
  obtain ⟨s, hs, hp, ho, hl⟩ := f.scalar data env ctx ctx index C opcode op bytes next front input output
    hmatch rfl hscalar (by omega) hi hb hr ht
  exact ⟨s, hs, hp, ho, by omega⟩

/-- Independently encoded scalar atoms satisfy the whole-program interface. -/
theorem scalar_atom (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (op : instr)
    (hscalar : ∀ opcode bytes, Wasm.Immediate opcode (.plain op) bytes →
      opcode.val ∉ controlOpcodes) : AtomProgram data env ctx index [.plain op] op := by
  intro C st f next front input output hmatch hlabels hbounds hbytes hreal htyped
  have hat := hbytes.single
  obtain ⟨opcode, pos, bytes, hread, hpos, himmediate, hspan⟩ := hat.read_byte
  cases himmediate with
  | plain hi =>
    let decoded : multi_value.State := {st with core := {st.core with pos := pos}}
    let g : Frame decoded :=
      ⟨⟨f.core.parents, f.core.current, f.core.outer, f.core.operands,
        f.core.ctrls, f.core.vals, f.core.base⟩, f.parents, f.current, f.blocks, f.aligned⟩
    have hcap : decoded.core.vals.val.length + 1000 < Usize.max := hbounds.val_capacity
    obtain ⟨s, hrun, hcursor, hout, hlen⟩ :=
      scalar_leaf data env ctx index C decoded g opcode op bytes next front input output hmatch
        hcap (hscalar opcode bytes hi) hi hspan hreal htyped
    have hout' : f.Output (front ++ output) s := hout
    refine ⟨s, .single f.nonempty hread hrun, hcursor, hout', ?_⟩
    apply bounds_after hbounds hat hcursor
    · have hlenbytes : bytes.length + 1 = next.val - st.core.pos.val := by
        have := hspan.length
        omega
      simpa [decoded, hlenbytes] using hlen
    · have hb := hout'.2
      simp [hb]

end Itasca.MultiValue.Completeness
