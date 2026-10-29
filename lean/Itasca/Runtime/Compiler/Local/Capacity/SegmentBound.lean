import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentProgram
import Itasca.Module.Limits

/-! Source framing bounds the synthetic initialization program counter. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ModuleBinary

private theorem leb_positive {bytes value} (h : Itasca.Leb128.Encoding bytes value) :
    1 ≤ bytes.length := by
  obtain ⟨before, last, rfl, _⟩ := h
  simp

private theorem vec_positive {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : VecEncoding R values bytes) : 1 ≤ bytes.length := by
  obtain ⟨count, entries, hc, _, rfl⟩ := h
  have := leb_positive hc
  simp only [List.length_append]
  omega

private theorem element_bytes {profile entry bytes}
    (h : ElementEncodingFor profile entry bytes) : 2 ≤ bytes.length := by
  cases profile with
  | Wasm1 =>
    obtain ⟨_, _, _, table, offset, entries, _, ht, _, he, rfl⟩ := h
    have := leb_positive ht
    have := vec_positive he
    simp only [List.length_append]
    omega
  | Wasm2 =>
    cases h with
    | activeIndices hf _ he | activeExpressions hf _ he =>
      have := leb_positive hf
      have := vec_positive he
      simp only [List.length_append]
      omega
    | passiveIndices hf he | declarativeIndices hf he | passiveExpressions hf he | declarativeExpressions hf he =>
      have := leb_positive hf
      have := vec_positive he
      simp only [List.length_append, List.length_singleton]
      omega
    | explicitIndices hf _ _ he | explicitExpressions hf _ _ he =>
      have := leb_positive hf
      have := vec_positive he
      simp only [List.length_append, List.length_singleton]
      omega

private theorem active_positive {index explicit bytes}
    (h : ActiveIndexEncoding index explicit bytes) : 1 ≤ bytes.length := by
  cases h with
  | implicit hf => exact leb_positive hf
  | explicit hf _ => have := leb_positive hf; simp only [List.length_append]; omega

private theorem data_bytes {profile entry bytes}
    (h : DataEncodingFor profile entry bytes) : 2 ≤ bytes.length := by
  cases profile with
  | Wasm1 =>
    obtain ⟨_, _, memory, offset, entries, _, hm, _, he, rfl⟩ := h
    have := leb_positive hm
    have := vec_positive he
    simp only [List.length_append]
    omega
  | Wasm2 =>
    cases h with
    | active hi _ he =>
      have := active_positive hi
      have := vec_positive he
      simp only [List.length_append]
      omega
    | passive hf he =>
      have := leb_positive hf
      have := vec_positive he
      simp only [List.length_append]
      omega

private theorem rep_size {α : Type} {R : α → List U8 → Prop} {values bytes}
    (h : Rep R values bytes) (minimum : ∀ value bytes, R value bytes → 2 ≤ bytes.length) :
    2 * values.length ≤ bytes.length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    have := minimum _ _ hx
    simp only [List.length_cons, List.length_append]
    omega

private theorem padded_size {α : Type} {R : α → List U8 → Prop} {id values bytes}
    (h : PaddedEncoding id (VecEncoding R) [] values bytes)
    (minimum : ∀ value bytes, R value bytes → 2 ≤ bytes.length) :
    2 * values.length ≤ bytes.length := by
  obtain ⟨customs, sec, _, hs, rfl⟩ := h
  cases hs with
  | absent => simp
  | present hp =>
    obtain ⟨size, payload, _, ⟨count, entries, _, hr, rfl⟩, rfl⟩ := hp
    have := rep_size hr minimum
    simp only [List.length_append, List.length_cons]
    omega

/-- Segment vectors consume at least two bytes per entry, including empty
passive segments. This holds for both binary profiles and non-minimal LEBs. -/
theorem segment_count_bytes {R raw bytes profile}
    (h : ModuleEncodingWith R raw bytes profile) :
    2 * (raw.elements.length + raw.data.length) ≤ bytes.length := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, hel, _, _, hd, _, rfl, _, _⟩ := h
  have he := padded_size hel (fun _ _ h => element_bytes h)
  have hd := padded_size hd (fun _ _ h => data_bytes h)
  simp only [List.length_append]
  omega

private theorem flatten_bound {α : Type} (blocks : List (List α))
    (bounded : ∀ block ∈ blocks, block.length ≤ 5) :
    blocks.flatten.length ≤ 5 * blocks.length := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
    have head := bounded block (by simp)
    have tail := ih (fun block member => bounded block (by simp [member]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- At most five instructions are emitted for any source segment, followed by
one return. No allocator or runtime execution assumption enters this bound. -/
theorem SegmentProgram.length_bound {module function}
    (certificate : SegmentProgram module function) :
    function.code.length ≤
      5 * (module.module.env.elements.length + module.module.tail.data.length) + 1 := by
  obtain ⟨elements, datas, cert⟩ := certificate
  have he : elements.flatten.length ≤ 5 * elements.length := by
    apply flatten_bound
    intro block member
    obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < module.module.env.elements.val.length := by
      have := cert.elementCount
      simp only [alloc.vec.Vec.length] at this
      omega
    obtain ⟨instructions, read, program⟩ := cert.elements index _ (List.getElem?_eq_getElem sourceBound)
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem bound, found] at read
      exact Option.some.inj read.symm
    subst instructions
    cases program <;> simp
  have hd : datas.flatten.length ≤ 5 * datas.length := by
    apply flatten_bound
    intro block member
    obtain ⟨index, bound, found⟩ := List.mem_iff_getElem.mp member
    have sourceBound : index < module.module.tail.data.val.length := by
      have := cert.dataCount
      simp only [alloc.vec.Vec.length] at this
      omega
    obtain ⟨instructions, read, program⟩ := cert.datas index _ (List.getElem?_eq_getElem sourceBound)
    have same : instructions = block := by
      rw [List.getElem?_eq_getElem bound, found] at read
      exact Option.some.inj read.symm
    subst instructions
    cases program <;> simp
  rw [alloc.vec.Vec.length, cert.instructions]
  simp only [List.length_append, List.length_singleton]
  have := cert.elementCount
  have := cert.dataCount
  omega

/-- The fixed one-GiB validator cap and the binary segment framing leave ample
room below the interpreter's 32-bit program counter. The two count equalities
are source/metadata coherence, not execution-correctness premises. -/
theorem SegmentProgram.pc_bound {module function raw bytes profile R}
    (certificate : SegmentProgram module function)
    (encoding : ModuleEncodingWith R raw bytes profile)
    (moduleBound : bytes.length ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (elements : module.module.env.elements.length = raw.elements.length)
    (datas : module.module.tail.data.length = raw.data.length) :
    function.code.length < U32.max := by
  have codeBound := certificate.length_bound
  have sourceBound := segment_count_bytes encoding
  simp only [Itasca.limits.MAX_MODULE_BYTES] at moduleBound
  rw [elements, datas] at codeBound
  norm_num [U32.max_eq] at *
  omega

end Itasca.Runtime.Code
