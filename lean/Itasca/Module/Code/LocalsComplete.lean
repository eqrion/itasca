import Itasca.Module.Code.Locals
import Itasca.Module.Readers.BasicComplete

/-!
# Local declaration completeness

`metadata.decode_locals.complete` shows that `metadata.decode_locals` accepts any independent
`LocalEncoding` vector whose types the profile allows and whose expansion fits in
`limits.MAX_LOCALS`, returning the expansion `ModuleLocals.declared`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- The loop of `metadata.decode_locals` accepts the remaining encoded groups and returns the
output extended by their expansion. -/
theorem metadata.decode_locals_loop.complete (data : Slice U8) (profile : ValidationProfile) (groups : U32)
    (out : alloc.vec.Vec wasm_types.ValueType) (pos : Usize) (i : U32)
    (decoded : List (U32 × wasm_types.ValueType)) (next : Usize)
    (hcount : i.val + decoded.length = groups.val)
    (hbytes : At (Rep LocalEncoding) data pos decoded next)
    (hallowed : ∀ group ∈ decoded, ValueTypeAllowed profile group.2)
    (hcap : out.val.length + (ModuleLocals.declared decoded).length ≤ limits.MAX_LOCALS.val) :
    ∃ locals, metadata.decode_locals_loop data profile groups out pos i = .ok (.Ok (locals, next)) ∧
      locals.val = out.val ++ ModuleLocals.declared decoded := by
  induction decoded generalizing out pos i with
  | nil =>
    have hi : i = groups := UScalar.eq_of_val_eq (by simpa using hcount)
    have hn := hbytes.rep_nil
    refine ⟨out, ?_, by simp [ModuleLocals.declared]⟩
    unfold metadata.decode_locals_loop
    rw [loop]
    simp [metadata.decode_locals_loop.body, hi, hn]
  | cons group rest ih =>
    obtain ⟨count, ty⟩ := group
    obtain ⟨middle, hlocal, hrest⟩ := hbytes.rep_cons
    obtain ⟨bytes, ⟨countBytes, hcountBytes, rfl⟩, hlocal⟩ := hlocal
    obtain ⟨valuePos, hcountSpan, htypeSpan⟩ := hlocal.split
    have hread := hcountSpan.read_u32 count hcountBytes
    have htype := metadata.decode_value_type.complete data valuePos ty middle
      ⟨[valueByte ty], rfl, htypeSpan⟩ profile (hallowed (count, ty) (by simp))
    have hlt : i.val < groups.val := by simp only [List.length_cons] at hcount; omega
    have hstop : ¬ i ≥ groups := by scalar_tac
    have hdecl : ModuleLocals.declared ((count, ty) :: rest) =
        List.replicate count.val ty ++ ModuleLocals.declared rest := rfl
    have hroom : out.val.length + count.val + (ModuleLocals.declared rest).length ≤ limits.MAX_LOCALS.val := by
      simpa [hdecl, List.length_append, List.length_replicate, Nat.add_assoc] using hcap
    obtain ⟨space, hspace, hspaceVal⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x := limits.MAX_LOCALS) (y := alloc.vec.Vec.len out) (by scalar_tac))
    have hfits : ¬ UScalar.cast .Usize count > space := by
      have hc := U32.cast_Usize_val_eq count
      scalar_tac
    have hfitval : ¬ space.val < count.val := by scalar_tac
    have hmax : limits.MAX_LOCALS.val ≤ Usize.max := by
      simp only [limits.MAX_LOCALS]; scalar_tac
    obtain ⟨pushed, hpush, hpushed⟩ := WP.spec_imp_exists
      (metadata.push_locals.spec out count ty (by omega))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    obtain ⟨locals, hrec, hvals⟩ := ih pushed middle j
      (by simp only [List.length_cons] at hcount; scalar_tac) hrest
      (fun group hm => hallowed group (by simp [hm]))
      (by simpa [hpushed, List.length_append, List.length_replicate] using hroom)
    refine ⟨locals, ?_, by simpa [hpushed, hdecl, List.append_assoc] using hvals⟩
    unfold metadata.decode_locals_loop
    rw [loop]
    simp only [metadata.decode_locals_loop.body, hstop, ↓reduceIte, hread, bind_ok,
      core.result.Result.Insts.CoreOpsTry.branch, lift, hspace, hj]
    simpa [metadata.decode_locals_loop, metadata.decode_locals_loop.body,
      core.result.Result.Insts.CoreOpsTry.branch, lift, htype, hfitval, hpush, hspace, hj] using hrec

/-- `metadata.decode_locals` accepts an independently encoded local vector within the limit and
returns its expansion. -/
theorem metadata.decode_locals.complete (data : Slice U8) (pos : Usize) (profile : ValidationProfile)
    (groups : List (U32 × wasm_types.ValueType)) (next : Usize)
    (hbytes : At (VecEncoding LocalEncoding) data pos groups next)
    (hallowed : ∀ group ∈ groups, ValueTypeAllowed profile group.2)
    (hcap : (ModuleLocals.declared groups).length ≤ limits.MAX_LOCALS.val) :
    ∃ locals, metadata.decode_locals data pos profile = .ok (.Ok (locals, next)) ∧
      locals.val = ModuleLocals.declared groups := by
  obtain ⟨count, first, hcount, hread, hrest⟩ := hbytes.vector_split
  obtain ⟨locals, hloop, hvals⟩ := metadata.decode_locals_loop.complete data profile count
    (alloc.vec.Vec.new _) first 0#u32 groups next (by simpa using hcount.symm) hrest hallowed (by simpa using hcap)
  refine ⟨locals, ?_, by simpa using hvals⟩
  simp [metadata.decode_locals, reader.read_u32_leb.complete data pos count first hread,
    core.result.Result.Insts.CoreOpsTry.branch, hloop]

end Itasca
