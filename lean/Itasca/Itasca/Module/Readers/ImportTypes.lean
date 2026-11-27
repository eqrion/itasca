import Itasca.Module.Readers.ExternalType

/-! The import accessor walks four independent descriptor spaces in import order. -/

open Aeneas Aeneas.Std

namespace Itasca.Module.Externals

/-- Index of the next import in each of the four Wasm index spaces. -/
structure ImportPositions where
  funcs : U32
  tables : U32
  memories : U32
  globals : U32

def ImportPositions.current (p : ImportPositions) : metadata.ImportKind → metadata.ExportDesc
  | .Func => .Func p.funcs
  | .Table => .Table p.tables
  | .Memory => .Memory p.memories
  | .Global => .Global p.globals

/-- One import advances its own index and preserves the other three. -/
def ImportPositions.Advances (p q : ImportPositions) (kind : metadata.ImportKind) : Prop :=
  match kind with
  | .Func => q = { p with funcs := q.funcs } ∧ q.funcs.val = p.funcs.val + 1
  | .Table => q = { p with tables := q.tables } ∧ q.tables.val = p.tables.val + 1
  | .Memory => q = { p with memories := q.memories } ∧ q.memories.val = p.memories.val + 1
  | .Global => q = { p with globals := q.globals } ∧ q.globals.val = p.globals.val + 1

/-- Ordered import types as determined by index-space lookup on successive imports. -/
inductive ImportTypes (env : metadata.CodeMetadata) :
    ImportPositions → List metadata.Import → List wasm_types.ExternType → Prop where
  | nil (p) : ImportTypes env p [] []
  | cons {p q entry xt rest types} :
      env.externalTypeAt (p.current entry.kind) = some xt → p.Advances q entry.kind →
      ImportTypes env q rest types → ImportTypes env p (entry :: rest) (xt :: types)

end Itasca.Module.Externals

namespace Itasca.metadata.ModuleMetadataArcCodeMetadata

open Module.Externals

theorem import_types_loop.resolved (env : ModuleMetadata (alloc.sync.Arc CodeMetadata))
    (expected : List wasm_types.ExternType) (hlen : expected.length = env.imports.val.length)
    (p : ImportPositions) (out : alloc.vec.Vec wasm_types.ExternType) (i : Usize)
    (hi : i.val ≤ expected.length) (hout : out.val = expected.take i.val)
    (types : ImportTypes env.code p (env.imports.val.drop i.val) (expected.drop i.val)) :
    import_types_loop env p.funcs p.tables p.memories p.globals out i ⦃ r =>
      ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  unfold import_types_loop
  apply loop.spec_decr_nat (fun x => expected.length - x.2.2.2.2.2.val)
    (fun (f,t,m,g,v,j) => j.val ≤ expected.length ∧ v.val = expected.take j.val ∧
      ImportTypes env.code ⟨f,t,m,g⟩ (env.imports.val.drop j.val) (expected.drop j.val))
  · rintro ⟨f,t,m,g,v,j⟩ ⟨hj,hv,typed⟩
    simp only [import_types_loop.body]
    split
    · have hlt : j.val < env.imports.val.length := by scalar_tac
      have hx : j.val < expected.length := by omega
      have hcap : v.val.length < Usize.max := by
        have hb := env.imports.property
        rw [hv, List.length_take, Nat.min_eq_left hj]
        scalar_tac
      rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hx] at typed
      cases typed with
      | @cons _ q _ _ _ _ look advance tail =>
        step as ⟨entry, hentry⟩
        subst entry
        cases hk : env.imports.val[j.val].kind <;>
          simp only [hk, ImportPositions.Advances, ImportPositions.current] at advance look <;>
          obtain ⟨hq, hn⟩ := advance
        all_goals
          dsimp only
          step as ⟨n, hn'⟩
          simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_ok]
          step as ⟨r, hr⟩
          rw [look] at hr
          cases r with
          | Err e => contradiction
          | Ok xt =>
            cases Option.some.inj hr
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step as ⟨out', hv'⟩
            step as ⟨next, hnext⟩
            refine ⟨by omega, ?_, ?_, by omega⟩
            · rw [hv', hnext, hv, List.take_succ_eq_append_getElem hx]
            · rw [hnext]
              convert tail using 2 <;> rw [hq] <;> congr 1 <;> apply UScalar.eq_of_val_eq <;> dsimp only at * <;> omega
    · have he : j.val = expected.length := by scalar_tac
      exact ⟨v, rfl, by simpa [he] using hv⟩
  · exact ⟨hi, hout, types⟩

theorem import_types.resolved (env : ModuleMetadata (alloc.sync.Arc CodeMetadata))
    (expected : List wasm_types.ExternType)
    (types : ImportTypes env.code ⟨0#u32,0#u32,0#u32,0#u32⟩ env.imports.val expected) :
    import_types env ⦃ r => ∃ result, r = .Ok result ∧ result.val = expected ⦄ := by
  have sameLength {p xs ys} (h : ImportTypes env.code p xs ys) : ys.length = xs.length := by
    induction h <;> simp_all
  exact import_types_loop.resolved env expected (sameLength types) ⟨0#u32, 0#u32, 0#u32, 0#u32⟩
    (alloc.vec.Vec.new _) 0#usize (by simp) (by simp) (by simpa using types)

end Itasca.metadata.ModuleMetadataArcCodeMetadata
