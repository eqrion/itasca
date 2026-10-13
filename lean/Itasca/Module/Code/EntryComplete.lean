import Itasca.Module.Code.FuncTyping
import Itasca.Module.Code.LocalsComplete
import Itasca.Module.Code.Limits
import Itasca.Module.Code.Entry
import Itasca.Wasm1.Visitor.Lift
import Itasca.Profile.EntryComplete

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

/-- Successful code-entry validation follows from independent exact bytes,
declarative function typing, the Wasm 1.0 profile, and the explicit byte/local caps. -/
theorem module.validate_code_entry_with.complete_spec {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)
    (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (hbytes : At CodeEncodingWithinLimits data pos entry next) :
    module.validate_code_entry_with visitor data pos env index .Wasm1 v ⦃ r => r.1 = .Ok next ⦄ := by
  have hs : Profile.FuncType .Wasm1
      (env.types.val[env.func_type_indices.val[index.val].val]'htyped.type_lt) :=
    henv.types _ (List.getElem_mem _)
  apply module.validate_code_entry_with.complete_spec_of_body visitor haccept data pos env index entry next v
    .Wasm1 hi (Profile.EntryTyped.of_wasm1 htyped hs) hbound hbytes
  intro body ctx typeIdx ft hlookup hresults hsize hcert started
  exact code.validate_body_with.accepted_lift visitor haccept body env ctx started
    (Profile.run.complete .Wasm1 body env ctx typeIdx ft hlookup hresults
      ⟨henv.types, henv.funcs⟩ ⟨by intros; trivial, by intros; trivial⟩ hsize hcert)


theorem module.validate_code_entry_with.complete {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (entry : Code) (next : Usize) (v : V)
    (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (hbytes : At CodeEncodingWithinLimits data pos entry next) :
    ∃ v', module.validate_code_entry_with visitor data pos env index .Wasm1 v = .ok (.Ok next, v') := by
  obtain ⟨⟨r, v'⟩, hr, hok⟩ := WP.spec_imp_exists
    (module.validate_code_entry_with.complete_spec visitor haccept data pos env index entry next v
      hi htyped henv hbound hbytes)
  dsimp only at hok
  exact ⟨v', by simpa only [hok] using hr⟩

theorem module.validate_code_entry.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (index : Usize) (entry : Code) (next : Usize)
    (hi : index.val < env.func_type_indices.val.length)
    (htyped : CodeEntry.Typed env env.func_type_indices.val[index.val] entry)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (hbytes : At CodeEncodingWithinLimits data pos entry next) :
    module.validate_code_entry data pos env index .Wasm1 = .ok (.Ok next) := by
  obtain ⟨w, hr⟩ := module.validate_code_entry_with.complete
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts data pos env index entry next ()
    hi htyped henv hbound hbytes
  simp [module.validate_code_entry, hr]

end Itasca
