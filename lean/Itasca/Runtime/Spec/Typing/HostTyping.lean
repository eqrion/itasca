import SpecExt.Host

/-! Source host typing and conservativity of the host-code backport.
The default module environment is the one used by runtime host decoding.
These results do not establish preservation of `Store_ok` by callbacks. -/
namespace SpecExt

/-- Host typing needs a valid signature and a well-formed representation,
not a Wasm body or a typed Wasm module environment. -/
theorem host_funcinst_ok (s : store) (ft : functype) (mm : moduleinst) (id : Nat)
    (signature : Functype_ok ft) (storeWf : wf_store s) (moduleWf : wf_moduleinst mm) :
    Funcinst_ok s ⟨ft, mm, .HOST id⟩ ft :=
  .host s ft mm id signature storeWf (.funcinst_case_ ft mm (.HOST id)
    moduleWf (.funccode_case_1 id))

/-- On Wasm code, the extended judgment has exactly the old premises. -/
theorem wasm_funcinst_ok_iff (s : store) (ft result : functype)
    (mm : moduleinst) (body : func) :
    Funcinst_ok s ⟨ft, mm, funccode_func body⟩ result ↔
      result = ft ∧ Functype_ok ft ∧ wf_store s ∧
      wf_funcinst ⟨ft, mm, funccode_func body⟩ ∧
      ∃ C, Moduleinst_ok s mm C ∧ Func_ok C body ft ∧ wf_context C := by
  constructor
  · intro typed
    cases body
    cases typed with
    | mk_Funcinst_ok _ _ _ C signature environment bodyTyped storeWf contextWf instanceWf =>
      exact ⟨rfl, signature, storeWf, instanceWf, C, environment, bodyTyped, contextWf⟩
  · rintro ⟨rfl, signature, storeWf, instanceWf, C, environment, bodyTyped, contextWf⟩
    exact .mk_Funcinst_ok s _ mm body C signature environment bodyTyped storeWf contextWf instanceWf

/-- Host functions with the decoder's empty environment inhabit source-typed
stores. No source store-typing assumption is used to construct this example. -/
theorem singleton_host_store_ok (ft : functype) (id : Nat) (signature : Functype_ok ft) :
    Store_ok ⟨[⟨ft, default, .HOST id⟩], [], [], [], [], []⟩ := by
  have moduleWf : wf_moduleinst (default : moduleinst) := by
    apply wf_moduleinst.moduleinst_case_ [] [] [] [] [] [] [] []
    simp [Forall]
  have instanceWf : wf_funcinst ⟨ft, default, .HOST id⟩ :=
    .funcinst_case_ _ _ _ moduleWf (.funccode_case_1 id)
  have storeWf : wf_store ⟨[⟨ft, default, .HOST id⟩], [], [], [], [], []⟩ := by
    constructor <;> simp_all [Forall]
  apply Store_ok.mk_Store_ok _ [] [] [] [] [] [] [⟨ft, default, .HOST id⟩] [ft] [] [] [] []
  all_goals first
    | rfl
    | exact storeWf
    | simpa [Forall₂] using host_funcinst_ok _ ft default id signature storeWf moduleWf
    | simp [Forall, Forall₂]

end SpecExt
