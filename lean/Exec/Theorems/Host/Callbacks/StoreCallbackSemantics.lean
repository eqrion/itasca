import Exec.Theorems.Host.Callbacks.StoreCallbacks

/-! Independent operation/control semantics for the executable callback class.
The write permission is an in-range mutable i32 global. Rejection traps and
retains the store; accepted writes specify the exact encoded field update. -/
namespace Exec.Theorems.PureCallbacks

theorem Returns.deterministic {program : Program} {status nextStatus values nextValues}
    (first : Returns program status values) (second : Returns program nextStatus nextValues) :
    status = nextStatus ∧ values = nextValues := by
  induction first generalizing nextStatus nextValues with
  | returned => cases second; exact ⟨rfl,rfl⟩
  | trapped => cases second; exact ⟨rfl,rfl⟩
  | yes source ih => cases second with | yes other => exact ih other
  | no source ih => cases second with | no other => exact ih other

end Exec.Theorems.PureCallbacks

namespace Exec.Theorems.StoreCallbacks
open Aeneas Aeneas.Std

inductive WriteI32Result {M : Type} (before : runtime.store.Store M) (index : Usize) (value : U32) :
    Bool → runtime.store.Store M → Prop
  | accepted (inside : index.val < before.globals.length)
      (mutable : (before.globals.val[index.val]).ty.mutability = .Var)
      (typed : (before.globals.val[index.val]).ty.valtype = .I32) :
      WriteI32Result before index value true
        ({before with globals := (before.globals.set index
          {before.globals.val[index.val] with lo := UScalar.cast .U64 value,hi := 0#u64})})
  | invalid (outside : ¬ index.val < before.globals.length) : WriteI32Result before index value false before
  | immutable (inside : index.val < before.globals.length)
      (immutable : (before.globals.val[index.val]).ty.mutability ≠ .Var) : WriteI32Result before index value false before
  | mismatch (inside : index.val < before.globals.length)
      (mismatch : (before.globals.val[index.val]).ty.valtype ≠ .I32) : WriteI32Result before index value false before

inductive Returns {M : Type} : Program → runtime.store.Store M →
    core.result.Result Unit runtime.platform.HostError → runtime.store.Store M → List runtime.Value → Prop
  | terminal {reply status values} (source : PureCallbacks.Returns reply status values) (store : runtime.store.Store M) :
      Returns (.terminal reply) store status store values
  | write {index value next before middle status after values}
      (effect : WriteI32Result before index value true middle)
      (tail : Returns next middle status after values) :
      Returns (.writeI32 index value next) before status after values
  | rejected {index value next before after} (effect : WriteI32Result before index value false after) :
      Returns (.writeI32 index value next) before (.Err .Trap) after []
  | yes {yes no before status after values} (source : Returns yes before status after values) :
      Returns (.branch true yes no) before status after values
  | no {yes no before status after values} (source : Returns no before status after values) :
      Returns (.branch false yes no) before status after values

theorem WriteI32Result.deterministic {M : Type} {before after next : runtime.store.Store M}
    {index value accepted nextAccepted}
    (first : WriteI32Result before index value accepted after)
    (second : WriteI32Result before index value nextAccepted next) : accepted = nextAccepted ∧ after = next := by
  cases first <;> cases second <;> first | exact ⟨rfl,rfl⟩ | contradiction

theorem Returns.deterministic {M : Type} {program : Program} {before after next : runtime.store.Store M}
    {status nextStatus values nextValues}
    (first : Returns program before status after values)
    (second : Returns program before nextStatus next nextValues) :
    status = nextStatus ∧ after = next ∧ values = nextValues := by
  induction first generalizing nextStatus next nextValues with
  | terminal source store =>
    cases second with
    | terminal other => exact ⟨(source.deterministic other).1,rfl,(source.deterministic other).2⟩
  | write effect tail ih =>
    cases second with
    | write other rest =>
      have same := (effect.deterministic other).2
      subst_vars
      exact ih rest
    | rejected other => cases (effect.deterministic other).1
  | rejected effect =>
    cases second with
    | write other rest => cases (effect.deterministic other).1
    | rejected other => exact ⟨rfl,(effect.deterministic other).2,rfl⟩
  | yes source ih => cases second with | yes other => exact ih other
  | no source ih => cases second with | no other => exact ih other

private theorem write_refines {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (index : Usize) (value : U32)
    (inside : index.val < store.globals.length) :
    runtime.store.Store.set_global memory store ⟨store.id,index⟩ (.I32 value) ⦃ answer =>
      (answer.1 = .Ok () ∧ WriteI32Result store index value true answer.2) ∨
      (∃ error, answer.1 = .Err error ∧ WriteI32Result store index value false answer.2) ⦄ := by
  have owned : Store.ValueInStore store (.I32 value) := ⟨trivial,trivial⟩
  by_cases mutable : (store.globals.val[index.val]).ty.mutability = .Var
  · by_cases typed : (store.globals.val[index.val]).ty.valtype = .I32
    · apply WP.spec_mono (Store.global_write memory store index (.I32 value) inside mutable typed owned.1)
      rintro answer ⟨words,encoded,_,same⟩
      have canonical : words = (UScalar.cast .U64 value,0#u64) := by
        simpa [runtime.value.encode,lift] using encoded.symm
      rw [same,canonical]
      exact Or.inl ⟨rfl,.accepted inside mutable typed⟩
    · apply WP.spec_mono (Store.global_write_rejected memory store index (.I32 value) inside owned (Or.inr typed))
      intro answer same
      rw [same]
      exact Or.inr ⟨_,rfl,.mismatch inside typed⟩
  · apply WP.spec_mono (Store.global_write_rejected memory store index (.I32 value) inside owned (Or.inl mutable))
    intro answer same
    rw [same]
    exact Or.inr ⟨_,rfl,.immutable inside mutable⟩

/-- The actual callback interpreter returns normally and refines the independent
operation semantics. No invariant, host law, or assumed action trace is needed. -/
theorem Program.refines {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (program : Program) (store : runtime.store.Store M) :
    program.run memory store ⦃ answer => Returns program store answer.1 answer.2.1 answer.2.2.val ⦄ := by
  induction program generalizing store with
  | terminal reply => exact WP.spec.ret (.terminal reply.refines store)
  | branch condition yes no hy hn =>
    cases condition with
    | false => exact WP.spec_mono (hn store) (fun _ source => .no source)
    | true => exact WP.spec_mono (hy store) (fun _ source => .yes source)
  | writeI32 index value next ih =>
    unfold Program.run
    split
    · rename_i inside
      obtain ⟨answer,actual,source⟩ := WP.spec_imp_exists (write_refines memory store index value inside)
      rw [actual,bind_ok]
      rcases source with ⟨status,effect⟩ | ⟨error,status,effect⟩
      · rw [status]
        exact WP.spec_mono (ih answer.2) (fun _ tail => .write effect tail)
      · rw [status]
        exact WP.spec.ret (.rejected effect)
    · exact WP.spec.ret (.rejected (.invalid (by assumption)))

/-- A finite independent action derivation determines an actual normal
implementation return. This discharges callback normality for the class. -/
theorem Returns.actual {M : Type} (memory : runtime.platform.MemoryBuffer M)
    {program : Program} {before after : runtime.store.Store M} {status values}
    (source : Returns program before status after values) :
    ∃ returned : Slice runtime.Value,
      program.run memory before = .ok (status,after,returned) ∧ returned.val = values := by
  obtain ⟨⟨actualStatus,actualStore,actualValues⟩,actual,refined⟩ :=
    WP.spec_imp_exists (program.refines memory before)
  obtain ⟨rfl,rfl,same⟩ := source.deterministic refined
  exact ⟨actualValues,actual,same.symm⟩

end Exec.Theorems.StoreCallbacks
