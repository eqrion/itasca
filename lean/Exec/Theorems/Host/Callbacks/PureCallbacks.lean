import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Host.HostWorldSound
import Exec.Store.Invariant.IssuedValues
import Exec.Interp.Relations.FrameStorePrefix

/-! An executable, store-independent callback class. These are implementations
of the extracted Platform interface, not contracts assumed of native callbacks.
Mutation, publication, and nested invocation require additional actions. -/
namespace Exec.Theorems.PureCallbacks
open Aeneas Aeneas.Std

/-- Pure callbacks can return numeric literals or null references. They cannot
manufacture a same-store address. -/
inductive Literal where
  | i32 (bits : U32)
  | i64 (bits : U64)
  | f32 (bits : U32)
  | f64 (bits : U64)
  | v128 (bits : U128)
  | nullFunc
  | nullExtern

def Literal.value : Literal → runtime.Value
  | .i32 bits => .I32 bits
  | .i64 bits => .I64 bits
  | .f32 bits => .F32 bits
  | .f64 bits => .F64 bits
  | .v128 bits => .V128 bits
  | .nullFunc => .FuncRef none
  | .nullExtern => .ExternRef none

/-- Finite local control and explicit return or host trap. No operation grants
access to the concrete store or a mutable memory borrow. -/
inductive Program where
  | returned (values : Slice Literal)
  | trapped
  | branch (condition : Bool) (yes no : Program)

def Program.evaluate : Program → core.result.Result Unit runtime.platform.HostError × Slice runtime.Value
  | .returned values => (.Ok (), Slice.from (values.val.map Literal.value) (by simpa using values.property))
  | .trapped => (.Err .Trap, Slice.new _)
  | .branch condition yes no => if condition then yes.evaluate else no.evaluate

/-- Independent finite control semantics. It records the values selected by
literal return and follows only the chosen branch. -/
inductive Returns : Program → core.result.Result Unit runtime.platform.HostError → List runtime.Value → Prop
  | returned (values : Slice Literal) : Returns (.returned values) (.Ok ()) (values.val.map Literal.value)
  | trapped : Returns .trapped (.Err .Trap) []
  | yes {yes no : Program} {status values} : Returns yes status values → Returns (.branch true yes no) status values
  | no {yes no : Program} {status values} : Returns no status values → Returns (.branch false yes no) status values

/-- The executable evaluator refines the independent control semantics. -/
theorem Program.refines (program : Program) :
    Returns program program.evaluate.1 program.evaluate.2.val := by
  induction program with
  | returned values => simpa only [Program.evaluate,Slice.from_val] using Returns.returned values
  | trapped => exact .trapped
  | branch condition yes no hy hn =>
    cases condition with
    | false => exact .no hn
    | true => exact .yes hy

/-- Every output value is issued, independently of the callback's arguments. -/
theorem Program.issued {M : Type} (program : Program) (store : runtime.store.Store M) :
    ∀ value ∈ program.evaluate.2.val, Store.IssuedValue store value := by
  induction program with
  | returned values =>
    intro value member
    simp only [Program.evaluate,Slice.from_val,List.mem_map] at member
    obtain ⟨literal,_,rfl⟩ := member
    cases literal <;> trivial
  | trapped => simp [Program.evaluate]
  | branch condition yes no hy hn => cases condition <;> assumption

/-- Literal results belong to the current store; pure code cannot manufacture
foreign references or unissued addresses. -/
theorem Program.in_store {M : Type} (program : Program) (store : runtime.store.Store M) :
    ∀value∈program.evaluate.2.val,Store.ValueInStore store value := by
  induction program with
  | returned values=>
    intro value member
    simp only [Program.evaluate,Slice.from_val,List.mem_map] at member
    obtain ⟨literal,_,rfl⟩ := member
    cases literal <;> exact ⟨trivial,trivial⟩
  | trapped=>simp [Program.evaluate]
  | branch condition yes no hy hn=>cases condition <;> assumption

/-- Total program selection may inspect the host identity and copied arguments.
It receives no raw store, metadata, or mutable-memory capability. -/
def platform {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Program) : runtime.platform.Platform Unit M where
  MemoryBufferInst := memory
  interrupt token := .ok (.Continue,token)
  call_host token store identity args _ :=
    let reply := (select identity args).evaluate
    .ok (reply.1,token,store,reply.2)

/-- The complete host source-store obligation is derived from this executable
implementation and the public invariant's typing theorem. -/
theorem sound {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Program) (view : M → Slice U8)
    (code : Store.CodeInterpretation) :
    Platform.HostSound (platform memory select) (ExecutableInv view code) (Store.decodeStore view code) := by
  apply Platform.HostSound.of_invariant (fun _ held => held.source_typed)
  intro token store identity args results held
  exact WP.spec.ret ⟨held,Spec.extend_store_refl _ held.well_formed⟩

/-- Pure implementations also satisfy the world-indexed contract. -/
theorem world_sound {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Program) (view : M → Slice U8) :
    HostWorldSound (platform memory select) view (ExecutableInv view) :=
  HostWorldSound.of_fixed (sound memory select view)

/-- The implementation's result issuance contract has no callback-normality
or returned-action decomposition premise. -/
theorem issued {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Program) (token : Unit)
    (store : runtime.store.Store M) (identity : U64) (args results : Slice runtime.Value) :
    (platform memory select).call_host token store identity args results ⦃ answer =>
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value ⦄ :=
  WP.spec.ret ((select identity args).issued store)

/-- Host effects retain the exact raw frame metadata and extern count. -/
theorem retained {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Program) (token : Unit)
    (store : runtime.store.Store M) (identity : U64) (args results : Slice runtime.Value) :
    (platform memory select).call_host token store identity args results ⦃ answer =>
      Interp.FrameStorePrefix store answer.2.2.1 ∧
      store.externs.length = answer.2.2.1.externs.length ⦄ :=
  WP.spec.ret ⟨Interp.FrameStorePrefix.refl _,rfl⟩

/-- Finite callback control returns normally, and interrupts always continue. -/
theorem total {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Program) :
    Platform.HooksTotal (platform memory select) := by
  constructor
  · intro token; exact WP.spec.ret trivial
  · intro token store identity args results; exact WP.spec.ret trivial

end Exec.Theorems.PureCallbacks
