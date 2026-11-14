import Itasca.Generated.Types
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.Equations.Bytecode
import Itasca.Generated.FunsRuntimeCommon
import SpecExt.Builtins.Float.Sign

/-!
Sections, each formerly its own module: Alloc, Recording, ReturnedLoop, Memory, Float, DivSpec, Laws.
-/

/-! ## Alloc -/

section

/-!
Allocator content-preservation and normal-return laws, with a separate allocation-availability premise. Compiler and runtime proofs distinguish valid allocation behavior from requests being granted.
-/

namespace Itasca.Runtime.Platform
open Aeneas Aeneas.Std

/-- Allocation may report either answer but must return normally and preserve
all modeled vector contents. Native capacity is outside Aeneas's vector model. -/
def AllocCorrect {A : Type} (ops : runtime.platform.Alloc A) : Prop :=
  ∀ (T : Type) (values : alloc.vec.Vec T) (additional : Usize),
    ops.reserve values additional ⦃ result => result.2 = values ⦄

theorem AllocCorrect.reserve_eq {A T : Type} {ops : runtime.platform.Alloc A}
    (h : AllocCorrect ops) (values : alloc.vec.Vec T) (additional : Usize) :
    ∃ answer, ops.reserve values additional = .ok (answer, values) := by
  obtain ⟨⟨answer, after⟩, hr, hp⟩ := WP.spec_imp_exists (h T values additional)
  dsimp only at hp
  subst after
  exact ⟨answer, hr⟩

/-- Every reserve request whose resulting logical length is within `bound`
succeeds. The bound is independent of any client computation or its result;
clients must prove that their requests fit it. Native capacity is unmodeled. -/
def AllocationAvailable {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) : Prop :=
  ∀ (T : Type) (values : alloc.vec.Vec T) (additional : Usize),
    values.val.length + additional.val ≤ bound →
    ops.reserve values additional = .ok (true, values)

end Itasca.Runtime.Platform

end

/-! ## Recording -/

section

/-!
Exact host-event instrumentation. Erasure, bind composition, partial correctness and loop transport preserve the actual recorded event sequence used by invocation constructions.
-/

/-! ## Recording -/

section

namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt

/-- Proof-only instrumentation records events at an interpreter call site,
after its result checker has determined the observable outcome. -/
def run {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) : Result (α × List HostEvent) := do
  let answer ← operation
  Result.ok (answer,prior ++ events answer)

/-- Erasing instrumentation preserves the exact computation, including
ordinary failure and divergence. -/
theorem erase {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) :
    (do let (answer,_) ← run operation events prior; Result.ok answer) = operation := by
  simp only [run,Std.bind_assoc,bind_ok,Std.uncurry,Std.bind_pure]

/-- Returning instrumented executions append precisely the site's event list. -/
theorem returned {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) (answer : α) (trace : List HostEvent) :
    run operation events prior = .ok (answer,trace) ↔
      operation = .ok answer ∧ trace = prior ++ events answer := by
  constructor
  · intro result
    have original := erase operation events prior
    rw [result,bind_ok] at original
    have exactRun : operation = .ok answer := original.symm
    refine ⟨exactRun,?_⟩
    simpa only [run,exactRun,bind_ok,Result.ok.injEq,Prod.mk.injEq,true_and] using result.symm
  · rintro ⟨operationEq,rfl⟩
    simp only [run,operationEq,bind_ok]

end Itasca.Runtime.Platform.Recording

end

/-! ## Recording Bind -/

section

namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt

theorem bind_erase_cont {α β : Type}
    (recorded : Result (α × List HostEvent)) (original : Result α)
    (next : α × List HostEvent → Result β) (plainNext : α → Result β)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (continued : ∀answer trace, next (answer,trace)=plainNext answer) :
    Std.bind recorded next = Std.bind original plainNext := by
  rw [←erase]
  simp only [Std.bind_assoc]
  apply congrArg (Std.bind recorded)
  funext pair
  rcases pair with ⟨answer,trace⟩
  simpa only [Std.uncurry,bind_ok] using continued answer trace
end Itasca.Runtime.Platform.Recording

end

/-! ## Recording Loop -/

section

namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt Lean.Order Aeneas.Data.Coinductive
unseal Result

/-- The extracted Result effect has only terminal failure; its order is flat.
This fact is proved from the library's interaction-tree order. -/
theorem result_le_flat {α : Type} {a b : Result α} (h : a ⊑ b) : a=.div ∨ a=b := by
  have step := Eq.mp (ITree.le_unfold (E:=RustEffect) a b) h
  rcases step with same | ⟨value,ha,hb⟩ | ⟨eff,k,j,ha,hb,rest⟩
  · exact Or.inl same
  · exact Or.inr (ha.trans hb.symm)
  · right
    apply ha.trans
    apply Eq.trans _ hb.symm
    congr 1
    funext x
    cases eff
    cases x

/-- Any predicate containing divergence is admissible for this flat result. -/
theorem result_admissible {α : Type} (P : Result α → Prop) (bottom : P .div) : admissible P := by
  intro c hc hp
  by_cases hasNondiv : ∃ a,c a ∧ a≠.div
  · obtain ⟨a,member,nondiv⟩ := hasNondiv
    have upper : ∀b,c b → b ⊑ a := by
      intro b present
      rcases hc a b member present with order | order
      · rcases result_le_flat order with impossible | same
        · exact False.elim (nondiv impossible)
        · rw [same]
      · exact order
    have equal : CCPO.csup hc=a := PartialOrder.rel_antisymm (csup_le hc upper) (le_csup hc member)
    rw [equal]
    exact hp a member
  · have upper : ∀b,c b → b ⊑ Result.div := by
      intro b present
      have same : b=Result.div := by
        by_contra different
        exact hasNondiv ⟨b,present,different⟩
      rw [same]
    have equal : CCPO.csup hc=Result.div := ITree.le_div_is_div _ (csup_le hc upper)
    rw [equal]
    exact bottom

seal Result

/-- Append each concrete body outcome before taking its continue/done branch. -/
def loopBody {α β : Type} (body : α → Result (ControlFlow α β))
    (events : α → ControlFlow α β → List HostEvent) (state : α × List HostEvent) :
    Result (ControlFlow (α × List HostEvent) (β × List HostEvent)) := do
  let out ← body state.1
  let trace := state.2++events state.1 out
  match out with
  | .cont next => .ok (.cont (next,trace))
  | .done result => .ok (.done (result,trace))

/-- Proof-only writer instrumentation of the original least-fixed-point loop. -/
def loop {α β : Type} (body : α → Result (ControlFlow α β))
    (events : α → ControlFlow α β → List HostEvent) (initial : α) (prior : List HostEvent) :
    Result (β × List HostEvent) := Aeneas.Std.loop (loopBody body events) (initial,prior)

private theorem bind_right_mono {α β : Type} (r : Result α) (f g : α → Result β)
    (h : ∀x,f x ⊑ g x) : (do let x←r; f x) ⊑ (do let x←r; g x) := by
  exact Aeneas.Std.bind_mono (fun _ : α → Result β=>r) (fun k=>k) (monotone_const _) monotone_id f g h

unseal Result in
private theorem result_div_le {α : Type} (r : Result α) : Result.div ⊑ r := by
  exact Eq.mpr (ITree.le_unfold (E:=RustEffect) _ _) (Or.inl rfl)

/-- Removing the log recovers the exact original computation, including
failure and divergence, without any body correctness or termination premise. -/
theorem loop_erase {α β : Type} (body : α → Result (ControlFlow α β))
    (events : α → ControlFlow α β → List HostEvent) (initial : α) (prior : List HostEvent) :
    (do let (answer,_) ← loop body events initial prior; Result.ok answer) = Aeneas.Std.loop body initial := by
  apply PartialOrder.rel_antisymm
  · have adm : admissible (fun run : α × List HostEvent → Result (β × List HostEvent) =>
      ∀state,(do let (answer,_)←run state; Result.ok answer) ⊑ Aeneas.Std.loop body state.1) := by
      apply admissible_pi
      intro state
      apply admissible_apply (fun (_ : α × List HostEvent) (value : Result (β × List HostEvent))=>(do let (answer,_)←value; Result.ok answer) ⊑ Aeneas.Std.loop body state.1) state
      apply result_admissible
      simpa only [bind_div] using result_div_le (Aeneas.Std.loop body state.1)
    change (do let (answer,_)←Aeneas.Std.loop (loopBody body events) (initial,prior); Result.ok answer) ⊑ _
    apply Aeneas.Std.loop.fixpoint_induct (loopBody body events) _ adm ?_ (initial,prior)
    intro run ih state
    rw [Aeneas.Std.loop.eq_def body state.1]
    simp only [loopBody,Std.bind_assoc]
    apply bind_right_mono
    intro out
    cases out with
    | done result => simp only [bind_ok]; exact PartialOrder.rel_refl
    | cont next => simpa only [bind_ok] using ih (next,state.2++events state.1 (.cont next))
  · have adm : admissible (fun run : α → Result β =>
      ∀state prior,run state ⊑ (do let (answer,_)←loop body events state prior; Result.ok answer)) := by
      apply admissible_pi
      intro state
      apply admissible_pi
      intro prior
      apply admissible_apply (fun (_ : α) (value : Result β)=>value ⊑ (do let (answer,_)←loop body events state prior; Result.ok answer)) state
      exact result_admissible _ (result_div_le _)
    apply Aeneas.Std.loop.fixpoint_induct body _ adm ?_ initial prior
    intro run ih state prior
    unfold loop
    rw [Aeneas.Std.loop.eq_def (loopBody body events) (state,prior)]
    simp only [loopBody,Std.bind_assoc]
    apply bind_right_mono
    intro out
    cases out with
    | done result => simp only [bind_ok]; exact PartialOrder.rel_refl
    | cont next => simpa only [bind_ok,loop] using ih next (prior++events state (.cont next))

end Itasca.Runtime.Platform.Recording

end

/-! ## Recording Spec -/

section

namespace Itasca.Runtime.Platform.Recording
open Aeneas Aeneas.Std SpecExt
/-- A returning trace witness lifts partial correctness through exact erasure.
The divergence branch follows from erasure and adds no termination premise. -/
theorem lift_dspec {α : Type} (recorded : Result (α × List HostEvent)) (original : Result α)
    (P : α → Prop) (Q : α × List HostEvent → Prop)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (checked : original ⦃ answer => P answer ⦄div)
    (returned : ∀answer,P answer → ∃trace, recorded=.ok (answer,trace) ∧ Q (answer,trace)) :
    recorded ⦃ pair => Q pair ⦄div := by
  cases checked with
  | ret held =>
    obtain ⟨trace,same,post⟩ := returned _ held
    rw [same]
    exact WP.dspec.ret post
  | div =>
    cases recorded using Result.cases with
    | ret pair =>
      rcases pair with ⟨answer,trace⟩
      simp only [bind_ok] at erase
      change Result.ok answer = .div at erase
      exact False.elim (ok_not_div erase)
    | div => exact WP.dspec.div _
    | vis e k => simp only [bind_vis,vis_not_div] at erase
/-- Erasure retains a graph witness identifying the exact returned log. -/
theorem erase_dspec {α : Type} (recorded : Result (α × List HostEvent)) (original : Result α)
    (Q : α × List HostEvent → Prop)
    (erase : (do let (answer,_) ← recorded; Result.ok answer)=original)
    (checked : recorded ⦃ pair => Q pair ⦄div) :
    original ⦃ answer => ∃trace, recorded=.ok (answer,trace) ∧ Q (answer,trace) ⦄div := by
  generalize actual : recorded=operation at checked
  cases checked with
  | ret held =>
    rw [←erase,actual,bind_ok]
    exact WP.dspec.ret ⟨_,rfl,held⟩
  | div =>
    rw [←erase,actual,bind_div]
    exact WP.dspec.div _
end Itasca.Runtime.Platform.Recording

end

end

/-! ## ReturnedLoop -/

section

/-!
Invariant witnesses for loops that return. Invocation recording uses this transport without adding a termination assumption to partial executions.
-/

namespace Itasca.Runtime.Platform
open Aeneas Aeneas.Std Lean.Order

private theorem returned_bind {α β : Type} (read : Result α) (next : α → Result β)
    (answer : β) (returned : (read >>= next) = .ok answer) :
    ∃ value, read = .ok value ∧ next value = .ok answer := by
  induction read using Result.cases with
  | ret value => exact ⟨value,rfl,by simpa using returned⟩
  | vis effect continuation => simp at returned
  | div => simp at returned

/-- An invariant follows every normally returning loop, even if the body may
fail or diverge on other states. This is a least-fixed-point induction, not a
termination assumption about the body. -/
theorem loop_returned_invariant {α β : Type} (body : α → Result (ControlFlow α β))
    (inv : α → Prop) (post : β → Prop)
    (step : ∀ state out, inv state → body state = .ok out →
      match out with | .cont next => inv next | .done answer => post answer)
    (state : α) (initial : inv state) (answer : β)
    (returned : loop body state = .ok answer) : post answer := by
  have adm : admissible (fun run : α → Result β =>
      ∀ state, inv state → ∀ answer, run state = .ok answer → post answer) := by
    apply admissible_pi
    intro state
    apply admissible_apply (fun _ (result : Result β) =>
      inv state → ∀ answer, result = .ok answer → post answer) state
    apply Recording.result_admissible
    intro _ answer impossible
    simp at impossible
  have held : ∀ state, inv state → ∀ answer, loop body state = .ok answer → post answer := by
    apply loop.fixpoint_induct body _ adm
    intro run ih state initial answer returned
    obtain ⟨out,called,tail⟩ := returned_bind _ _ _ returned
    have next := step state out initial called
    cases out with
    | done result =>
      simp at tail
      subst result
      exact next
    | cont state => exact ih state next answer tail
  exact held state initial answer returned

end Itasca.Runtime.Platform

end

/-! ## Memory -/

section

/-!
Memory-buffer laws relating platform operations to visible bytes and lengths. Runtime memory and store proofs assume these embedding obligations.
-/

namespace Itasca.Runtime.Platform
open Aeneas Aeneas.Std

/-- Laws for the actual extracted memory dictionary, relative to the bytes used
by the store decoder. No promise of successful allocation or growth is made. -/
structure MemoryLaws {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) : Prop where
  read : ∀ m, ops.bytes m = .ok (view m)
  write : ∀ m, ∃ back, ops.bytes_mut m = .ok (view m, back) ∧
    ∀ bytes, bytes.length = (view m).length → view (back bytes) = bytes
  create : ∀ n, ops.new_zeroed n ⦃ result =>
    ∀ m, result = some m → (view m).val = List.replicate n.val 0#u8 ⦄
  grow : ∀ m n, ops.grow m n ⦃ result =>
    if result.1 then (view m).length ≤ n.val ∧
      (view result.2).val = (view m).val ++
        List.replicate (n.val - (view m).length) 0#u8
    else view result.2 = view m ⦄

end Itasca.Runtime.Platform

end

/-! ## Float -/

section

/-! Exact embedding contract for the extracted float dictionary. Every method
returns normally. Finite/infinite results must belong to the specification set;
any raw NaN is allowed only when that set contains a NaN. Canonicalization is
an interpreter obligation, not an extra restriction on the embedding payload. -/

namespace Itasca.Runtime.Platform
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float

def FloatOutcome (value : fN) (allowed : List fN) : Prop :=
  if isNaN value then ∃ choice ∈ allowed, isNaN choice = true else value ∈ allowed

theorem float_outcome_non_nan {value : fN} {allowed : List fN}
    (h : FloatOutcome value allowed) (hn : isNaN value = false) : value ∈ allowed := by
  simpa [FloatOutcome, hn] using h

theorem float_outcome_nan {value : fN} {allowed : List fN}
    (h : FloatOutcome value allowed) (hn : isNaN value = true) :
    ∃ choice ∈ allowed, isNaN choice = true := by
  simpa [FloatOutcome, hn] using h

/-- A1 for all 27 rounding operations in the actual extracted dictionary. -/
structure FloatOpsCorrect {F : Type} (ops : runtime.platform.FloatOps F) : Prop where
  f32_add : ∀ a b, ops.f32_add a b ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fadd_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) ⦄
  f32_sub : ∀ a b, ops.f32_sub a b ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fsub_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) ⦄
  f32_mul : ∀ a b, ops.f32_mul a b ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fmul_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) ⦄
  f32_div : ∀ a b, ops.f32_div a b ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fdiv_ 32 (floatOfBits 32 a.val) (floatOfBits 32 b.val)) ⦄
  f32_sqrt : ∀ a, ops.f32_sqrt a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fsqrt_ 32 (floatOfBits 32 a.val)) ⦄
  f32_ceil : ∀ a, ops.f32_ceil a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fceil_ 32 (floatOfBits 32 a.val)) ⦄
  f32_floor : ∀ a, ops.f32_floor a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (ffloor_ 32 (floatOfBits 32 a.val)) ⦄
  f32_trunc : ∀ a, ops.f32_trunc a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (ftrunc_ 32 (floatOfBits 32 a.val)) ⦄
  f32_nearest : ∀ a, ops.f32_nearest a ⦃ result => FloatOutcome (floatOfBits 32 result.val) (fnearest_ 32 (floatOfBits 32 a.val)) ⦄
  f32_convert_i32_s : ∀ a, ops.f32_convert_i32_s a ⦃ result => FloatOutcome (floatOfBits 32 result.val) [convert__ 32 32 .S (.mk_uN (IScalar.hcast .U32 a).val)] ⦄
  f32_convert_i32_u : ∀ a, ops.f32_convert_i32_u a ⦃ result => FloatOutcome (floatOfBits 32 result.val) [convert__ 32 32 .U (.mk_uN a.val)] ⦄
  f32_convert_i64_s : ∀ a, ops.f32_convert_i64_s a ⦃ result => FloatOutcome (floatOfBits 32 result.val) [convert__ 64 32 .S (.mk_uN (IScalar.hcast .U64 a).val)] ⦄
  f32_convert_i64_u : ∀ a, ops.f32_convert_i64_u a ⦃ result => FloatOutcome (floatOfBits 32 result.val) [convert__ 64 32 .U (.mk_uN a.val)] ⦄
  f64_add : ∀ a b, ops.f64_add a b ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fadd_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  f64_sub : ∀ a b, ops.f64_sub a b ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fsub_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  f64_mul : ∀ a b, ops.f64_mul a b ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fmul_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  f64_div : ∀ a b, ops.f64_div a b ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fdiv_ 64 (floatOfBits 64 a.val) (floatOfBits 64 b.val)) ⦄
  f64_sqrt : ∀ a, ops.f64_sqrt a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fsqrt_ 64 (floatOfBits 64 a.val)) ⦄
  f64_ceil : ∀ a, ops.f64_ceil a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fceil_ 64 (floatOfBits 64 a.val)) ⦄
  f64_floor : ∀ a, ops.f64_floor a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (ffloor_ 64 (floatOfBits 64 a.val)) ⦄
  f64_trunc : ∀ a, ops.f64_trunc a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (ftrunc_ 64 (floatOfBits 64 a.val)) ⦄
  f64_nearest : ∀ a, ops.f64_nearest a ⦃ result => FloatOutcome (floatOfBits 64 result.val) (fnearest_ 64 (floatOfBits 64 a.val)) ⦄
  f64_convert_i32_s : ∀ a, ops.f64_convert_i32_s a ⦃ result => FloatOutcome (floatOfBits 64 result.val) [convert__ 32 64 .S (.mk_uN (IScalar.hcast .U32 a).val)] ⦄
  f64_convert_i32_u : ∀ a, ops.f64_convert_i32_u a ⦃ result => FloatOutcome (floatOfBits 64 result.val) [convert__ 32 64 .U (.mk_uN a.val)] ⦄
  f64_convert_i64_s : ∀ a, ops.f64_convert_i64_s a ⦃ result => FloatOutcome (floatOfBits 64 result.val) [convert__ 64 64 .S (.mk_uN (IScalar.hcast .U64 a).val)] ⦄
  f64_convert_i64_u : ∀ a, ops.f64_convert_i64_u a ⦃ result => FloatOutcome (floatOfBits 64 result.val) [convert__ 64 64 .U (.mk_uN a.val)] ⦄
  f32_demote_f64 : ∀ a, ops.f32_demote_f64 a ⦃ result =>
    FloatOutcome (floatOfBits 32 result.val) (demote__ 64 32 (floatOfBits 64 a.val)) ⦄

theorem float_outcome_canonicalize (width : Nat) (value : fN) (allowed : List fN)
    (h : FloatOutcome value allowed) (hc : CanonicalClosed width allowed) :
    (if isNaN value then fN.POS (.NAN (canon_ width)) else value) ∈ allowed := by
  cases hn : isNaN value
  · simpa [hn] using float_outcome_non_nan h hn
  · simpa [hn] using hc (float_outcome_nan h hn)

end Itasca.Runtime.Platform

end

/-! ## DivSpec -/

section

/-! Partial correctness that names the cause of divergence. `step` accepts `DivSpec` goals and
lifts total `spec` theorems into them. -/
namespace Itasca.Runtime
open Aeneas Aeneas.Std

/-- `m` returns a value satisfying `post`, or diverges and `cause` holds. -/
inductive DivSpec {α : Type} (cause : Prop) : Result α → WP.Post α → Prop where
  | ret {post : WP.Post α} {x : α} : post x → DivSpec cause (.ok x) post
  | div (post : WP.Post α) : cause → DivSpec cause .div post

namespace DivSpec

theorem mono {α : Type} {cause : Prop} {P₁ : WP.Post α} {m : Result α} {P₀ : WP.Post α}
    (h : DivSpec cause m P₀) : (∀ x, P₀ x → P₁ x) → DivSpec cause m P₁ := by
  intro weaken
  cases h with
  | ret post => exact .ret (weaken _ post)
  | div _ diverged => exact .div _ diverged

theorem bind {α β : Type} {cause : Prop} {k : α → Result β} {Pₖ : WP.Post β} {m : Result α}
    {Pₘ : WP.Post α} :
    DivSpec cause m Pₘ → (∀ x, Pₘ x → DivSpec cause (k x) Pₖ) → DivSpec cause (Std.bind m k) Pₖ := by
  intro first rest
  cases first with
  | ret post => rw [bind_ok]; exact rest _ post
  | div _ diverged => rw [bind_div]; exact .div _ diverged

theorem of_spec (cause : Prop) (α : Type) (m : Result α) (post : WP.Post α)
    (h : WP.spec m post) : DivSpec cause m post := by
  cases h with
  | ret post => exact .ret post

theorem of_dspec {α : Type} {cause : Prop} {m : Result α} {post : WP.Post α}
    (h : WP.dspec m post) (diverged : m = .div → cause) : DivSpec cause m post := by
  cases h with
  | ret post => exact .ret post
  | div _ => exact .div _ (diverged rfl)

theorem dspec {α : Type} {cause : Prop} {m : Result α} {post : WP.Post α}
    (h : DivSpec cause m post) : WP.dspec m post := by
  cases h with
  | ret post => exact .ret post
  | div _ _ => exact .div _

theorem diverged {α : Type} {cause : Prop} {m : Result α} {post : WP.Post α}
    (h : DivSpec cause m post) (divergent : m = .div) : cause := by
  cases h with
  | ret _ => exact absurd divergent ok_not_div
  | div _ cause => exact cause

/-- A computation that returns, or diverges with its cause. -/
theorem imp_exists {α : Type} {cause : Prop} {m : Result α} {post : WP.Post α}
    (h : DivSpec cause m post) : (∃ x, m = .ok x ∧ post x) ∨ (m = .div ∧ cause) := by
  cases h with
  | ret post => exact Or.inl ⟨_, rfl, post⟩
  | div _ diverged => exact Or.inr ⟨rfl, diverged⟩

/-- Divergence without a cause is impossible, so the computation returns. -/
theorem spec {α : Type} {m : Result α} {post : WP.Post α} (h : DivSpec False m post) :
    WP.spec m post := by
  cases h with
  | ret post => exact .ret post
  | div _ impossible => exact impossible.elim

@[simp] theorem ok_iff {α : Type} {cause : Prop} {x : α} {post : WP.Post α} :
    DivSpec cause (.ok x) post ↔ post x := by
  constructor
  · intro h
    rcases h.imp_exists with ⟨y, same, holds⟩ | ⟨impossible, _⟩
    · rw [Result.ok_injective same]; exact holds
    · exact absurd impossible ok_not_div
  · exact .ret

end DivSpec

#register_spec_info {
    spec_name := ``Itasca.Runtime.DivSpec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``Itasca.Runtime.DivSpec.mono
    mk_spec_mono_skip_args := 3
    mk_spec_bind := ``Itasca.Runtime.DivSpec.bind
    mk_spec_bind_skip_args := 5
    prepare_intro_outputs := ``Aeneas.Step.prepareIntroOutputs
    to_mvcgen := .none
    liftings := #[
      { from_statement := ``Aeneas.Std.WP.spec
        conversion_thm := ``Itasca.Runtime.DivSpec.of_spec
        conversion_thm_inferred_args := 4 }
    ]
  }

end Itasca.Runtime

end

/-! ## Laws -/

section

/-!
The platform-law bundle for floating point, allocation, memory and normal-returning interrupts. Public runtime constructions take this shared embedding contract.
-/

namespace Itasca.Runtime.Platform
open Aeneas Aeneas.Std

/-- The laws of the platform operations used by execution. -/
structure Laws {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) : Prop where
  floatsCorrect : FloatOpsCorrect floats
  allocCorrect : AllocCorrect allocator
  interruptsReturn : ∀ p, hooks.interrupt p ⦃ _ => True ⦄
  memoryLaws : MemoryLaws memory view

end Itasca.Runtime.Platform

end
