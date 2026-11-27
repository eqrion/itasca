import Aeneas
import ItascaRust.Types
import WebAssembly.Host
import WebAssembly

/-!
# Platform laws

Allocator, memory, floating-point and interrupt contracts state the behavior required of
generic platform operations. They are premises of runtime results, not conclusions about
native wrappers. Allocation refusal and resource limits remain observable possibilities.
Keeping these laws independent of store and execution certificates makes the external
obligations readable without following implementation proofs.

-/

/-! ## Platform -/

section Platform

/-!
## Conditional platform behavior

Allocator availability/correctness, memory and float laws, callback observations and the aggregate platform laws state what generic execution proofs require from their embedding.
-/

namespace Itasca.Platform

open Aeneas Aeneas.Std

/-- Allocation may report either answer but must return normally and preserve
all modeled vector contents. Native capacity is outside Aeneas's vector model. -/
def AllocCorrect {A : Type} (ops : runtime.platform.Alloc A) : Prop :=
  ∀ (T : Type) (values : alloc.vec.Vec T) (additional : Usize),
    ops.reserve values additional ⦃ result => result.2 = values ⦄

/-- Every reserve request whose resulting logical length is within `bound`
succeeds. The bound is independent of any client computation or its result;
clients must prove that their requests fit it. Native capacity is unmodeled. -/
def AllocationAvailable {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) : Prop :=
  ∀ (T : Type) (values : alloc.vec.Vec T) (additional : Usize),
    values.val.length + additional.val ≤ bound →
    ops.reserve values additional = .ok (true, values)

end Itasca.Platform

namespace Itasca.Platform

open Aeneas Aeneas.Std

/-- A completed callback exchange at the embedding boundary. The host identity
is the value passed to `call_host`, not a Wasm function address: multiple source
functions may share an embedding identity. Raw replies are retained because a
successful callback can still fail the caller's result-type validation. -/
structure HostObservation (M : Type) where
  before : runtime.store.Store M
  identity : U64
  arguments : Slice runtime.Value
  defaults : Slice runtime.Value
  result : core.result.Result Unit runtime.platform.HostError
  after : runtime.store.Store M
  returned : Slice runtime.Value

/-- Observe the platform itself, so every invocation uses the extracted
interpreter unchanged. Interrupts forward the embedding state and preserve the
log. A returning callback appends exactly its request and reply; panic and
divergence propagate without inventing a completed exchange. -/
def observing {M P : Type} (hooks : runtime.platform.Platform P M) :
    runtime.platform.Platform (P × List (HostObservation M)) M where
  MemoryBufferInst := hooks.MemoryBufferInst
  interrupt := fun (platform, prior) => do
    let (action, next) ← hooks.interrupt platform
    .ok (action, next, prior)
  call_host := fun (platform, prior) before identity arguments defaults => do
    let (result, next, after, returned) ← hooks.call_host platform before identity arguments defaults
    .ok (result, (next, prior ++ [⟨before, identity, arguments, defaults, result, after, returned⟩]),
      after, returned)

end Itasca.Platform

namespace Itasca.Platform

open Aeneas Aeneas.Std

/-- Laws for the actual extracted memory dictionary, relative to the bytes used
by the store decoder. No promise of successful allocation or growth is made. -/
structure MemoryLaws {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) : Prop where
  /-- Shared access returns exactly the bytes used by source-store decoding. -/
  read : ∀ m, ops.bytes m = .ok (view m)
  /-- Mutable access returns those bytes; writing back an equal-length slice
  makes that slice the new decoded view. -/
  write : ∀ m, ∃ back, ops.bytes_mut m = .ok (view m, back) ∧
    ∀ bytes, bytes.length = (view m).length → view (back bytes) = bytes
  /-- Creation returns normally; a supplied buffer has exactly `n` zero bytes. -/
  create : ∀ n, ops.new_zeroed n ⦃ result =>
    ∀ m, result = some m → (view m).val = List.replicate n.val 0#u8 ⦄
  /-- Growth returns normally, extending to the requested length with zeros on
  success and retaining the decoded view on refusal. -/
  grow : ∀ m n, ops.grow m n ⦃ result =>
    if result.1 then (view m).length ≤ n.val ∧
      (view result.2).val = (view m).val ++
        List.replicate (n.val - (view m).length) 0#u8
    else view result.2 = view m ⦄

end Itasca.Platform

namespace Itasca.Platform

open Aeneas Aeneas.Std WebAssembly.Builtins WebAssembly.Builtins.Float

/-- Non-NaN replies belong to the specified result set. A NaN reply requires
some permitted NaN outcome, without demanding identical NaN payloads. -/
def FloatOutcome (value : fN) (allowed : List fN) : Prop :=
  if isNaN value then ∃ choice ∈ allowed, isNaN choice = true else value ∈ allowed

/-- Each of the 27 extracted floating-point operations returns normally with
a reply satisfying FloatOutcome for its specification result set. -/
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

end Itasca.Platform

namespace Itasca.Platform

open Aeneas Aeneas.Std

/-- The laws of the platform operations used by execution. -/
structure Laws {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) : Prop where
  /-- Floating-point replies satisfy the stated arithmetic/conversion outcomes. -/
  floatsCorrect : FloatOpsCorrect floats
  /-- Allocation returns normally and retains logical vector contents. -/
  allocCorrect : AllocCorrect allocator
  /-- Interrupt checks return normally; they may still request termination. -/
  interruptsReturn : ∀ p, hooks.interrupt p ⦃ _ => True ⦄
  /-- Memory operations respect the canonical byte view and stated effects. -/
  memoryLaws : MemoryLaws memory view

end Itasca.Platform

end Platform
