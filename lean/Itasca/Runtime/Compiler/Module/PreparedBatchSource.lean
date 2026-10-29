import Itasca.Runtime.Compiler.Module.PreparedFunctionDemand
import Itasca.Runtime.Compiler.Module.PreparedFunctionAvailable
import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Module.Code.ReachedEntry
import Itasca.Module.Code.LocalsComplete
import Itasca.Runtime.Compiler.Module.EntryAvailable

/-!
Prepared compiler-batch source certificates. Entry uniqueness and conservative function-demand envelopes establish the batch source/resource relation.
-/

/-! ## Function Demand Envelope -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Conservative per-function charges from independent source maxima. -/
def functionDemandRate (bodyBytes localCount : Nat) : ChargeCounter → Nat
  | .instructions => 3*bodyBytes
  | .branches => bodyBytes
  | .controls => 1+bodyBytes
  | .locals => localCount

/-- Module-wide numerical headroom for uniformly bounded source functions.
The maxima concern source bytes, expanded locals, and validated operand depth;
no emitted target object or compilation result occurs here. -/
structure FunctionDemandEnvelope {A : Type} (budget : runtime.compiler.Budget A)
    (functions bodyBytes localCount peak bound : Nat) : Prop where
  size : bodyBytes ≤ limits.MAX_FUNCTION_BYTES.val
  counters : ∀ counter, (counter.used budget).val+functions*functionDemandRate bodyBytes localCount counter ≤
    (counter.limit budget).val
  temporary : 3*bodyBytes+3 ≤ bound
  locals : localCount ≤ bound
  operands : peak ≤ bound
  slots : 2*localCount+2*peak ≤ U32.max

/-- Each source function fits the remaining module-wide budget after the
preceding functions' conservative charges. -/
theorem FunctionDemandEnvelope.prepared {A : Type}
    {base budget : runtime.compiler.Budget A} {functions bodyBytes localCount peak bound processed}
    (envelope : FunctionDemandEnvelope base functions bodyBytes localCount peak bound)
    (paid : CompilationBudgetEffect base budget (fun counter => processed*functionDemandRate bodyBytes localCount counter))
    (remaining : processed < functions) (ctx : code.Context) (length operands : Nat)
    (bytes : length ≤ bodyBytes) (locals : ctx.locals.val.length ≤ localCount) (stack : operands ≤ peak) :
    PreparedFunctionDemand budget ctx length operands bound := by
  have counterRoom (counter : ChargeCounter) :
      (counter.used budget).val+functionDemandRate bodyBytes localCount counter ≤ (counter.limit budget).val := by
    have before := envelope.counters counter
    have used := (paid.counts counter).2
    have mult : (processed+1)*functionDemandRate bodyBytes localCount counter ≤ functions*functionDemandRate bodyBytes localCount counter :=
      Nat.mul_le_mul_right _ (by omega)
    have unchanged : counter.limit budget = counter.limit base := by
      cases counter <;> simp only [ChargeCounter.limit,paid.limits]
    rw [unchanged]
    simp only [Nat.add_mul,Nat.one_mul] at mult
    omega
  refine ⟨bytes.trans envelope.size,?_,?_,?_,?_,?_,locals.trans envelope.locals,stack.trans envelope.operands,?_⟩
  · have room := counterRoom .instructions
    simp only [ChargeCounter.used,ChargeCounter.limit,functionDemandRate] at room
    omega
  · have room := counterRoom .branches
    simp only [ChargeCounter.used,ChargeCounter.limit,functionDemandRate] at room
    omega
  · have room := counterRoom .controls
    simp only [ChargeCounter.used,ChargeCounter.limit,functionDemandRate] at room
    omega
  · have room := counterRoom .locals
    simp only [ChargeCounter.used,ChargeCounter.limit,functionDemandRate] at room
    omega
  · have room := envelope.temporary
    omega
  · have room := envelope.slots
    omega

/-- The exact prepared-function allowance fits the independent uniform rate. -/
theorem prepared_allowance_le_rate (ctx : code.Context) (length bodyBytes localCount : Nat)
    (bytes : length ≤ bodyBytes) (locals : ctx.locals.val.length ≤ localCount) :
    ∀ counter, preparedFunctionAllowance ctx length counter ≤ functionDemandRate bodyBytes localCount counter := by
  intro counter
  cases counter <;> simp only [preparedFunctionAllowance,functionDemandRate] <;> omega

end Itasca.Runtime.Code

end

/-! ## Prepared Entry Unique -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Pure entry decoding determines all inputs to source body demand. Grouping
of declared locals does not affect the expanded context consumed by compilation. -/
theorem prepared_entry_unique {data env index start profile}
    (first second : CodeEntry.Prepared data env index start profile) :
    first.typeIdx = second.typeIdx ∧ first.ctx = second.ctx ∧ first.body = second.body ∧
      first.bodyStart = second.bodyStart ∧ first.finish = second.finish := by
  have typeEq : first.typeIdx = second.typeIdx := first.index_type.symm.trans second.index_type
  have functionEq : first.ft = second.ft := by
    have left := first.function_type
    have right := second.function_type
    simpa only [typeEq,right] using left.symm
  obtain ⟨sizeEq,contentEq⟩ := first.header.unique second.header
  have finishEq : first.finish = second.finish := UScalar.eq_of_val_eq (by
    have left := first.extent
    have right := second.extent
    rw [sizeEq,contentEq] at left
    omega)
  obtain ⟨declaredLeft,decodedLeft,valuesLeft⟩ := module.decode_locals.complete data first.content profile first.groups
    first.bodyStart first.locals_bytes first.locals_allowed first.locals_bound
  obtain ⟨declaredRight,decodedRight,valuesRight⟩ := module.decode_locals.complete data second.content profile second.groups
    second.bodyStart second.locals_bytes second.locals_allowed second.locals_bound
  rw [contentEq,decodedRight] at decodedLeft
  have localsEq : declaredLeft = declaredRight ∧ first.bodyStart = second.bodyStart := by
    simpa only [Result.ok.injEq,core.result.Result.Ok.injEq,Prod.mk.injEq] using decodedLeft.symm
  have groupsEq : ModuleLocals.declared first.groups = ModuleLocals.declared second.groups := by
    rw [localsEq.1] at valuesLeft
    exact valuesLeft.symm.trans valuesRight
  have ctxLocals : first.ctx.locals = second.ctx.locals := alloc.vec.Vec.ext _ _ (by
    rw [first.context_locals,second.context_locals,functionEq,groupsEq])
  have ctxResults : first.ctx.results = second.ctx.results := alloc.vec.Vec.ext _ _ (by
    rw [first.context_results,second.context_results,functionEq])
  have ctxEq : first.ctx = second.ctx := by
    cases left : first.ctx
    cases right : second.ctx
    simp_all
  have bodyEq : first.body = second.body := Slice.ext _ _ (by
    have left := first.body_bytes.suffix
    rw [localsEq.2,finishEq] at left
    exact List.append_cancel_right (left.symm.trans second.body_bytes.suffix))
  exact ⟨typeEq,ctxEq,bodyEq,localsEq.2,finishEq⟩

end Itasca.Runtime.Code

end

/-! ## Entry Demand -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- One independently prepared source entry suffices to establish all entry
resource eligibility. Pure decoding fixes every operand of the numeric demand,
so no compiler run or universal family of callback proofs is supplied. -/
theorem EntryResourceDemand.of_prepared {A : Type} {budget : runtime.compiler.Budget A}
    {data env index start profile bound}
    (prepared : CodeEntry.Prepared data env index start profile)
    (demand : PreparedFunctionDemand budget prepared.ctx prepared.body.length
      (independentBodyDemand prepared.body env prepared.ctx prepared.typeIdx).operands bound) :
    EntryResourceDemand budget data env index start profile bound := by
  intro other
  obtain ⟨typeEq,ctxEq,bodyEq,_,_⟩ := prepared_entry_unique prepared other
  simpa only [← typeEq,← ctxEq,← bodyEq] using demand

end Itasca.Runtime.Code

end

/-! ## Prepared Batch Source -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independently prepared, encoded, and typed source entries in byte/index
order, with conservative source maxima. Preparation contains only source
metadata and decoding facts, never a compiler callback or target certificate. -/
inductive PreparedBatchSource (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (bodyBytes localCount peak : Nat) : Nat → Usize → List ModuleBinary.Code → Usize → Prop where
  | nil (index start) : PreparedBatchSource data env profile bodyBytes localCount peak index start [] start
  | cons {index start next finish entry entries}
      (ordinal : Usize) (ordinalValue : ordinal.val = index)
      (indexBound : ordinal.val < env.func_type_indices.val.length)
      (typed : Profile.EntryTyped profile env env.func_type_indices.val[ordinal.val] entry)
      (encoded : ModuleBinary.At (Profile.CodeEncodingWithinLimits profile) data start entry next)
      (prepared : CodeEntry.Prepared data env ordinal start profile) (ending : prepared.finish = next)
      (bytes : prepared.body.length ≤ bodyBytes) (locals : prepared.ctx.locals.val.length ≤ localCount)
      (operands : (independentBodyDemand prepared.body env prepared.ctx prepared.typeIdx).operands ≤ peak)
      (rest : PreparedBatchSource data env profile bodyBytes localCount peak (index+1) next entries finish) :
      PreparedBatchSource data env profile bodyBytes localCount peak index start (entry::entries) finish

end Itasca.Runtime.Code

end
