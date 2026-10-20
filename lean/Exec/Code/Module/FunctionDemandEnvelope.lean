import Exec.Code.Module.PreparedFunctionDemand
import Exec.Code.Module.PreparedFunctionAvailable

namespace Exec.Code
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

end Exec.Code
