import Exec.Code.Module.SourceCompilationDemand

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Source-derived upper bounds on every kind of compiler reserve request.
These are element counts for individual allocations, not aggregate heap bytes. -/
def sourceAllocationRequests (env : module.Env) (tail : module.Tail)
    (bodyBytes localCount peak : Nat) : List Nat :=
  [4,env.types.length,env.func_types.length,env.func_type_indices.length,
    3*bodyBytes+3,localCount,peak,env.func_type_indices.length+initializerMappingCost ⟨env,tail⟩+1,
    2,5*(env.elements.length+tail.data.length)+1]

/-- A concrete conservative allocation demand from source metadata and
independent body/local/operand maxima. -/
def sourceAllocationDemand (env : module.Env) (tail : module.Tail)
    (bodyBytes localCount peak : Nat) : Nat :=
  (sourceAllocationRequests env tail bodyBytes localCount peak).foldr Nat.max 0

private theorem member_le_max (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr Nat.max 0 := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact (ih member).trans (Nat.le_max_right _ _)

/-- The explicit source maximum bounds each component reserve request. -/
theorem source_allocation_request_fits {env tail bodyBytes localCount peak request}
    (member : request ∈ sourceAllocationRequests env tail bodyBytes localCount peak) :
    request ≤ sourceAllocationDemand env tail bodyBytes localCount peak :=
  member_le_max _ _ member

/-- Numerical eligibility may always use the computed source allocation bound;
no successful allocator call or compiler result is needed to choose that bound. -/
theorem SourceCompilationDemand.computed_allocation {A env tail profile limits bodyBytes localCount peak bound}
    (demand : SourceCompilationDemand A env tail profile limits bodyBytes localCount peak bound) :
    SourceCompilationDemand A env tail profile limits bodyBytes localCount peak
      (sourceAllocationDemand env tail bodyBytes localCount peak) := by
  have request (value : Nat) (member : value ∈ sourceAllocationRequests env tail bodyBytes localCount peak) :=
    source_allocation_request_fits member
  have environment := demand.environment
  have functions := demand.functions
  constructor
  · refine ⟨environment.functionLimit,environment.typeLimit,environment.signatureWidths,environment.functionWidths,
      environment.signatureCapacity,?_,environment.slotCapacity,?_,environment.functionCapacity,?_⟩
    all_goals
      simp only [initialScheduler,alloc.vec.Vec.new,alloc.vec.Vec.length,List.length_nil,Nat.zero_add]
      apply request
      simp [sourceAllocationRequests]
  · refine ⟨functions.size,functions.counters,?_,?_,?_,functions.slots⟩
    all_goals
      apply request
      simp [sourceAllocationRequests]
  · exact demand.maxima
  · exact demand.instructions
  · exact demand.mappingCapacity
  · apply request
    simp [sourceAllocationRequests,alloc.vec.Vec.length]
  · apply request
    simp [sourceAllocationRequests]
  · exact demand.segmentCapacity
  · apply request
    simp [sourceAllocationRequests]
  · exact demand.elementCount
  · exact demand.dataCount
  · exact demand.elementLengths
  · exact demand.dataLengths
  · apply request
    simp [sourceAllocationRequests]

end Exec.Code
