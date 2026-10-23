import Exec.Spec.Wf

/-! Bounds shared by scalar, packed, vector, and lane stores. The source
update judgment carries the guard; a clamping list splice cannot establish it. -/
namespace Exec.Spec

/-- Every source memory write stays inside the original memory's byte range. -/
theorem memory_write_bounds {z z' : state} {index : memidx} {address width : Nat}
    {bytes : List byte} (write : fun_with_mem z index address width bytes z') :
    address + width ≤ (fun_mem z index).BYTES.length := by
  cases write
  assumption

end Exec.Spec
