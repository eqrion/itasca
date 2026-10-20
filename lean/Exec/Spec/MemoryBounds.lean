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

/-- A permitted write excludes the corresponding out-of-bounds trap guard.
This covers arbitrary widths and unbounded effective addresses. -/
theorem memory_write_excludes_oob {z z' : state} {index : memidx} {address width : Nat}
    {bytes : List byte} (write : fun_with_mem z index address width bytes z') :
    ¬ address + width > (fun_mem z index).BYTES.length :=
  Nat.not_lt.mpr (memory_write_bounds write)

/-- Byte-range success and trap guards cover every effective address and
length, including empty memories and effective addresses past 4 GiB. -/
theorem memory_bounds_partition (address offset width length : Nat) :
    (address + offset + width ≤ length ∨ length < address + offset + width) ∧
    ¬ (address + offset + width ≤ length ∧ length < address + offset + width) := by
  omega

end Exec.Spec
