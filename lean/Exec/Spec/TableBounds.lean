import Exec.Spec.Wf

/-! Table writes require an element inside the original table. The source
update judgment carries this guard even though the generated list update is total. -/
namespace Exec.Spec

/-- A permitted source table write cannot silently update past the end. -/
theorem table_write_bounds {z z' : state} {index : tableidx} {position : Nat}
    {value : ref} (write : fun_with_table z index position value z') :
    position < (fun_table z index).REFS.length := by
  cases write
  assumption

/-- Success excludes the table access trap guard for every element index. -/
theorem table_write_excludes_oob {z z' : state} {index : tableidx} {position : Nat}
    {value : ref} (write : fun_with_table z index position value z') :
    ¬ (fun_table z index).REFS.length ≤ position :=
  Nat.not_le.mpr (table_write_bounds write)

/-- Table access guards cover empty tables and arbitrary natural indices. -/
theorem table_bounds_partition (position length : Nat) :
    (position < length ∨ length ≤ position) ∧
    ¬ (position < length ∧ length ≤ position) := by
  omega

end Exec.Spec
