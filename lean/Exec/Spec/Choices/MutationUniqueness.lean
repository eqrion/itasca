import Exec.Spec.MemoryBounds
/-! Exact source mutation relations are functional in their poststate. -/
namespace Exec.Spec
open SpecExt

theorem source_with_local_unique {before left right : state} (index : localidx) (value : val)
    (first : fun_with_local before index value left)
    (second : fun_with_local before index value right) : left=right := by
  cases first
  cases second
  with_reducible rfl

theorem source_with_global_unique {before left right : state} (index : globalidx) (value : val)
    (first : fun_with_global before index value left)
    (second : fun_with_global before index value right) : left=right := by
  cases first
  cases second
  with_reducible rfl

theorem source_with_table_unique {before left right : state} (index : tableidx) (position : Nat) (value : ref)
    (first : fun_with_table before index position value left)
    (second : fun_with_table before index position value right) : left=right := by
  cases first
  cases second
  with_reducible rfl

theorem source_with_mem_unique {before left right : state} (index : memidx) (position count : Nat) (bytes : List byte)
    (first : fun_with_mem before index position count bytes left)
    (second : fun_with_mem before index position count bytes right) : left=right := by
  cases first
  cases second
  with_reducible rfl

theorem source_with_elem_unique {before left right : state} (index : elemidx) (values : List ref)
    (first : fun_with_elem before index values left)
    (second : fun_with_elem before index values right) : left=right := by
  cases first
  cases second
  with_reducible rfl

theorem source_with_data_unique {before left right : state} (index : dataidx) (bytes : List byte)
    (first : fun_with_data before index bytes left)
    (second : fun_with_data before index bytes right) : left=right := by
  cases first
  cases second
  with_reducible rfl
end Exec.Spec
