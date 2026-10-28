import Itasca.Runtime.Spec.TableInitSource
import Itasca.Runtime.Spec.SegmentCopy

namespace Itasca.Runtime.Spec.Segment
open SpecExt

theorem tableInit_eq (s : store) (f : frame) (tableIndex elementIndex destination source count : Nat) :
    tableInit s f tableIndex elementIndex destination source count =
      {s with TABLES := s.TABLES.modify f.MODULE.TABLES[tableIndex]! (fun table => {table with REFS := copyInto table.REFS (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS destination source count})} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [tableInit,copyInto]
    have identity : (fun table : tableinst => {table with REFS := table.REFS}) = id := by funext table; cases table; rfl
    rw [identity,List.modify_id]
  | succ count ih =>
    rw [tableInit,ih]
    simp only [tableWrite,fun_elem,proj_uN_0,List.modify_modify_eq,Function.comp_def,copyInto]
    congr 1
    congr 1
    funext table
    simp only [List.modify_eq_set]

end Itasca.Runtime.Spec.Segment
