import Exec.Spec.TableFillSource
namespace Exec.Spec.Segment
open SpecExt

def fillInto {T : Type} (before : List T) (destination : Nat) (value : T) : Nat → List T
  | 0 => before
  | count+1 => fillInto (before.set destination value) (destination+1) value count

theorem fillInto_map {T U : Type} (decode : T → U) (before : List T) (destination count : Nat) (value : T) :
    (fillInto before destination value count).map decode =
      fillInto (before.map decode) destination (decode value) count := by
  induction count generalizing before destination with
  | zero => rfl
  | succ count ih => simp only [fillInto,ih,List.map_set]

theorem tableFill_eq (s : store) (f : frame) (tableIndex destination count : Nat) (value : ref) :
    tableFill s f tableIndex destination value count =
      {s with TABLES := s.TABLES.modify f.MODULE.TABLES[tableIndex]! (fun table =>
        {table with REFS := fillInto table.REFS destination value count})} := by
  induction count generalizing s destination with
  | zero =>
    simp only [tableFill,fillInto]
    have identity : (fun table : tableinst => {table with REFS := table.REFS}) = id := by funext table; cases table; rfl
    rw [identity,List.modify_id]
  | succ count ih =>
    rw [tableFill,ih]
    simp only [tableWrite,List.modify_modify_eq,Function.comp_def,fillInto]
    congr 1
    congr 1
    funext table
    simp only [List.modify_eq_set]
end Exec.Spec.Segment
