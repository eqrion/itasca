import Itasca.Runtime.Spec.TableCopyRun
import Itasca.Runtime.Spec.CopyPlain
namespace Itasca.Runtime.Spec.Segment
open SpecExt

def withRefs (table : tableinst) (refs : List ref) : tableinst := {table with REFS := refs}

theorem tableCopyForward_same_words (s : store) (f : frame) (targetTable sourceTable destination source count : Nat)
    (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (aliasEq : f.MODULE.TABLES[targetTable]! = f.MODULE.TABLES[sourceTable]!) :
    tableCopyForward s f targetTable sourceTable destination source count =
      {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (copyForwardPlain (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS destination source count))} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [tableCopyForward,copyForwardPlain]
    have identity : withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS = s.TABLES[f.MODULE.TABLES[targetTable]!]! := by cases s.TABLES[f.MODULE.TABLES[targetTable]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.TABLES (f.MODULE.TABLES[targetTable]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [tableCopyForward,ih (tableWrite s f targetTable destination (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]!) (destination+1) (source+1)
      (by simpa [tableWrite] using address) (by simpa [tableWrite] using sourceAddress)]
    simp only [tableWrite,fun_table,proj_uN_0,List.modify_eq_set,copyForwardPlain,withRefs]
    rw [aliasEq] at address ⊢
    generalize same : f.MODULE.TABLES[sourceTable]! = a at address sourceAddress ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.set_set,address]

theorem tableCopyForward_distinct_words (s : store) (f : frame) (targetTable sourceTable destination source count : Nat)
    (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (aliasEq : f.MODULE.TABLES[targetTable]! ≠ f.MODULE.TABLES[sourceTable]!) :
    tableCopyForward s f targetTable sourceTable destination source count =
      {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (copyInto (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS (s.TABLES[f.MODULE.TABLES[sourceTable]!]!).REFS destination source count))} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [tableCopyForward,copyInto]
    have identity : withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS = s.TABLES[f.MODULE.TABLES[targetTable]!]! := by cases s.TABLES[f.MODULE.TABLES[targetTable]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.TABLES (f.MODULE.TABLES[targetTable]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [tableCopyForward,ih (tableWrite s f targetTable destination (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[source]!) (destination+1) (source+1)
      (by simpa [tableWrite] using address) (by simpa [tableWrite] using sourceAddress)]
    simp only [tableWrite,fun_table,proj_uN_0,List.modify_eq_set,copyInto,withRefs]
    generalize targetEq : f.MODULE.TABLES[targetTable]! = a at address aliasEq ⊢
    generalize sourceEq : f.MODULE.TABLES[sourceTable]! = b at sourceAddress aliasEq ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.getElem?_eq_getElem sourceAddress,List.set_set,address,aliasEq]

theorem tableCopyBackward_same_words (s : store) (f : frame) (targetTable sourceTable destination source count : Nat)
    (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (aliasEq : f.MODULE.TABLES[targetTable]! = f.MODULE.TABLES[sourceTable]!) :
    tableCopyBackward s f targetTable sourceTable destination source count =
      {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (copyBackward (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS destination source count))} := by
  induction count generalizing s with
  | zero =>
    simp only [tableCopyBackward,copyBackward]
    have identity : withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS = s.TABLES[f.MODULE.TABLES[targetTable]!]! := by cases s.TABLES[f.MODULE.TABLES[targetTable]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.TABLES (f.MODULE.TABLES[targetTable]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [tableCopyBackward,ih (tableWrite s f targetTable (destination+count) (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[(source+count)]!)
      (by simpa [tableWrite] using address) (by simpa [tableWrite] using sourceAddress)]
    simp only [tableWrite,fun_table,proj_uN_0,List.modify_eq_set,copyBackward,withRefs]
    rw [aliasEq] at address ⊢
    generalize same : f.MODULE.TABLES[sourceTable]! = a at address sourceAddress ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.set_set,address]

theorem tableCopyBackward_distinct_words (s : store) (f : frame) (targetTable sourceTable destination source count : Nat)
    (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (aliasEq : f.MODULE.TABLES[targetTable]! ≠ f.MODULE.TABLES[sourceTable]!) :
    tableCopyBackward s f targetTable sourceTable destination source count =
      {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (copyBackwardFrom (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS (s.TABLES[f.MODULE.TABLES[sourceTable]!]!).REFS destination source count))} := by
  induction count generalizing s with
  | zero =>
    simp only [tableCopyBackward,copyBackwardFrom]
    have identity : withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) (s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS = s.TABLES[f.MODULE.TABLES[targetTable]!]! := by cases s.TABLES[f.MODULE.TABLES[targetTable]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.TABLES (f.MODULE.TABLES[targetTable]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [tableCopyBackward,ih (tableWrite s f targetTable (destination+count) (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS[(source+count)]!)
      (by simpa [tableWrite] using address) (by simpa [tableWrite] using sourceAddress)]
    simp only [tableWrite,fun_table,proj_uN_0,List.modify_eq_set,copyBackwardFrom,withRefs]
    generalize targetEq : f.MODULE.TABLES[targetTable]! = a at address aliasEq ⊢
    generalize sourceEq : f.MODULE.TABLES[sourceTable]! = b at sourceAddress aliasEq ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.getElem?_eq_getElem sourceAddress,List.set_set,address,aliasEq]

end Itasca.Runtime.Spec.Segment
