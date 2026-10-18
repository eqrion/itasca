import Exec.Spec.MemoryCopyRun
import Exec.Spec.CopySnapshot
namespace Exec.Spec.Segment
open SpecExt

def withBytes (memory : meminst) (bytes : List byte) : meminst := {memory with BYTES := bytes}

theorem memoryCopyForward_words (s : store) (f : frame) (destination source count : Nat)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length) :
    memoryCopyForward s f destination source count =
      {s with MEMS := s.MEMS.set (f.MODULE.MEMS[0]!) (withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) (copyForward (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source count))} := by
  induction count generalizing s destination source with
  | zero =>
    simp only [memoryCopyForward,copyForward]
    have identity : withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES = s.MEMS[f.MODULE.MEMS[0]!]! := by cases s.MEMS[f.MODULE.MEMS[0]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.MEMS (f.MODULE.MEMS[0]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [memoryCopyForward,ih (memoryWrite s f destination (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source]!)
      (next32 destination) (next32 source) (by simpa [memoryWrite] using address)]
    simp only [memoryWrite,fun_mem,proj_uN_0,List.modify_eq_set,copyForward,withBytes]
    generalize same : f.MODULE.MEMS[0]! = a at address ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.set_set,address]

theorem memoryCopyBackward_words (s : store) (f : frame) (destination source count : Nat)
    (address : f.MODULE.MEMS[0]! < s.MEMS.length) :
    memoryCopyBackward s f destination source count =
      {s with MEMS := s.MEMS.set (f.MODULE.MEMS[0]!) (withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) (copyBackward (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source count))} := by
  induction count generalizing s with
  | zero =>
    simp only [memoryCopyBackward,copyBackward]
    have identity : withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES = s.MEMS[f.MODULE.MEMS[0]!]! := by cases s.MEMS[f.MODULE.MEMS[0]!]!; rfl
    rw [identity]
    simp only [getElem!_pos s.MEMS (f.MODULE.MEMS[0]!) address,List.set_getElem_self]
  | succ count ih =>
    rw [memoryCopyBackward,ih (memoryWrite s f (destination+count) (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES[source+count]!)
      (by simpa [memoryWrite] using address)]
    simp only [memoryWrite,fun_mem,proj_uN_0,List.modify_eq_set,copyBackward,withBytes]
    generalize same : f.MODULE.MEMS[0]! = a at address ⊢
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem address,List.set_set,address]
end Exec.Spec.Segment
