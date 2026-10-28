import Exec.Spec.MemoryCopyAlgebra
namespace Itasca.Runtime.Spec.Segment
open SpecExt

def memoryCopy (s : store) (f : frame) (destination source count : Nat) : store :=
  {s with MEMS := s.MEMS.set (f.MODULE.MEMS[0]!) (withBytes (s.MEMS[f.MODULE.MEMS[0]!]!) ((s.MEMS[f.MODULE.MEMS[0]!]!).BYTES.setSlice! destination ((s.MEMS[f.MODULE.MEMS[0]!]!).BYTES.slice source (source+count))))}

theorem memory_copy_steps (s : store) (f : frame) (destination source count : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length) (address : f.MODULE.MEMS[0]! < s.MEMS.length)
    (memoryBound : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ≤ 2^32)
    (inside : source+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length ∧ destination+count ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [.MEMORY_COPY]⟩ []
      ⟨⟨memoryCopy s f destination source count,f⟩,[]⟩ := by
  by_cases direction : destination ≤ source
  · have run := memory_copy_forward_steps s f destination source count hs hf hd hi hn mapped address memoryBound inside (Or.inl direction)
    have snapshot := copyForward_snapshot (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES
      (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source 0 count count
      (CopyPrefix.initial _ _ _) (by omega) direction inside.1 inside.2 memoryBound
    simp only [Nat.add_zero] at snapshot
    rw [memoryCopyForward_words _ _ _ _ _ address,snapshot] at run
    exact run
  · have run := memory_copy_backward_steps s f destination source count hs hf hd hi hn mapped address memoryBound inside (Or.inl (by omega))
    have snapshot := copyBackward_snapshot (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES
      (s.MEMS[f.MODULE.MEMS[0]!]!).BYTES destination source count count
      (CopySuffix.initial _ _ _ _) (by omega) (by omega) inside.1 inside.2
    rw [memoryCopyBackward_words _ _ _ _ _ address,snapshot] at run
    exact run
end Itasca.Runtime.Spec.Segment
