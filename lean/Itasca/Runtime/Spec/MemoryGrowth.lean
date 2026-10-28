import Itasca.Runtime.Spec.TableGrowth
import Itasca.Runtime.Spec.IntegerDiv
namespace Itasca.Runtime.Spec
open SpecExt

theorem memory_grow_fail_step (s : store) (f : frame) (delta : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : delta < 2^32) :
    StepH ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
      ⟨⟨s,f⟩,[Segment.i32 (2^32-1)]⟩ := by
  apply StepH.step
  apply Step.memory_grow_fail
  · simpa using (fun_inv_signed_.fun_inv_signed__case_1 32 (-1) (by decide))
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hd,.admininstr_case_63⟩
  · apply wf_config_make hs hf
    simpa [Forall,Segment.i32] using Segment.i32_wf 4294967295 (by decide)

theorem memory_pages_nat (length : Nat) :
    rat_to_nat ((length : Rat) / (64 * Ki : Rat)) = length / 65536 := by
  simp only [Ki]
  norm_num
  exact truncz_nat_div length 65536

theorem memory_grow_success_step (s : store) (f : frame) (delta : Nat) (next : meminst)
    (hs : wf_store s) (hf : wf_frame f) (hd : delta < 2^32)
    (mapped : 0 < f.MODULE.MEMS.length)
    (bounded : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536 < 2^32)
    (grown : fun_growmemory (fun_mem ⟨s,f⟩ (.mk_uN 0)) delta (some next))
    (fresh : wf_store {s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun _ => next)}) :
    StepH ⟨⟨s,f⟩,[Segment.i32 delta,.MEMORY_GROW]⟩ []
      ⟨⟨{s with MEMS := s.MEMS.modify f.MODULE.MEMS[0]! (fun _ => next)},f⟩,
        [Segment.i32 ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length / 65536)]⟩ := by
  have pages := memory_pages_nat (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length
  rw [← pages]
  apply StepH.step
  apply Step.memory_grow_succeed _ _ next (some next)
  · exact grown
  · exact fun_with_meminst.fun_with_meminst_case_0 s f (.mk_uN 0) next mapped (.state_case_0 _ _ fresh hf)
  · simp
  · rfl
  · apply wf_config_make hs hf
    simp only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp]
    exact ⟨Segment.i32_wf _ hd,.admininstr_case_63⟩
  · apply wf_config_make fresh hf
    simpa only [Forall,List.mem_cons,List.not_mem_nil,false_implies,forall_const,and_true,forall_eq_or_imp,pages,Segment.i32]
      using Segment.i32_wf _ bounded
  · exact Segment.index_wf 0 (by decide)
end Itasca.Runtime.Spec
