import Exec.Spec.TableCopyAlgebra
namespace Itasca.Runtime.Spec.Segment
open SpecExt

def tableCopy (s : store) (f : frame) (targetTable sourceTable destination source count : Nat) : store :=
  {s with TABLES := s.TABLES.set (f.MODULE.TABLES[targetTable]!) (withRefs (s.TABLES[f.MODULE.TABLES[targetTable]!]!) ((s.TABLES[f.MODULE.TABLES[targetTable]!]!).REFS.setSlice! destination ((s.TABLES[f.MODULE.TABLES[sourceTable]!]!).REFS.slice source (source+count))))}

theorem table_copy_steps (s : store) (f : frame) (destination source count targetTable sourceTable : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (ht : targetTable < 2^32) (hy : sourceTable < 2^32)
    (mapped : targetTable < f.MODULE.TABLES.length) (address : f.MODULE.TABLES[targetTable]! < s.TABLES.length)
    (sourceAddress : f.MODULE.TABLES[sourceTable]! < s.TABLES.length)
    (tableBounds : (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length < 2^32 ∧ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length < 2^32)
    (inside : source+count ≤ (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS.length ∧ destination+count ≤ (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS.length) :
    StepsH ⟨⟨s,f⟩,operands destination source count ++ [.TABLE_COPY (.mk_uN targetTable) (.mk_uN sourceTable)]⟩ []
      ⟨⟨tableCopy s f targetTable sourceTable destination source count,f⟩,[]⟩ := by
  by_cases direction : destination ≤ source
  · have run := table_copy_forward_steps s f destination source count targetTable sourceTable hs hf hd hi hn ht hy mapped address sourceAddress tableBounds inside (Or.inl direction)
    by_cases same : f.MODULE.TABLES[targetTable]! = f.MODULE.TABLES[sourceTable]!
    · rw [tableCopyForward_same_words _ _ _ _ _ _ _ address sourceAddress same] at run
      have sameSource : (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS = (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS := by simp only [fun_table,proj_uN_0,same]
      have snapshot := copyForwardPlain_snapshot (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS
        (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS destination source 0 count count
        (CopyPrefix.initial _ _ _) (by omega) direction (by simpa only [sameSource] using inside.1) inside.2
      simp only [Nat.add_zero,fun_table,proj_uN_0] at snapshot
      rw [snapshot] at run
      simpa only [tableCopy,same] using run
    · simp only [fun_table,proj_uN_0] at inside
      rw [tableCopyForward_distinct_words _ _ _ _ _ _ _ address sourceAddress same,
        copyInto_eq_setSlice _ _ _ _ _ inside.1 inside.2] at run
      exact run
  · have run := table_copy_backward_steps s f destination source count targetTable sourceTable hs hf hd hi hn ht hy mapped address sourceAddress tableBounds inside (Or.inl (by omega))
    by_cases same : f.MODULE.TABLES[targetTable]! = f.MODULE.TABLES[sourceTable]!
    · rw [tableCopyBackward_same_words _ _ _ _ _ _ _ address sourceAddress same] at run
      have sameSource : (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS = (fun_table ⟨s,f⟩ (.mk_uN sourceTable)).REFS := by simp only [fun_table,proj_uN_0,same]
      have snapshot := copyBackward_snapshot (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS
        (fun_table ⟨s,f⟩ (.mk_uN targetTable)).REFS destination source count count
        (CopySuffix.initial _ _ _ _) (by omega) (by omega) (by simpa only [sameSource] using inside.1) inside.2
      simp only [fun_table,proj_uN_0] at snapshot
      rw [snapshot] at run
      simpa only [tableCopy,same] using run
    · simp only [fun_table,proj_uN_0] at inside
      rw [tableCopyBackward_distinct_words _ _ _ _ _ _ _ address sourceAddress same,
        copyBackwardFrom_snapshot _ _ _ _ _ inside.1 inside.2] at run
      exact run
end Itasca.Runtime.Spec.Segment
