import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulMetadataPosts
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Wasm2.Bulk.Dispatch

/-!
Composition of bulk stateful reader cases.

Main declarations: `reader_stateful_bulk_wasm2`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundStatefulAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2
set_option maxRecDepth 2048

theorem reader_stateful_bulk_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    ∃ op a b, StatefulArguments op a b ∧
      statefulCallback visitor before out.core op a b = .ok (.Ok (),after) ∧ StatefulReaderPost p out.core op := by
  obtain ⟨size,run⟩ := profile_scalar_success visitor st out data env ctx index 252#u8 before after (by decide) accepted
  have extended : 8 ≤ subopcode.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  rw [code.step_wasm2.bulk _ _ _ _ _ subopcode next _ decoded extended,code.step_bulk.eq_runs] at run
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | member | member | member | member | member | member | member | member | member
  · have equal : subopcode = 8#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.memoryInit value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_memory_init_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 9#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.dataDrop value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_data_drop_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 10#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨.memoryCopy,0#u32,0#u32,⟨rfl,rfl⟩,?_,reader_memory_copy_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 11#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨.memoryFill,0#u32,0#u32,⟨rfl,rfl⟩,?_,reader_memory_fill_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 12#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.tableInit value.2.val value.1.val),value.1,value.2,⟨rfl,rfl⟩,?_,reader_table_init_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 13#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.elemDrop value.1.val),value.1,0#u32,⟨rfl,rfl⟩,?_,reader_elem_drop_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 14#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.tableCopy value.1.val value.2.val),value.1,value.2,⟨rfl,rfl⟩,?_,reader_table_copy_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 15#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.tableGrow value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_table_grow_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 16#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.tableSize value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_table_size_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback
  · have equal : subopcode = 17#u32 := (UScalar.eq_equiv _ _).mpr member
    subst subopcode
    simp only [bulkStep] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.tableFill value.val),value,0#u32,⟨rfl,rfl⟩,?_,reader_table_fill_post_wasm2 p byte next decoded size value out.core read⟩
    simpa only [statefulCallback] using callback

end Itasca.Runtime.Code
