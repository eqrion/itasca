import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulMetadataPosts
import Itasca.Runtime.Compiler.Body.Reader.References.StatefulReferences
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement

/-!
Composition of base stateful reader cases.

Main declarations: `reader_stateful_base_wasm2`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundStatefulAcceptance`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2
set_option maxRecDepth 2048

theorem reader_stateful_base_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    ∃ op a b, StatefulArguments op a b ∧
      statefulCallback visitor before out.core op a b = .ok (.Ok (),after) ∧ StatefulReaderPost p out.core op := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | member | member | member | member | member | member
  · have equal : opcode = 37#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := profile_scalar_success visitor st out data env ctx index 37#u8 before after (by decide) accepted
    rw [code.step_wasm2.table_get] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.tableGet value.val),value,0#u32,?_,?_,reader_table_get_post_wasm2 p byte size value out.core read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translate.referenceType] using callback
  · have equal : opcode = 38#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := profile_scalar_success visitor st out data env ctx index 38#u8 before after (by decide) accepted
    rw [code.step_wasm2.table_set] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.tableSet value.val),value,0#u32,?_,?_,reader_table_set_post_wasm2 p byte size value out.core read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translate.referenceType] using callback
  · have equal : opcode = 63#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := profile_scalar_success visitor st out data env ctx index 63#u8 before after (by decide) accepted
    rw [code.step_wasm2.base _ _ _ _ _ _ _ (by decide),
      code.step_extended.base _ _ _ _ _ _ _ rfl (by simp [global_simps])] at run
    have dispatch := code.step_memory_size.dispatch visitor st.core data env ctx before
    simp only [global_simps] at dispatch
    rw [dispatch] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    cases value
    refine ⟨.memorySize,0#u32,0#u32,?_,?_,reader_memory_size_post_wasm2 p byte size out.core read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translate.referenceType] using callback
  · have equal : opcode = 64#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := profile_scalar_success visitor st out data env ctx index 64#u8 before after (by decide) accepted
    rw [code.step_wasm2.base _ _ _ _ _ _ _ (by decide),
      code.step_extended.base _ _ _ _ _ _ _ rfl (by simp [global_simps])] at run
    have dispatch := code.step_memory_grow.dispatch visitor st.core data env ctx before
    simp only [global_simps] at dispatch
    rw [dispatch] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    cases value
    refine ⟨.memoryGrow,0#u32,0#u32,?_,?_,reader_memory_grow_post_wasm2 p byte size out.core read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translate.referenceType] using callback
  · have equal : opcode = 208#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := profile_scalar_success visitor st out data env ctx index 208#u8 before after (by decide) accepted
    rw [code.step_wasm2.ref_null] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.refNull (Translate.referenceType value)),(match value with | .FuncRef => 0#u32 | .ExternRef => 1#u32),0#u32,?_,?_,reader_ref_null_post_wasm2 p byte size value out.core read⟩
    · cases value <;> exact ⟨rfl,rfl⟩
    · cases value <;> simpa only [statefulCallback,Translate.referenceType] using callback
  · have equal : opcode = 209#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := profile_scalar_success visitor st out data env ctx index 209#u8 before after (by decide) accepted
    rw [code.step_wasm2.ref_is_null] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    cases value
    refine ⟨.refIsNull,0#u32,0#u32,?_,?_,reader_ref_is_null_post_wasm2 p out.core byte size read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translate.referenceType] using callback
  · have equal : opcode = 210#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    obtain ⟨size,run⟩ := profile_scalar_success visitor st out data env ctx index 210#u8 before after (by decide) accepted
    rw [code.step_wasm2.ref_func] at run
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ run
    refine ⟨(.refFunc value.val),value,0#u32,?_,?_,reader_ref_func_post_wasm2 p value out.core byte size read⟩
    · exact ⟨rfl,rfl⟩
    · simpa only [statefulCallback,Translate.referenceType] using callback

end Itasca.Runtime.Code
