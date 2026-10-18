import Exec.Code.Body.Relations.Memory.StatefulMemoryPostsWasm1
import Exec.Code.Local.Relations.Calls.StatefulCallbacks
import Exec.Code.Local.Relations.Common.StatefulLowering
import Exec.Code.Body.Reader.Common.ReaderProfile
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1

theorem reader_stateful_memory_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState) (opcode : U8)
    (member : opcode.val ∈ [63,64])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step visitor st data env ctx opcode before = .ok (.Ok (),out,after)) :
    ∃ op, statefulUsesPair op = false ∧ StatefulArguments op 0#u32 0#u32 ∧
      statefulCallback visitor before out op 0#u32 0#u32 = .ok (.Ok (),after) ∧
      StatefulReaderPostWasm1 p out op := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | member
  · have equal : opcode = 63#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    have dispatch := code.step_memory_size.dispatch visitor st data env ctx before
    simp only [global_simps] at dispatch
    rw [dispatch] at accepted
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
    cases value
    refine ⟨.memorySize,rfl,⟨rfl,rfl⟩,?_,reader_memory_size_post_wasm1 p byte (by have := p.val_capacity; omega) out read⟩
    simpa only [statefulCallback] using callback
  · have equal : opcode = 64#u8 := (UScalar.eq_equiv _ _).mpr member
    rw [equal] at byte accepted
    have dispatch := code.step_memory_grow.dispatch visitor st data env ctx before
    simp only [global_simps] at dispatch
    rw [dispatch] at accepted
    obtain ⟨value,read,callback⟩ := reader_run_success _ _ _ _ _ accepted
    cases value
    refine ⟨.memoryGrow,rfl,⟨rfl,rfl⟩,?_,reader_memory_grow_post_wasm1 p byte (by have := p.val_capacity; omega) out read⟩
    simpa only [statefulCallback] using callback

end Exec.Code
