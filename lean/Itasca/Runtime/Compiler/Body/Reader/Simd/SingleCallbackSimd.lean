import Itasca.Runtime.Compiler.Body.Reader.Replay.SingleCallbackExtended
import Itasca.Wasm2.Trace.Refinement

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace Itasca.Wasm2.Simd
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private theorem pure_meaning_bound {opcode : Nat} {op : Operation}
    (found : pureMeaning opcode = some op) : opcode < 256 := by
  by_cases beyond : opcode ≥ 256
  · unfold pureMeaning at found
    rw [if_pos beyond] at found
    cases found
  · exact Nat.lt_of_not_ge beyond

private theorem lane_meaning_bound {opcode : Nat} {op : LaneOperation}
    (found : laneMeaning opcode = some op) : opcode < 256 := by
  unfold laneMeaning at found
  split at found <;> simp_all <;> omega

private theorem memory_meaning_bound {opcode : Nat} {op : MemoryOperation}
    (found : memoryMeaning opcode = some op) : opcode < 256 := by
  unfold memoryMeaning at found
  split at found <;> simp_all <;> omega

/-- The independent SIMD tables bound every selected subopcode and every
accepted substep calls exactly one of the six SIMD visitor event forms. -/
theorem reader_single_callback_simd_sub {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (opcode : U32)
    (before after : V) (out : code.OpIterState)
    (accepted : subStep visitor st data env opcode before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  unfold subStep at accepted
  rw [pure_table] at accepted
  cases hp : pureMeaning opcode.val with
  | some op =>
    simp only [hp,Option.map_some,bind_ok] at accepted
    exact reader_single_callback_of_run visitor _ (fun _ _ => .simd opcode) before after out
      (by intro arg; exact ⟨True.intro,pure_meaning_bound hp⟩) accepted
  | none =>
    simp only [hp,Option.map_none,bind_ok] at accepted
    rw [lane_table] at accepted
    cases hl : laneMeaning opcode.val with
    | some lane =>
      simp only [hl,Option.map_some,bind_ok] at accepted
      rcases runtime : lane.runtime with ⟨ty,count,replace⟩
      simp only [runtime] at accepted
      exact reader_single_callback_of_run visitor _ (fun _ arg => .simd_lane opcode arg) before after out
        (by intro arg; exact ⟨True.intro,lane_meaning_bound hl⟩) accepted
    | none =>
      simp only [hl,Option.map_none,bind_ok] at accepted
      rw [memory_table] at accepted
      cases hm : memoryMeaning opcode.val with
      | some mem =>
        simp only [hm,Option.map_some,bind_ok] at accepted
        rcases runtime : mem.runtime with ⟨alignment,store,count⟩
        simp only [runtime] at accepted
        split at accepted
        · exact reader_single_callback_of_run visitor _
            (fun _ (arg : code.MemArg × U8) => .simd_memory_lane opcode arg.1 arg.2) before after out
            (by intro arg; exact ⟨True.intro,memory_meaning_bound hm⟩) accepted
        · cases store <;> simp only [Bool.false_eq_true,if_true,if_false] at accepted
          all_goals
            exact reader_single_callback_of_run visitor _ (fun _ arg => .simd_memory opcode arg) before after out
              (by intro arg; exact ⟨True.intro,memory_meaning_bound hm⟩) accepted
      | none =>
        simp only [hm,Option.map_none,bind_ok] at accepted
        split at accepted
        · exact reader_single_callback_of_run visitor _ (fun _ (arg : U64 × U64) => .simd_const arg.1 arg.2) before after out
            (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
        · exact reader_single_callback_of_run visitor _ (fun _ (arg : U64 × U64) => .simd_shuffle arg.1 arg.2) before after out
            (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
        · simp at accepted

/-- SIMD prefix decoding retains the exact event and its independently bounded
subopcode; it does not introduce an additional callback. -/
theorem reader_single_callback_simd {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (before after : V) (out : code.OpIterState)
    (accepted : code.step_simd visitor st data env before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  rw [code.step_simd.eq_runs] at accepted
  unfold prefixStep at accepted
  obtain ⟨read,called⟩ := reader.read_u32_leb.total data st.pos
  simp only [called,bind_ok] at accepted
  cases read with
  | Err error => simp at accepted
  | Ok pair =>
    obtain ⟨opcode,next⟩ := pair
    exact reader_single_callback_simd_sub visitor _ data env opcode before after out accepted

end Itasca.Runtime.Compiler
