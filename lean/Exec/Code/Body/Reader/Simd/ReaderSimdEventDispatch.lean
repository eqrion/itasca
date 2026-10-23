import Exec.Code.Body.Reader.Simd.ReaderSimdEvents
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Every accepted SIMD-prefixed reader is one of the independently classified
families and retains a complete canonical reader/callback witness. -/
theorem reader_simd_event_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0xfd#u8 before = .ok (.Ok (),out,after)) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,sub,next,decoded,called⟩ := simd_prefix_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index before after accepted
  cases pure : Wasm2.Simd.pureMeaning sub.val with
  | some op => exact simd_reader_event_pure p ops before after out ctx C sub next decoded byte accepted op pure
  | none =>
    cases lane : Wasm2.Simd.laneMeaning sub.val with
    | some op => exact simd_reader_event_lane p ops before after out ctx C sub next decoded byte accepted op lane
    | none =>
      cases memory : Wasm2.Simd.memoryMeaning sub.val with
      | some op =>
        by_cases full : op.laneCount = 0
        · exact simd_reader_event_memory p ops before after out ctx C sub next decoded byte accepted op memory full contextMemories
        · exact simd_reader_event_memory_lane p ops before after out ctx C sub next decoded byte accepted op memory full contextMemories
      | none =>
        simp only [Wasm2.Simd.subStep,Wasm2.Simd.pure_table,pure,Wasm2.Simd.lane_table,lane,
          Wasm2.Simd.memory_table,memory,Option.map_none,bind_ok] at called
        split at called
        · exact simd_reader_event_constant p ops before after out ctx C 12#u32 next decoded byte accepted rfl
        · exact simd_reader_event_shuffle p ops before after out ctx C 13#u32 next decoded byte accepted rfl
        · simp at called
end Exec.Code
