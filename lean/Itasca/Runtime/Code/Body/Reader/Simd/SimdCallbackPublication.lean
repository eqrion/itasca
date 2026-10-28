import Itasca.Runtime.Code.Local.Coordinates.SimdSourceCoordinates
import Itasca.Runtime.Code.Local.Publication.LiteralMapPublication
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdBitsCallbacks
import Itasca.Visitor.Events

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- SIMD visitor arguments use the Wasm 2 subopcode interval. Constant and
shuffle events carry their complete immediate bits directly. -/
inductive SimdPublicationAction : Action → Prop where
  | plain (sub : U32) (bound : sub.val < 256) : SimdPublicationAction (.simd sub)
  | lane (sub : U32) (lane : U8) (bound : sub.val < 256) : SimdPublicationAction (.simd_lane sub lane)
  | memory (sub : U32) (arg : code.MemArg) (bound : sub.val < 256) : SimdPublicationAction (.simd_memory sub arg)
  | memoryLane (sub : U32) (arg : code.MemArg) (lane : U8) (bound : sub.val < 256) :
      SimdPublicationAction (.simd_memory_lane sub arg lane)
  | constant (lo hi : U64) : SimdPublicationAction (.simd_const lo hi)
  | shuffle (lo hi : U64) : SimdPublicationAction (.simd_shuffle lo hi)

/-- All six SIMD event forms dispatch to a bounded ordinary compiler opcode. -/
theorem simd_hook_publication_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    {action : Action} (supported : SimdPublicationAction action) :
    ∃ (opcode : U16) (a b : U32) (bits : U128), 512 ≤ opcode.val ∧ opcode.val < 768 ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state action) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits := by
  cases supported with
  | plain sub bound =>
    let opcode : U16 := ⟨⟨512+sub.val,by change 512+sub.val < 65536; omega⟩⟩
    exact ⟨opcode,0#u32,0#u32,0#u128,by change 512 ≤ 512+sub.val; omega,by change 512+sub.val < 768; omega,
      compiler_simd_callback ops compiler state sub opcode bound rfl⟩
  | lane sub lane bound =>
    let opcode : U16 := ⟨⟨512+sub.val,by change 512+sub.val < 65536; omega⟩⟩
    exact ⟨opcode,UScalar.cast .U32 lane,0#u32,0#u128,by change 512 ≤ 512+sub.val; omega,by change 512+sub.val < 768; omega,
      compiler_simd_lane_callback ops compiler state sub opcode bound rfl lane⟩
  | memory sub arg bound =>
    let opcode : U16 := ⟨⟨512+sub.val,by change 512+sub.val < 65536; omega⟩⟩
    exact ⟨opcode,arg.offset,arg.align,0#u128,by change 512 ≤ 512+sub.val; omega,by change 512+sub.val < 768; omega,
      compiler_simd_memory_callback ops compiler state sub opcode bound rfl arg⟩
  | memoryLane sub arg lane bound =>
    let opcode : U16 := ⟨⟨512+sub.val,by change 512+sub.val < 65536; omega⟩⟩
    exact ⟨opcode,arg.offset,arg.align,UScalar.cast .U128 lane,by change 512 ≤ 512+sub.val; omega,by change 512+sub.val < 768; omega,
      compiler_simd_memory_lane_callback ops compiler state sub opcode bound rfl arg lane⟩
  | constant lo hi =>
    exact ⟨524#u16,0#u32,0#u32,initializerBits lo hi,by decide,by decide,
      compiler_simd_constant_callback ops compiler state lo hi⟩
  | shuffle lo hi =>
    exact ⟨525#u16,0#u32,0#u32,initializerBits lo hi,by decide,by decide,
      compiler_simd_shuffle_callback ops compiler state lo hi⟩

/-- Actual SIMD visitor events preserve both publication invariants, including
unreachable code, memory lanes, constants, and shuffles. -/
theorem compiler_simd_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) {action : Action} (supported : SimdPublicationAction action)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state action) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨opcode,a,b,bits,lower,upper,dispatch⟩ := simd_hook_publication_dispatch ops before state supported
  rw [dispatch] at called
  exact ⟨compiler_simd_op_source_coordinates ops law before after state opcode a b bits lower upper
      coordinates inside forward called,
    compiler_lower_simd_map_publication ops law before after state opcode a b bits lower upper called maps forward⟩

end Itasca.Runtime.Code
