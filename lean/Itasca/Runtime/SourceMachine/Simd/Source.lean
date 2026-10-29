import Itasca.Runtime.SourceMachine.Simd.Signature

namespace Itasca.Runtime.SourceMachine.Simd
open SpecExt

/-- The source stack signatures of SIMD memory operations. Width, alignment and
lane validity remain obligations of the generated instruction typing rules. -/
inductive MemorySignature : instr → List valtype → List valtype → Prop where
  | load operation argument : MemorySignature (.VLOAD .V128 operation argument) [.I32] [.V128]
  | loadLane width argument lane : MemorySignature (.VLOAD_LANE .V128 width argument lane) [.I32,.V128] [.V128]
  | store argument : MemorySignature (.VSTORE .V128 argument) [.I32,.V128] []
  | storeLane width argument lane : MemorySignature (.VSTORE_LANE .V128 width argument lane) [.I32,.V128] []

theorem MemorySignature.principal {source inputs outputs C signature}
    (shape : MemorySignature source inputs outputs) (typed : Instr_ok C source signature) :
    signature = .mk_functype (.mk_list inputs) (.mk_list outputs) := by
  cases shape <;> cases typed <;> rfl

end Itasca.Runtime.SourceMachine.Simd

namespace Itasca.Runtime.SourceMachine

/-- SIMD source syntax, independent of opcode decoding and extracted execution.
The generated typing separately constrains shapes, immediates and memory use. -/
inductive SimdInstr : instr → Prop where
  | pure {source inputs output} (signature : Simd.PureSignature source inputs output) : SimdInstr source
  | constant value : SimdInstr (.VCONST .V128 value)
  | memory {source inputs outputs} (signature : Simd.MemorySignature source inputs outputs) : SimdInstr source

end Itasca.Runtime.SourceMachine
