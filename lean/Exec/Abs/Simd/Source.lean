import Exec.Abs.Simd.Signature

namespace Exec.Abs.Simd
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

theorem MemorySignature.arity {source inputs outputs}
    (shape : MemorySignature source inputs outputs) : inputs.length ≤ 2 := by
  cases shape <;> simp

end Exec.Abs.Simd

namespace Exec.Abs

/-- SIMD source syntax, independent of opcode decoding and extracted execution.
The generated typing separately constrains shapes, immediates and memory use. -/
inductive SimdInstr : instr → Prop where
  | pure {source inputs output} (signature : Simd.PureSignature source inputs output) : SimdInstr source
  | constant value : SimdInstr (.VCONST .V128 value)
  | memory {source inputs outputs} (signature : Simd.MemorySignature source inputs outputs) : SimdInstr source

theorem SimdInstr.not_block {type body} : ¬ SimdInstr (.BLOCK type body) := by
  intro allowed
  cases allowed with
  | pure signature => cases signature
  | memory signature => cases signature

theorem SimdInstr.not_loop {type body} : ¬ SimdInstr (.LOOP type body) := by
  intro allowed
  cases allowed with
  | pure signature => cases signature
  | memory signature => cases signature

theorem SimdInstr.not_if {type yes no} : ¬ SimdInstr (.IFELSE type yes no) := by
  intro allowed
  cases allowed with
  | pure signature => cases signature
  | memory signature => cases signature

end Exec.Abs
