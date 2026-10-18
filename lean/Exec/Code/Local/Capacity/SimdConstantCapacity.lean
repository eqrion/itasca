import Exec.Code.Local.Capacity.OperandBounds
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

theorem const_v128_valid_bounds (compiled : runtime.bytecode.CompiledFunction) (dst pool : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled (.ConstV128 dst pool) = .ok true) :
    dst.val + 2 ≤ compiled.slot_count.val ∧ pool.val < compiled.v128_pool.length := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.Instr.scalar,
    runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at checked
  obtain ⟨fits,fitRun,checked⟩ := bind_ok_inv _ _ _ checked
  cases fits with
  | false => simp at checked
  | true =>
    have bound := slots_fit_true compiled dst 2#u32 fitRun
    simp only [ite_true,lift,bind_ok,Result.ok.injEq,decide_eq_true_eq] at checked
    exact ⟨by simpa using bound,by simpa using checked⟩
end Exec.Code
