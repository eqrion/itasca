import Itasca.Runtime.Compiler.Local.Capacity.OperandBounds
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdConstructor
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem simd_view_disjoint (instruction : runtime.bytecode.Instr) (op dst a entry : U32)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (op,dst,a,entry))) :
    runtime.bytecode.Instr.scalar instruction = .ok none ∧
    runtime.bytecode.Instr.load instruction = .ok none ∧
    runtime.bytecode.Instr.store instruction = .ok none := by
  cases instruction
  all_goals simp only [runtime.bytecode.Instr.simd,Result.ok.injEq,Option.some.injEq,reduceCtorEq,Prod.mk.injEq] at view
  all_goals first | contradiction | exact ⟨rfl,rfl,rfl⟩

theorem simd_valid_bounds (compiled : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (op dst a entry wa wb wc wr : U32)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (op,dst,a,entry)))
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled instruction = .ok true) :
    a.val + wa.val + wb.val + wc.val ≤ compiled.slot_count.val ∧
    dst.val + wr.val ≤ compiled.slot_count.val ∧ entry.val < compiled.simd.length := by
  obtain ⟨scalar,load,store⟩ := simd_view_disjoint instruction op dst a entry view
  unfold runtime.bytecode.CompiledFunction.instruction_valid at checked
  simp only [scalar,load,store,view,shape,bind_ok,uncurry_apply_pair] at checked
  obtain ⟨xy,xyRun,checked⟩ := bind_ok_inv _ _ _ checked
  obtain ⟨xyz,xyzRun,checked⟩ := bind_ok_inv _ _ _ checked
  have xyFact := UScalar.add_equiv wa wb
  rw [xyRun] at xyFact
  have xyVal : xy.val = wa.val+wb.val := xyFact.2.1
  have xyzFact := UScalar.add_equiv xy wc
  rw [xyzRun] at xyzFact
  have xyzVal : xyz.val = xy.val+wc.val := xyzFact.2.1
  obtain ⟨fits,fitRun,checked⟩ := bind_ok_inv _ _ _ checked
  cases fits with
  | false => simp at checked
  | true =>
    simp only [ite_true] at checked
    obtain ⟨fits,fitOut,checked⟩ := bind_ok_inv _ _ _ checked
    cases fits with
    | false => simp at checked
    | true =>
      have inputs := slots_fit_true compiled a xyz fitRun
      have outputs := slots_fit_true compiled dst wr fitOut
      simp only [ite_true,lift,bind_ok,Result.ok.injEq,decide_eq_true_eq] at checked
      exact ⟨by omega,outputs,by simpa using checked⟩
end Itasca.Runtime.Compiler
