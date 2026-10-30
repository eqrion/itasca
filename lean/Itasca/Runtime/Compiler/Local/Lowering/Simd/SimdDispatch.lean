import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdLowered
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

/-- The checked 0xfd compiler opcode interval delegates to SIMD lowering. -/
theorem lower_simd_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a b : U32) (bits : U128)
    (reachable : before.reachable = true) (lower : 512 ≤ opcode.val) (upper : opcode.val < 768) :
    runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits =
      runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits := by
  -- Fix both branches before reducing opcode literals. Letting `if_pos` infer
  -- them in each case retains the entire dispatcher in every proof term.
  have choose (op : U16) :
      (if before.reachable then
        runtime.compiler.simd.FunctionCompiler.simd_op ops before state op a bits
      else runtime.compiler.FunctionCompiler.observe ops before state) =
        runtime.compiler.simd.FunctionCompiler.simd_op ops before state op a bits :=
    if_pos reachable
  rcases opcode with ⟨⟨n, hn⟩⟩
  change 512 ≤ n at lower
  change n < 768 at upper
  interval_cases n <;> exact choose _

end Itasca.Runtime.Compiler
