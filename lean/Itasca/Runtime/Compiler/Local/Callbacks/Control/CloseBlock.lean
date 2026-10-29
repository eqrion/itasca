import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.Fixups
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Observe
/-! Closing a reachable ordinary block removes its compiler frame, resolves
its complete forward-fixup list, records the source/bytecode exit coordinates,
and preserves reachability. The proof follows the actual extracted callback. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem compiler_pc_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (target : U32)
    (position : target.val = compiler.function.code.val.length) :
    runtime.compiler.FunctionCompiler.pc ops compiler = .ok (.Ok target, compiler) := by
  unfold runtime.compiler.FunctionCompiler.pc
  simp only [lift, bind_ok]
  split
  · rename_i tooLarge
    have bound := target.hmax
    simp only [alloc.vec.Vec.len, core.num.U32.MAX, U32.rMax] at tooLarge
    scalar_tac
  · congr 3
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq, alloc.vec.Vec.len]
    scalar_tac

end Itasca.Runtime.Compiler
