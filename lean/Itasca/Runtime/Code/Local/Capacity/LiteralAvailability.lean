import Itasca.Runtime.Code.Local.Capacity.AuxiliaryAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

inductive ScalarLiteralKind where
  | i32 | i64 | f32 | f64

def ScalarLiteralKind.opcode : ScalarLiteralKind → U16
  | .i32 => 65#u16 | .i64 => 66#u16 | .f32 => 67#u16 | .f64 => 68#u16

def ScalarLiteralKind.lowering {A : Type} (kind : ScalarLiteralKind) (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (bits : U128) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) :=
  match kind with
  | .i32 | .f32 => do
    let word ← lift (UScalar.cast .U32 bits)
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Const32 compiler.height word)
  | .i64 | .f64 => do
    let word ← lift (UScalar.cast .U64 bits)
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Const64 compiler.height word)

end Itasca.Runtime.Code
