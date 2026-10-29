import Itasca.Runtime.Interp.Machine.Point
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredFunction

/-!
Function-local emission metadata and complete syntactic compiler evidence.

Main declarations: `FunctionCode`. A direct consumer is `Interp.Machine.Calls.CallStackEntry`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

/-- Function-local emission metadata and complete syntactic compiler evidence. -/
def FunctionCode (C : context)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS = params ++ declared ∧
  Compiler.StructuredFunctionCode (emission compiled C) C.TYPES C.FUNCS params declared results body compiled epilogue

theorem FunctionCode.entry {C params declared results body compiled epilogue}
    (certificate : FunctionCode C params declared results body compiled epilogue) :
    Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS results C.LOCALS compiled.code.val compiled.jump_tables.val
      [Compiler.functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  simpa only [certificate.1] using certificate.2.entry
end Itasca.Runtime.Interp.Machine
