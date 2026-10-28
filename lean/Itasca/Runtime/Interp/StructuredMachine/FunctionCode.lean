import Itasca.Runtime.Interp.StructuredMachine.Point
import Itasca.Runtime.Code.Local.Control.Table.StructuredFunction
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas.Std

/-- Function-local emission metadata and complete syntactic compiler evidence. -/
def FunctionCode (C : context)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS = params ++ declared ∧
  Code.StructuredFunctionCode (emission compiled C) C.TYPES C.FUNCS params declared results body compiled epilogue

theorem FunctionCode.entry {C params declared results body compiled epilogue}
    (certificate : FunctionCode C params declared results body compiled epilogue) :
    Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS results C.LOCALS compiled.code.val compiled.jump_tables.val
      [Code.functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  simpa only [certificate.1] using certificate.2.entry
end Itasca.Runtime.Interp.StructuredMachine
