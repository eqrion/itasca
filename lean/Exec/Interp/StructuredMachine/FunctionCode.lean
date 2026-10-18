import Exec.Interp.StructuredMachine.Point
import Exec.Code.Local.Control.Table.StructuredFunctionWithTables
namespace Exec.Interp.StructuredMachine
open Aeneas.Std

/-- Function-local emission metadata and complete syntactic compiler evidence. -/
def FunctionCode (emission : FunctionEmission) (C : context)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS = params ++ declared ∧
  Code.StructuredFunctionCodeWithTables (emission compiled C) C.TYPES C.FUNCS params declared results body compiled epilogue

theorem FunctionCode.entry {emission C params declared results body compiled epilogue}
    (certificate : FunctionCode emission C params declared results body compiled epilogue) :
    Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS results C.LOCALS compiled.code.val compiled.jump_tables.val
      [Code.functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  simpa only [certificate.1] using certificate.2.entry
end Exec.Interp.StructuredMachine
