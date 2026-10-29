import SpecExt.Host

/-! A flat abstract execution state over specification values and instructions.
The first frame and first label are innermost. Operand values retain Wasm's
bottom-to-top order. Addresses are specification addresses, never Rust handles. -/

namespace Itasca.Runtime.SourceMachine

structure Label where
  branchTypes : List valtype
  resultTypes : List valtype
  cont : List instr
  /-- Absolute value-stack height below the label's parameters. -/
  height : Nat
  /-- Enclosing code that resumes after this label exits. -/
  after : List instr

structure AFrame where
  fa : funcaddr
  /-- Result arity from the function's declared type. -/
  resultTypes : List valtype
  locals : List val
  module : moduleinst
  labels : List Label
  code : List instr
  vals : List val
  deriving Inhabited

structure AState where
  store : _root_.store
  /-- The external invocation's ambient frame. -/
  ambient : frame
  frames : List AFrame
  /-- Values returned when the final frame exits; empty while frames remain. -/
  results : List val

def Label.arity (label : Label) : Nat := label.branchTypes.length

def AFrame.arity (f : AFrame) : Nat := f.resultTypes.length

def AFrame.toFrame (f : AFrame) : frame := ⟨f.locals, f.module⟩

end Itasca.Runtime.SourceMachine
