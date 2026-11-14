import SpecExt.Builtins

/-!
Sections, each formerly its own module: State, Decode.
-/

/-! ## State -/

section

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

end

/-! ## Decode -/

section

/-! Reconstruct nested specification evaluation contexts from flat frames and
absolute label heights. The innermost frame's current values and code appear
at the unique redex position, before the suspended callers' continuations. -/

namespace Itasca.Runtime.SourceMachine
open SpecExt

def decodeLabels : List Label → List val → List admininstr → List admininstr
  | [], values, code => vals values ++ code
  | label :: rest, values, code =>
      decodeLabels rest (values.take label.height)
        ([.LABEL_ label.arity label.cont (vals (values.drop label.height) ++ code)] ++
          label.after.map admininstr_instr)

def decodeFrames : List AFrame → List admininstr → List admininstr
  | [], inner => inner
  | f :: rest, inner =>
      decodeFrames rest [.FRAME_ f.arity f.toFrame
        (decodeLabels f.labels f.vals (inner ++ f.code.map admininstr_instr))]

def decode (s : AState) : config :=
  .mk_config (.mk_state s.store s.ambient) (decodeFrames s.frames (vals s.results))

@[simp] theorem decode_labels_nil (values : List val) (code : List admininstr) :
    decodeLabels [] values code = vals values ++ code := rfl

@[simp] theorem decode_frames_nil (code : List admininstr) : decodeFrames [] code = code := rfl

end Itasca.Runtime.SourceMachine

end
