import Itasca.Runtime.Abs.State

/-! Reconstruct nested specification evaluation contexts from flat frames and
absolute label heights. The innermost frame's current values and code appear
at the unique redex position, before the suspended callers' continuations. -/

namespace Itasca.Runtime.Abs
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

@[simp] theorem decodeLabels_nil (values : List val) (code : List admininstr) :
    decodeLabels [] values code = vals values ++ code := rfl

@[simp] theorem decodeFrames_nil (code : List admininstr) : decodeFrames [] code = code := rfl

end Itasca.Runtime.Abs
