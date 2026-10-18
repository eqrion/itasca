import Exec.Abs.State

/-! Reconstruct nested specification evaluation contexts from flat frames and
absolute label heights. The innermost frame's current values and code appear
at the unique redex position, before the suspended callers' continuations. -/

namespace Exec.Abs
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

/-- A completed invocation exposes precisely its returned values. -/
theorem decode_done (s : store) (ambient : frame) (results : List val) :
    decode ⟨s, ambient, [], results⟩ = .mk_config (.mk_state s ambient) (vals results) := rfl

/-- One active function, before entering a structured label. -/
theorem decode_one_frame (s : store) (ambient : frame) (f : AFrame)
    (h : f.labels = []) :
    decode ⟨s, ambient, [f], []⟩ =
      .mk_config (.mk_state s ambient)
        [.FRAME_ f.arity f.toFrame (vals f.vals ++ f.code.map admininstr_instr)] := by
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, h, decodeLabels]

end Exec.Abs
