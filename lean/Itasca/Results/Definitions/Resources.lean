import Itasca.Results.Definitions.Binary
import Itasca.Results.Definitions.Representation
import SpecExt.Host

/-!
# Sufficient source execution budgets

These bounds describe SpecTec configurations, source function signatures and independent
body encodings. They mention no compiled instructions, interpreter frames or allocator
requests. They are conservative sufficient conditions, not exact memory measurements.
-/

namespace Itasca.Spec

mutual
  /-- Number of nested source function activations in an instruction. -/
  def instrDepth : admininstr → Nat
    | .FRAME_ _ _ body => instrsDepth body + 1
    | .LABEL_ _ _ body => instrsDepth body
    | _ => 0

  /-- Maximum source function nesting in an administrative instruction sequence. -/
  def instrsDepth : List admininstr → Nat
    | [] => 0
    | ai :: rest => max (instrDepth ai) (instrsDepth rest)
end

/-- Source function nesting, excluding the ambient invocation frame. -/
def frameDepth : config → Nat
  | .mk_config _ body => instrsDepth body

namespace Resources

open Aeneas Aeneas.Std SpecExt Representation

mutual
  /-- A conservative storage charge: two words per local and per non-context
  instruction/value. Labels and frames contribute their active contents. Charging
  ordinary instructions too avoids depending on an interpreter operand layout. -/
  def instructionWords : admininstr → Nat
    | .FRAME_ _ frame body => 2 * frame.LOCALS.length + sequenceWords body
    | .LABEL_ _ _ body => sequenceWords body
    | _ => 2

  /-- Sum of source storage charges in an administrative instruction sequence. -/
  def sequenceWords : List admininstr → Nat
    | [] => 0
    | instruction :: rest => instructionWords instruction + sequenceWords rest
end

/-- Every source function fits one callee allowance. Signatures include host
functions. Defined bodies use two words per parameter/local plus 1000 words per
encoded instruction-body byte (excluding local declarations). Every permitted
encoding must fit; neither parser acceptance nor a chosen compiler artifact is assumed. -/
structure FunctionsFit (store : _root_.store) (calleeWords : Nat) : Prop where
  signatures : ∀ function ∈ store.FUNCS, ∀ params results,
    function.TYPE = .mk_functype (.mk_list params) (.mk_list results) →
    max (slots params) (slots results) ≤ calleeWords
  bodies : ∀ function ∈ store.FUNCS, ∀ index locals body (bytes : Slice U8) params results,
    function.CODE = .FUNC index locals body →
    function.TYPE = .mk_functype (.mk_list params) (.mk_list results) →
    Body.BodyEncoding bytes body →
    2 * (params.length + locals.length) + 1000 * bytes.length ≤ calleeWords

/-- A sufficient budget for an invocation from `store` and `initial`.
One common callee allowance covers the initial store and every reachable store,
including newly published host code. Every reachable configuration leaves that
allowance beyond its source storage charge and stays below the frame limit.
All source runs and host replies are covered, not just one terminating run. -/
structure Fits (store : _root_.store) (initial : config)
    (calleeWords valueLimit frameLimit : Nat) : Prop where
  initialFunctions : FunctionsFit store calleeWords
  reachable : ∀ events source ambient body,
    StepsH initial events ⟨⟨source, ambient⟩, body⟩ →
    FunctionsFit source calleeWords ∧
    sequenceWords body + calleeWords ≤ valueLimit ∧
    frameDepth ⟨⟨source, ambient⟩, body⟩ < frameLimit

end Resources
end Itasca.Spec
