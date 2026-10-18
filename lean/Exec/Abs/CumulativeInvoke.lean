import Exec.Abs.Invoke
import Exec.Abs.CumulativeState
namespace Exec.Abs
open SpecExt Exec.Spec

/-- A real defined function address and typed arguments construct the initial
abstract state and its generated specification call reduction. -/
theorem defined_cumulative_invocation (s : store) (ambient : frame) (address : funcaddr)
    (moduleInst : moduleinst) (typeIndex : idx) (params results : List valtype)
    (locals : List «local») (body : List instr) (args : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (functions : FunctionsTyped s)
    (covered : CumulativeFunctions s)
    (lookup : s.FUNCS[address]? = some ⟨⟨.mk_list params, .mk_list results⟩, moduleInst,
      .FUNC typeIndex locals body⟩)
    (arguments : ResultsTyped s params args) :
    ∃ defaults, defaultLocals locals = some defaults ∧
      ATyped (entryState s ambient address moduleInst results body args defaults) ∧
      CumulativeState (entryState s ambient address moduleInst results body args defaults) ∧
      StepH ⟨⟨s, ambient⟩, vals args ++ [.CALL_ADDR address]⟩ []
        (decode (entryState s ambient address moduleInst results body args defaults)) := by
  have member := List.mem_of_getElem? lookup
  have hfunc := functions _ member
  obtain ⟨C, bindings, emptyLocals, emptyLabels, _, hfunc⟩ := hfunc
  obtain ⟨defaults, hdefaults, hcallee⟩ := callee_frame_typed hs (function_module_wf hs member)
    bindings emptyLocals emptyLabels hfunc arguments address
  refine ⟨defaults, hdefaults, ?_, ?_, ?_⟩
  · refine ⟨hs, functions, ha, .cons hcallee (.nil results), by simp [entryState, Forall], by simp [entryState], ?_⟩
    intro frame hm
    simp only [entryState, List.mem_singleton] at hm
    subst frame
    exact frameTyped_heights hcallee
  · refine ⟨?_, covered⟩
    intro frame hm
    simp only [entryState, List.mem_singleton] at hm
    subst frame
    exact ⟨covered _ member, by simp [Forall]⟩
  · obtain ⟨types, hlocals, nonbot⟩ := function_local_types hfunc
    subst locals
    have result := call_invoke s ambient address typeIndex moduleInst params results types body args defaults
      hs ha lookup nonbot hdefaults (resultsTyped_wf arguments) (resultsTyped_length arguments)
    simpa [entryState, decode, decodeFrames, decodeLabels, vals, AFrame.arity, AFrame.toFrame, Label.arity] using result

end Exec.Abs
