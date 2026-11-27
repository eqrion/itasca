import Itasca.Runtime.Integration.Invocation.Behaves

/-!
# Source budgets imply internal resource adequacy

This bridge is the only place that relates the public configuration charges to
flat simulation frames and compiler capacity witnesses.
-/

namespace Itasca.Spec.Resources
open Aeneas Aeneas.Std WebAssembly Itasca.Representation Itasca.Interp Itasca.Integration

private theorem sequence_append (left right : List admininstr) :
    sequenceWords (left ++ right) = sequenceWords left + sequenceWords right := by
  induction left with
  | nil => simp only [List.nil_append, sequenceWords, Nat.zero_add]
  | cons head tail ih => simp only [List.cons_append, sequenceWords, ih, Nat.add_assoc]

private theorem sequence_values (values : List val) :
    sequenceWords (vals values) = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    have charge : instructionWords (admininstr_val value) = 2 := by cases value <;> rfl
    simp only [vals, List.map_cons, sequenceWords] at *
    rw [charge, ih]
    simp only [List.length_cons]
    omega

private theorem labels_bound (labels : List SourceMachine.Label) (values : List val)
    (code : List admininstr) :
    2 * values.length + sequenceWords code ≤
      sequenceWords (SourceMachine.decodeLabels labels values code) := by
  induction labels generalizing values code with
  | nil => simp only [SourceMachine.decodeLabels, sequence_append, sequence_values, Nat.le_refl]
  | cons label rest ih =>
    have bound := ih (values.take label.height)
      ([.LABEL_ label.arity label.cont (vals (values.drop label.height) ++ code)] ++
        label.after.map admininstr_instr)
    simp only [SourceMachine.decodeLabels]
    simp only [sequence_append, sequenceWords, instructionWords, sequence_values] at bound
    have lengths := congrArg List.length (List.take_append_drop label.height values)
    simp only [List.length_append] at lengths
    omega

private theorem frames_bound (frames : List SourceMachine.AFrame) (inner : List admininstr) :
    suspendedSourceWords frames + sequenceWords inner ≤
      sequenceWords (SourceMachine.decodeFrames frames inner) := by
  induction frames generalizing inner with
  | nil => simp only [SourceMachine.decodeFrames, suspendedSourceWords, Nat.zero_add, Nat.le_refl]
  | cons frame rest ih =>
    have outer := ih [.FRAME_ frame.arity frame.toFrame
      (SourceMachine.decodeLabels frame.labels frame.vals (inner ++ frame.code.map admininstr_instr))]
    have labels := labels_bound frame.labels frame.vals (inner ++ frame.code.map admininstr_instr)
    have widths := slots_le_twice_length ((frame.locals ++ frame.vals).map valueType)
    simp only [List.length_map, List.length_append] at widths
    simp only [sequenceWords, instructionWords, SourceMachine.AFrame.toFrame, Nat.add_zero] at outer
    rw [sequence_append] at labels
    simp only [SourceMachine.decodeFrames, suspendedSourceWords, SourceMachine.AFrame.toFrame]
    omega

private theorem base_bound (frame : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (front extra : List val) (values : frame.vals = front ++ extra) :
    suspendedSourceWords rest + slots ((frame.locals ++ front).map valueType) ≤
      sequenceWords (SourceMachine.decodeFrames (frame :: rest) []) := by
  have bound := frames_bound (frame :: rest) []
  simp only [suspendedSourceWords, sequenceWords, Nat.add_zero, values,
    ← List.append_assoc, List.map_append, slots_append] at bound
  simp only [List.map_append, slots_append]
  omega

/-- A source function's coarse public allowance bounds any internal capacity witness. -/
theorem FunctionsFit.capacity {store : WebAssembly.store} {allowance address words : Nat}
    (fits : FunctionsFit store allowance)
    (capacity : SourceCanonicalFunctionCapacity store address words) : words ≤ allowance := by
  obtain ⟨function, env, typeIndex, _, found, correspondence, _, _,
    signature, declared, bytes, body, signatureAt, source, encoded, amount⟩ := capacity
  obtain ⟨signature', signatureAt', functionType⟩ := correspondence.signature
  have same : signature' = signature := Option.some.inj (signatureAt'.symm.trans signatureAt)
  subst signature'
  have bound := fits.bodies function (List.mem_of_getElem? found)
    (.mk_uN typeIndex.val) (declared.map (local.LOCAL ∘ Translation.valueType)) body bytes
    (signature.params.val.map Translation.valueType) (signature.results.val.map Translation.valueType)
    source functionType encoded
  have widths := slots_le_twice_length ((signature.params.val ++ declared).map Translation.valueType)
  simp only [List.length_map, List.length_append] at bound widths
  omega

private theorem steps_trans {first middle last : config} {events more : List HostEvent}
    (before : StepsH first events middle) (after : StepsH middle more last) :
    StepsH first (events ++ more) last := by
  induction before with
  | refl _ => simpa using after
  | cons step _ ih => simpa [List.append_assoc] using StepsH.cons step (ih after)

private theorem Fits.site {store : WebAssembly.store} {initial : config} {allowance values frames : Nat}
    (fits : Fits store initial allowance values frames) {events source address base}
    (reached : StepsH initial events (SourceMachine.decode source))
    (site : SourceInvocationSite source address base) :
    FunctionsFit source.store allowance ∧ base + allowance ≤ values := by
  rcases site with direct | indirect
  · obtain ⟨frame, rest, target, after, front, args, _, _, _, _, steps, _, _, _, _, rfl⟩ := direct
    have all := fits.reachable (events ++ []) source.store source.ambient _ (steps_trans reached steps.erase)
    have bound := base_bound {frame with code := .CALL (.mk_uN target) :: after, vals := front ++ args}
      rest front args rfl
    have storage := all.2.1
    exact ⟨all.1, by dsimp only [vals, List.map_nil] at bound storage ⊢; omega⟩
  · obtain ⟨frame, rest, table, type, position, after, front, args, _, _, _, _, steps,
      operands, _, _, _, _, _, rfl⟩ := indirect
    have all := fits.reachable (events ++ []) source.store source.ambient _ (steps_trans reached steps.erase)
    have bound := base_bound {frame with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after}
      rest front (args ++ [SourceMachine.integerVal .I32 position]) (by simpa [List.append_assoc] using operands)
    have storage := all.2.1
    exact ⟨all.1, by dsimp only [vals, List.map_nil] at bound storage ⊢; omega⟩

/-- Public source bounds suffice for the existing internal resource-exclusion proof. -/
theorem Fits.internal {store : WebAssembly.store} {address : funcaddr} {initial : config}
    {allowance values frames : Nat} (fits : Fits store initial allowance values frames)
    (initialWf : wf_config initial) : SourceResourcesFit store address initial values frames := by
  have allowanceFits : allowance ≤ values := by
    cases initial with
    | mk_config state body =>
      cases state with
      | mk_state source ambient =>
        have bound := (fits.reachable [] source ambient body (.refl initialWf)).2.1
        omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro function found
    cases signature : function.TYPE with
    | mk_functype params results =>
      cases params with
      | mk_list params =>
        cases results with
        | mk_list results =>
          have bound := fits.initialFunctions.signatures function (List.mem_of_getElem? found) params results signature
          simpa [signature, signatureWords] using bound.trans allowanceFits
  · intro words capacity
    exact (fits.initialFunctions.capacity capacity).trans allowanceFits
  · intro events final steps
    cases final with
    | mk_config state body =>
      cases state with
      | mk_state source ambient => exact (fits.reachable events source ambient body steps).2.2
  · intro events source steps
    refine ⟨(fits.reachable events source.store source.ambient _ steps).2.2, ?_, ?_⟩
    · intro callee base words site capacity
      obtain ⟨functions, bound⟩ := fits.site steps site
      have needed := functions.capacity capacity
      omega
    · intro callee identity base params results site host
      obtain ⟨functions, bound⟩ := fits.site steps site
      obtain ⟨module, found⟩ := host
      have needed := functions.signatures _ (List.mem_of_getElem? found) params results rfl
      omega

end Itasca.Spec.Resources
