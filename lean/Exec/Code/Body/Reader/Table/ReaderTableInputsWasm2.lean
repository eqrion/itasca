import Exec.Code.Body.Reader.Table.ReaderTableTargetsWasm2
import Exec.Code.Body.Reader.Table.ReaderTableScopesWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Every live canonical Wasm 2 BR_TABLE read supplies the source scope and
operand suffix certificate required by actual table lowering. -/
theorem reader_table_inputs_wasm2 {V : Type} (visitor : code.OpVisitor V)
    {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st)
    {parents current}
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (chain : SourceEntryChain parents current) (entered : current.entered=true)
    (known : ConcreteStack st.core.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base=false)
    (before after : V) (final : code.BodyState) (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback next)
    (accepted : code.branch_table_with visitor st data env .Wasm2 before=.ok (.Ok (),final,after)) :
    ∃ stack, Sequence.stackTypes st.core.vals.val=stack++[.I32] ∧
      TableOperandScopes (parents++[current]) stack (depths++[fallback]) := by
  obtain ⟨C,outer,spine,header,base,typed,controls,_,values⟩ := p.opened
  obtain ⟨count,first,selector,popped,all,arity,countDecoded,popCall,popControls,popPos,
    countEq,labelsDecoded,targets⟩ := reader_table_targets_wasm2 visitor before after st final data env
      _ p.current.ctrl controls p.opened.shape.core accepted
  obtain ⟨sourceCount,sourceFirst,defaultStart,countSource,lengthSource,labelsSource,defaultSource⟩ := encoded
  obtain ⟨rfl,rfl⟩ := countDecoded.unique countSource
  have allEq : all=depths++[fallback] := (labelsDecoded.unique (labelsSource.snoc defaultSource)
    (by simp only [List.length_append,List.length_singleton]; omega)).1
  rw [allEq] at targets
  have wholeKnown : ConcreteStack (outer++p.current.vals) := values ▸ known
  have segmentKnown := (concreteStack_append.mp wholeKnown).2
  have popSpec := code.pop_with_type.segment {st.core with pos := first} outer p.current.vals .I32
    values (by simpa [Control.base,controls] using base)
  rw [popCall,WP.spec_ok] at popSpec
  obtain ⟨_,_,remaining,poppedValues,popEffect⟩ := popSpec
  dsimp only at poppedValues popEffect
  have poly : Control.polymorphic {st.core with pos := first}=false := by
    simpa [Control.polymorphic,controls] using monomorphic
  rw [poly] at popEffect
  have segmentEq := typed_pop_exact segmentKnown popEffect
  have remainingKnown := (concreteStack_append.mp (segmentEq ▸ segmentKnown)).1
  have outerEq : outer=(p.parents.map Wasm2.Frames.Saved.vals).flatten := by
    simpa only [List.flatMap_def] using wasm2_spine_values spine
  have scopes := reader_table_scopes_wasm2 p same fronts chain entered popped remaining
    (by simpa only [outerEq] using poppedValues) popControls remainingKnown monomorphic
    (depths++[fallback]) (some arity) targets
  refine ⟨Sequence.stackTypes popped.vals.val,?_,scopes⟩
  simp only [values,segmentEq,poppedValues,Sequence.stackTypes,List.map_append,List.map_cons,List.map_nil,
    Translate.valueType,List.append_assoc]
end Exec.Code
