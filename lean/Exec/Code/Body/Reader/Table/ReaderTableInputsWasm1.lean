import Exec.Code.Body.Reader.Table.ReaderTableTargetsWasm1
import Exec.Code.Local.Relations.Table.BranchTableOperands
import Exec.Code.Body.Reader.Table.ReaderTableSource
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- The live Wasm 1 reader establishes exact source operands for every table
arm using its common-type check and the canonical saved-scope zipper. -/
theorem reader_table_inputs_wasm1 {V : Type} (visitor : code.OpVisitor V)
    {data env ctx bt st} (p : Wasm1.Pending data env ctx bt st)
    {parents current}
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (chain : SourceEntryChain parents current) (entered : current.entered=true)
    (known : ConcreteStack st.vals.val)
    (monomorphic : p.current.ctrl.polymorphic_base=false)
    (before after : V) (final : code.OpIterState) (actual : U32) (common : code.BlockType)
    (depths : List U32) (fallback : U32) (next : Usize)
    (encoded : BrTable.Decoded data st.pos depths fallback next)
    (accepted : code.read_br_table visitor st data before=.ok (.Ok (actual,common),final,after)) :
    ∃ stack, Sequence.stackTypes st.vals.val=stack++[.I32] ∧
      TableOperandScopes (parents++[current]) stack (depths++[fallback]) := by
  obtain ⟨C,outer,spine,header,base,typed,controls,values⟩ := p.opened
  have segmentKnown := (concreteStack_append.mp (values ▸ known)).2
  have erased := code.read_br_table.accepted_erasure visitor st data before (actual,common) final after accepted
  have checked := reader_table_targets_wasm1_spec code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data ()
    _ p.current.ctrl outer p.current.vals controls values base segmentKnown monomorphic
    (fun _ _ _ => ⟨.Ok (),(),rfl⟩)
  rw [erased,WP.spec_ok] at checked
  obtain ⟨actualDepths,front,decoded,targets,arguments⟩ := checked actual common rfl
  obtain ⟨rfl,rfl,_⟩ := decoded.unique encoded
  have outerEq : outer=(p.parents.map Wasm1.Frames.Saved.vals).flatten := by
    simpa only [List.flatMap_def] using wasm1_spine_values spine
  have sourceFront : Sequence.stackTypes outer=current.front := by simpa only [outerEq] using fronts.current.symm
  refine ⟨current.front++front++Control.resultTypes common,?_,?_⟩
  · simp only [values,Sequence.stackTypes,List.map_append] at *
    rw [arguments,sourceFront]
    simp only [List.append_assoc]
  · intro depth member
    obtain ⟨bound,targetType⟩ := targets depth member
    let target := st.ctrls.val[st.ctrls.val.length-1-depth.val]'(by omega)
    have targetAt : st.ctrls.val.reverse[depth.val]?=some target := by
      rw [List.getElem?_reverse bound]
      exact List.getElem?_eq_getElem (by omega)
    obtain ⟨scope,scopeAt,branchTypes⟩ := same.label p.opened depth.val target targetAt
    have commonEq : common=Control.targetBlockType target := Option.some.inj targetType
    have branchEq : scope.branchTypes=Control.resultTypes common := by
      simpa only [Control.targetTypes,Control.resultTypes,←commonEq] using branchTypes
    obtain ⟨outside,frontEq⟩ := fronts.selected depth.val scope scopeAt
    have selected : (parents++[current]).reverse[depth.val]?=some scope := by
      simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using scopeAt
    refine ⟨scope,outside++front,selected,chain.all_entered entered scope ?_,?_⟩
    · simpa only [List.mem_reverse] using List.mem_of_getElem? selected
    · rw [branchEq,frontEq]
      simp only [List.append_assoc]
end Exec.Code
