import Itasca.Runtime.Code.Body.Reader.Table.ReaderTableSuffix
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableOperands
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Canonical target checks and the saved source zipper discharge every static
branch-table operand obligation on a live path. -/
theorem reader_table_scopes_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {parents current}
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (chain : SourceEntryChain parents current) (entered : current.entered=true)
    (popped : code.OpIterState) (segment : List code.StackType)
    (values : popped.vals.val=(p.parents.map Wasm2.Frames.Saved.vals).flatten++segment)
    (controls : popped.ctrls=st.core.ctrls) (known : ConcreteStack segment)
    (monomorphic : p.current.ctrl.polymorphic_base=false)
    (depths : List U32) (arity : Option Usize)
    (targets : Wasm2.TableTargets env ⟨popped⟩ depths arity) :
    TableOperandScopes (parents++[current]) (Sequence.stackTypes popped.vals.val) depths := by
  intro depth member
  obtain ⟨view,types,n,selected,resolved,_,_,suffix⟩ := targets depth member
  have blocks : (code.BodyState.mk popped).blocks=st.blocks := code.BodyState.blocks_eq_of_ctrls controls
  have originalSelected : Wasm2.labelAt st depth.val=some view := by
    simpa only [Wasm2.labelAt,blocks,controls] using selected
  obtain ⟨scope,actual,scopeAt,actualResolved,branchTypes⟩ := same.label p.opened depth.val view originalSelected
  have typeEq : actual=types := by rw [resolved] at actualResolved; exact Option.some.inj actualResolved.symm
  subst actual
  obtain ⟨C,outer,spine,header,base,typed,savedControls,_,originalValues⟩ := p.opened
  have outerEq : outer=(p.parents.map Wasm2.Frames.Saved.vals).flatten := by
    simpa only [List.flatMap_def] using wasm2_spine_values spine
  have poppedBase : (Control.base popped).val=(p.parents.map Wasm2.Frames.Saved.vals).flatten.length := by
    simpa [Control.base,controls,savedControls,outerEq] using base
  have poppedMono : Control.polymorphic popped=false := by
    simpa [Control.polymorphic,controls,savedControls] using monomorphic
  obtain ⟨front,arguments⟩ := table_suffix_concrete popped _ segment types values poppedBase poppedMono known suffix
  obtain ⟨discarded,whole⟩ := fronts.branch depth.val scope scopeAt segment front
    (by simpa only [branchTypes] using arguments)
  have selected' : (parents++[current]).reverse[depth.val]?=some scope := by
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using scopeAt
  refine ⟨scope,discarded,selected',chain.all_entered entered scope ?_,?_⟩
  · simpa only [List.mem_reverse] using List.mem_of_getElem? selected'
  · simpa only [values] using whole
end Itasca.Runtime.Code
