import Exec.Spec.Choices.ReadAuxiliaryUniqueness
/-! The actual stored function instance and canonical generated defaults
determine one call-entry frame and body. -/

namespace Exec.Spec
open SpecExt
private theorem values_admin_injective (left right : List val)
    (same : Map (fun value => admininstr_val value) left=Map (fun value => admininstr_val value) right) : left=right := by
  apply (List.map_inj_right ?_).mp same
  intro left right same
  cases left <;> cases right <;> simp_all [admininstr_val]

theorem source_function_entry_unique {object : funcinst}
    {leftArgs rightArgs : List val} {leftParams rightParams leftResults rightResults leftLocals rightLocals : List valtype}
    {leftModule rightModule : moduleinst} {leftBody rightBody : List instr} {leftIndex rightIndex : idx}
    {leftDefaults rightDefaults : List (Option val)}
    (leftFound : object=⟨.mk_functype (.mk_list leftParams) (.mk_list leftResults),leftModule,
      .FUNC leftIndex (leftLocals.map «local».LOCAL) leftBody⟩)
    (rightFound : object=⟨.mk_functype (.mk_list rightParams) (.mk_list rightResults),rightModule,
      .FUNC rightIndex (rightLocals.map «local».LOCAL) rightBody⟩)
    (arguments : Map (fun value => admininstr_val value) leftArgs=Map (fun value => admininstr_val value) rightArgs)
    (leftCount : leftDefaults.length=leftLocals.length) (rightCount : rightDefaults.length=rightLocals.length)
    (leftDefault : Forall₂ (fun option type => fun_default_ type option) leftDefaults leftLocals)
    (rightDefault : Forall₂ (fun option type => fun_default_ type option) rightDefaults rightLocals)
    (leftPresent : Forall (fun option => option≠none) leftDefaults)
    (rightPresent : Forall (fun option => option≠none) rightDefaults) :
    [admininstr.FRAME_ leftResults.length ⟨leftArgs++leftDefaults.map Option.get!,leftModule⟩
      [.LABEL_ leftResults.length [] (leftBody.map admininstr_instr)]] =
    [admininstr.FRAME_ rightResults.length ⟨rightArgs++rightDefaults.map Option.get!,rightModule⟩
      [.LABEL_ rightResults.length [] (rightBody.map admininstr_instr)]] := by
  have same := leftFound.symm.trans rightFound
  have types := congrArg funcinst.TYPE same
  have modules := congrArg funcinst.MODULE same
  have bodies := congrArg funcinst.CODE same
  simp only [functype.mk_functype.injEq,list.mk_list.injEq] at types
  simp only [funccode.FUNC.injEq] at bodies
  have locals := source_local_types_injective bodies.2.1
  have args := values_admin_injective leftArgs rightArgs arguments
  obtain ⟨_,rfl⟩ := types
  change leftModule=rightModule at modules
  cases modules
  cases locals
  have defaults := source_defaults_unique _ _ _ leftCount rightCount leftDefault rightDefault leftPresent rightPresent
  cases defaults
  cases args
  rw [bodies.2.2]
end Exec.Spec
