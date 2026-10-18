import Exec.Interp.Cumulative.Machine
import Exec.Interp.Machines.Cumulative.CumulativeCompiledFunctions
import Exec.Interp.StructuredMachine.CompiledFunctions
import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Local.Control.Table.StructuredCodeTableLegacy
namespace Exec.Interp.Cumulative

theorem function_code {C params declared results body compiled epilogue}
    (certificate : Code.CumulativeFunctionCode C params declared results body compiled epilogue) :
    StructuredMachine.FunctionCode emission C params declared results body compiled epilogue :=
  ⟨certificate.1, certificate.2.with_tables (fun _ _ _ _ h => h.not_branchTable)⟩

theorem compiled_functions {M : Type} {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certificate : CumulativeCompiledFunctions code store) :
    StructuredMachine.CompiledFunctions emission code store := by
  intro function member instanceIndex functionIndex lookup
  obtain ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,source,table,types,cert⟩ :=
    certificate function member instanceIndex functionIndex lookup
  exact ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,source,table,types,function_code cert⟩

theorem compiled_functions_legacy {M : Type} {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (certificate : StructuredMachine.CompiledFunctions emission code store) :
    CumulativeCompiledFunctions code store := by
  intro function member instanceIndex functionIndex lookup
  obtain ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,source,table,types,cert⟩ :=
    certificate function member instanceIndex functionIndex lookup
  refine ⟨inst,compiled,signature,declared,body,epilogue,hi,hc,hs,source,table,types,cert.1,?_⟩
  rcases cert.2 with ⟨signature,locals,parameterSlots,localSlots,capacity,fetchBound,checked,bodyCode,returnCode,endPosition⟩
  exact ⟨signature,locals,parameterSlots,localSlots,capacity,fetchBound,checked,
    bodyCode.to_old (fun _ depths fallback _ _ _ h => h.not_branchTable depths fallback rfl),returnCode,endPosition⟩
end Exec.Interp.Cumulative
