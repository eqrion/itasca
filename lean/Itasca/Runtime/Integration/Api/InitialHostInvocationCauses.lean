import Itasca.Runtime.Integration.Host.HostDispatchCauses
import Itasca.Runtime.Interp.Invocation.PrefixCauses
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Exact initial-host invocation causes. Setup retains the initial store;
readback retains the completed source host event and its actual refused result
request; call failure retains the exact prepared base-zero helper execution. -/
def InitialHostInvocationCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (ambient : frame) (address : runtime.FuncAddr) (identity : U64)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  (after=store ∧ InvocationResourceCause allocator exec store signature results error) ∨
  (error=.Exhausted .Allocation ∧ ∃ values,
    ResultsTyped (Store.decodeStore view code after) (signature.results.val.map sourceType) values ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
      [.call address.index.val (args.val.map sourceValue) (some values)]
      ⟨⟨Store.decodeStore view code after,ambient⟩,vals values⟩ ∧
    ∃ n : Usize, n.val=signature.results.length-results.length ∧ allocator.reserve results n=.ok (false,results)) ∨
  ∃ (prepared : runtime.interp.Execution) (p : P)
    (called : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P),
    prepared.store=store.id ∧ prepared.frames.val=[] ∧ ValuesAt prepared.slots.val 0 (args.val.map sourceValue) ∧
    runtime.interp.call memory hooks floats allocator prepared store p address 0#usize=.ok called ∧
    called.1=.Err error ∧ called.2.2.1=after ∧
    HostCallCauses allocator hooks prepared store p signature 0#usize identity called

/-- Values refusal before or during initial host preparation uses only the
source signature buffers. There is no source Wasm frame requirement to invent. -/
theorem InitialHostInvocationCause.source_values {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after (.Exhausted .Values)) :
    store.limits.max_values.val<signatureWords (Store.decodeFuncType signature) := by
  rcases cause with ⟨same,cause⟩ | ⟨impossible,_⟩ | ⟨prepared,p,called,_,_,_,_,failed,_,cause⟩
  · exact cause
  · cases impossible
  · simpa only [HostCallCauses,failed,HostPreparationCause,hostSlotDemand,typeSlots,
      (show (0#usize).val = 0 from rfl),Nat.zero_add,Store.decodeFuncType,signatureWords,Nat.max_comm] using cause

/-- Every initial-host allocation refusal is an actual request bounded by
source parameter/result lengths or the source signature's slot width. -/
theorem InitialHostInvocationCause.source_allocation {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after (.Exhausted .Allocation)) :
    HostSignatureAllocation allocator (signature.params.val.map sourceType) (signature.results.val.map sourceType) 0 := by
  rcases cause with ⟨same,cause⟩ | ⟨_,values,typed,source,n,amount,refused⟩ | ⟨prepared,p,called,_,_,_,_,failed,_,cause⟩
  · rcases cause with ⟨n,bound,refused⟩ | ⟨n,amount,refused⟩
    · exact Or.inl ⟨exec.slots,n,by simpa only [Nat.zero_add,typeSlots] using bound,refused⟩
    · refine Or.inr (Or.inr ⟨results,n,?_,refused⟩)
      simp only [List.length_map]
      simp only [alloc.vec.Vec.length] at amount
      omega
  · refine Or.inr (Or.inr ⟨results,n,?_,refused⟩)
    simp only [List.length_map]
    simp only [alloc.vec.Vec.length] at amount
    omega
  · simp only [HostCallCauses,failed,HostPreparationCause] at cause
    rcases cause with ⟨n,bound,refused⟩ | ⟨n,bound,refused⟩ | ⟨n,bound,refused⟩
    · exact Or.inl ⟨prepared.slots,n,by simpa only [hostSlotDemand,typeSlots,(show (0#usize).val = 0 from rfl),Nat.zero_add,Nat.max_comm] using bound,refused⟩
    · exact Or.inr (Or.inl ⟨prepared.host_args,n,by simpa only [List.length_map] using bound,refused⟩)
    · exact Or.inr (Or.inr ⟨prepared.host_results,n,by simpa only [List.length_map] using bound,refused⟩)

theorem InitialHostInvocationCause.interrupted {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after .Terminated) :
    ∃ p next, hooks.interrupt p=.ok (.Terminate,next) := by
  rcases cause with ⟨same,impossible⟩ | ⟨impossible,_⟩ | ⟨prepared,p,called,_,_,_,_,failed,_,cause⟩
  · exact False.elim impossible
  · cases impossible
  · exact ⟨p,by simpa only [HostCallCauses,failed,HostPreparationCause] using cause⟩

theorem InitialHostInvocationCause.host_overflow {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {signature : Itasca.types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after (.Exhausted .CallStack)) :
    ∃ p arguments defaults host returned,
      hooks.call_host p store identity arguments defaults=.ok (.Err .StackOverflow,host,after,returned) := by
  rcases cause with ⟨same,impossible⟩ | ⟨impossible,_⟩ | ⟨prepared,p,called,_,_,_,_,failed,same,cause⟩
  · exact False.elim impossible
  · cases impossible
  · simp only [HostCallCauses,failed] at cause
    obtain ⟨next,arguments,defaults,returned,actual⟩ := cause
    exact ⟨next,arguments,defaults,called.2.2.2,returned,by simpa only [same] using actual⟩
end Itasca.Runtime.Integration
