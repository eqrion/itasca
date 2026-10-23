import Exec.Theorems.Host.HostIndirectContext
import Exec.Interp.Calls.IndirectCallResolved
import Exec.Interp.Calls.IndirectResolve
import Exec.Interp.State.TableSource
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The actual extracted host call, including preparation and result checking,
refines an indirect source call under every suspended execution context. -/
theorem execute_indirect_host_frame_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (invariant : runtime.store.Store M → Prop)
    (shape : ∀ s, invariant s → Store.Shape view s)
    (sound : Platform.HostSound hooks invariant (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : invariant store)
    (sourceWf : ∀ s, invariant s → wf_store (Store.decodeStore view code s))
    (address : runtime.FuncAddr) (base : Usize) (ambient : frame) (wfAmbient : wf_frame ambient)
    (function : runtime.store.FuncInst) (identity : U64) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (values : List val)
    (typed : signature.params.val.map sourceType = values.map Code.valueType)
    (arguments : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) values)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt exec.slots.val base.val values)
    (issued : ∀ p args results answer,
      hooks.call_host p store identity args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (f : Abs.AFrame) (frameWf : wf_frame f.toFrame)
    (rest : List Abs.AFrame) (after : List instr) (table type position : U32) (front : List val)
    (labels : Abs.LabelsWf f.labels) (frontWf : Forall wf_val front)
    (tail : Forall wf_instr after) (callers : Forall Abs.FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (instanceIndex functionIndex rawBase : Usize) (entry selector callee : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst) (signatureIndex : Usize)
    (reference : U64)
    (instanceFound : store.instances.val[instanceIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[functionIndex.val]? = some compiled)
    (pairFound : compiled.indirect.val[entry.val]? = some (table,type))
    (tableMapped : inst.tables.val[table.val]? = some tableAddress)
    (tableFound : store.tables.val[tableAddress.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[rawBase.val+selector.val]! = position)
    (indexBound : rawBase.val+selector.val < exec.slots.length)
    (signatureMapped : inst.types.val[type.val]? = some signatureIndex)
    (baseOffset : base.val = rawBase.val+callee.val)
    (selected : object.elements.val[position.val]? = some reference)
    (word : reference.val = address.index.val+1)
    (signatureEq : function.signature = signatureIndex)
    (owner : address.store = store.id) (funcref : object.ty = .FuncRef)
    (moduleEq : f.toFrame.MODULE = Store.decodeInstance store inst) :
    runtime.interp.execute_call_indirect memory hooks floats allocator exec store platform
      instanceIndex functionIndex rawBase entry selector callee ⦃ out =>
      invariant out.2.2.1 ∧
      ((∃ error, out.1 = .Err error ∧ HostPreparationError error ∧ out.2.2.1 = store) ∨
       (HostCallSourceOutcome view code store f.toFrame address values base exec out ∧
        ∃ n, 2 ≤ n ∧ Spec.StepsHN n
          (Abs.decode ⟨Store.decodeStore view code store,ambient,
            {f with code := .CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val) :: after,vals := front ++ values ++ [Abs.integerVal .I32 position.val]} :: rest,[]⟩)
          (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out))) ⦄ := by
  have tableRead := table_lookup_decodes view code store inst f.toFrame table tableAddress object moduleEq tableMapped tableFound
  have sourceType : fun_type ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN type.val) =
      (Store.decodeFunction code store function).TYPE := by
    simp [fun_type,proj_uN_0,moduleEq,Store.decodeInstance,Store.decodeFunction,host,
      List.getElem!_eq_getElem?_getD,signatureMapped,←signatureEq,signatureAt]
  have resolved := indirect_resolve_reference view code store f table.val type.val position.val
    object reference address.index function tableRead funcref selected word functionAt
  rw [if_pos sourceType] at resolved
  have target := (Abs.Indirect.resolve_iff _ _ _ _ _ _).mp resolved
  have referenceShape := (shape store valid).tables object (List.mem_of_getElem? tableFound)
  have referenceBound := (referenceShape.2.2 reference (List.mem_of_getElem? selected)).word_bound store object.ty reference
  have castEq : (UScalar.cast .Usize reference).val = address.index.val+1 := by
    rw [UScalar.cast_val_eq]
    have lt : reference.val < 2^UScalarTy.Usize.numBits := by scalar_tac
    rw [Nat.mod_eq_of_lt lt,word]
  have nonzero : reference ≠ 0#u64 := by intro zero; rw [zero] at word; scalar_tac
  apply execute_call_indirect_resolved memory hooks floats allocator exec store platform
    instanceIndex functionIndex rawBase entry selector callee inst compiled table type tableAddress object position
    signatureIndex base address.index reference function instanceFound functionFound pairFound tableMapped tableFound
    input indexBound signatureMapped baseOffset selected nonzero castEq functionAt signatureEq
  have addressEq : (⟨store.id,address.index⟩ : runtime.FuncAddr) = address := by
    cases address with | mk id index => simp_all
  rw [addressEq]
  exact call_indirect_host_frame_source memory hooks floats allocator allocation interrupts view code
    invariant shape sound exec store platform valid sourceWf address base ambient wfAmbient
    function identity signature functionAt host signatureAt values typed arguments wellFormed fits represented issued
    f frameWf rest after table.val type.val position.val front labels frontWf tail callers heights target
    (by scalar_tac) (by scalar_tac) (by scalar_tac)
end Exec.Theorems
