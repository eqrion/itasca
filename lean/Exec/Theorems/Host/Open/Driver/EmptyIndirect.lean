import Exec.Theorems.Host.Open.Driver.EmptyHost
import Exec.Theorems.Host.Open.Driver.IndirectFetch
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- A fetched indirect call with a present non-null matching host target
actually suspends with empty copied arguments. All table and signature tests
are discharged from raw lookups, rather than an assumed host-call outcome. -/
theorem prepare_empty_indirect {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (frameIndex : Usize) (frame : runtime.interp.Frame) (entry index : U32)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (table type : U32) (tableAddress : runtime.TableAddr) (object : runtime.store.Table)
    (position : U32) (reference : U64) (address : Usize) (function : runtime.store.Function)
    (identity : U64) (signature : Itasca.types.FuncType)
    (last : frameIndex.val+1=exec.frames.length) (frameAt : exec.frames.val[frameIndex.val]?=some frame)
    (fetched : compiled.code.val[frame.pc.val]?=some (.CallIndirect entry index 0#u32))
    (pcBound : frame.pc.val<U32.max) (base : frame.base=0#usize)
    (instanceAt : store.instances.val[frame.instance.val]?=some inst)
    (compiledAt : inst.module.functions.val[frame.function.val]?=some compiled)
    (pairAt : compiled.indirect.val[entry.val]?=some (table,type))
    (tableMapped : inst.tables.val[table.val]?=some tableAddress)
    (tableAt : store.tables.val[tableAddress.index.val]?=some object)
    (input : UScalar.cast .U32 exec.slots.val[frame.base.val+index.val]! =position)
    (indexBound : frame.base.val+index.val<exec.slots.length)
    (signatureAt : inst.types.val[type.val]?=some function.signature)
    (selected : object.elements.val[position.val]?=some reference) (nonzero : reference≠0#u64)
    (encoded : (UScalar.cast .Usize reference).val=address.val+1)
    (functionAt : store.funcs.val[address.val]?=some function) (kind : function.code=.Host identity)
    (typeAt : store.types.val[function.signature.val]?=some signature)
    (params : signature.params.val=[]) (results : signature.results.val=[])
    (scratch : exec.host_args=alloc.vec.Vec.new runtime.Value) :
    ∃next : U32,next.val=frame.pc.val+1 ∧
      prepareStep memory (inert memory) floats allocator exec store ()=
        .ok (.pending {exec with frames:=exec.frames.set frameIndex {frame with pc:=next}}
          store () ⟨store.id,address⟩ 0#usize identity (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)) := by
  let post : CallPhase M Unit → Prop := fun phase=>∃next : U32,next.val=frame.pc.val+1 ∧
    phase=.pending {exec with frames:=exec.frames.set frameIndex {frame with pc:=next}}
      store () ⟨store.id,address⟩ 0#usize identity (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)
  have selectedBound : position.val<object.elements.length := (List.getElem?_eq_some_iff.mp selected).1
  have targetUnique : ∀r : U64,∀a : Usize,∀f : runtime.store.Function,
      object.elements.val[position.val]?=some r → (UScalar.cast .Usize r).val=a.val+1 →
      store.funcs.val[a.val]?=some f → r=reference ∧ a=address ∧ f=function := by
    intro r a f found bits target
    have same : r=reference := Option.some.inj (found.symm.trans selected)
    subst r
    have sameAddress : a=address := by scalar_tac
    subst a
    exact ⟨rfl,rfl,Option.some.inj (target.symm.trans functionAt)⟩
  have total : prepareStep memory (inert memory) floats allocator exec store () ⦃post⦄ := by
    apply prepare_step_indirect_effect memory (inert memory) floats allocator exec store () frameIndex frame entry index 0#u32
      inst compiled table type tableAddress object position function.signature 0#usize last frameAt fetched pcBound instanceAt compiledAt
      pairAt tableMapped tableAt input indexBound signatureAt (by rw [base]; simp)
      (fun r found _=>by
        have same : r=reference := Option.some.inj (found.symm.trans selected)
        subst r
        exact ⟨address,function,encoded,functionAt⟩) post
    · intro next nextEq outside
      exact False.elim (outside selectedBound)
    · intro next nextEq null
      exact False.elim (nonzero (Option.some.inj (selected.symm.trans null)))
    · intro next nextEq r a f found notNull bits target different
      obtain ⟨refEq,addrEq,funEq⟩ := targetUnique r a f found bits target
      subst r
      subst a
      subst f
      exact False.elim (different rfl)
    · intro next nextEq r a f found notNull bits target sameSignature
      obtain ⟨refEq,addrEq,funEq⟩ := targetUnique r a f found bits target
      subst r
      subst a
      subst f
      rw [prepare_empty_host memory floats allocator allocation available {exec with frames:=exec.frames.set frameIndex {frame with pc:=next}} store ⟨store.id,address⟩ function identity signature
        functionAt kind typeAt params results scratch]
      exact WP.spec.ret ⟨next,nextEq,rfl⟩
  obtain ⟨phase,actual,next,nextEq,rfl⟩ := WP.spec_imp_exists total
  exact ⟨next,nextEq,actual⟩
end Exec.Theorems.OpenReentrantControl
