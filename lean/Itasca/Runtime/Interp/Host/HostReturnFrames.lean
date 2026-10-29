import Itasca.Runtime.Interp.Relations.FrameStorePrefix
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A checked host return keeps the caller frame vector and writes its results
at the shared argument base. The live prefix below that base is retained. -/
structure HostReturnEffect (before after : runtime.interp.Execution) (base : Nat)
    (results : List val) : Prop where
  identity : after.store = before.store
  frames : after.frames = before.frames
  capacity : before.slots.length ≤ after.slots.length
  results : ValuesAt after.slots.val base results
  preserved : ∀ j, j < before.slots.length → j < base → after.slots.val[j]? = before.slots.val[j]?

theorem HostReturnEffect.preserve_prefix {before after : runtime.interp.Execution}
    {base : Nat} {results : List val} (effect : HostReturnEffect before after base results)
    {position : Nat} {bits : List Nat} (represented : WordsAt before.slots.val position bits)
    (below : position + bits.length ≤ base) : WordsAt after.slots.val position bits := by
  intro j bound
  obtain ⟨oldBound,value⟩ := represented j bound
  have newBound : position+j < after.slots.val.length := lt_of_lt_of_le oldBound effect.capacity
  refine ⟨newBound,?_⟩
  have same := effect.preserved (position+j) oldBound (by omega)
  simpa only [List.getElem!_eq_getElem?_getD,same] using value

theorem HostReturnEffect.preserve_binding {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    (effect : HostReturnEffect before after base results)
    {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store before raw source) : FrameBinding store after raw source := by
  obtain ⟨inst,fn,compiled,signature,owner,member,found,functionAt,wasm,code,typed,moduleEq,resultTypes,locals,capacity⟩ := binding
  refine ⟨inst,fn,compiled,signature,effect.identity.trans owner,?_,found,functionAt,wasm,code,typed,moduleEq,resultTypes,locals,capacity.trans effect.capacity⟩
  simpa only [effect.frames] using member

theorem HostReturnEffect.resume {before after : runtime.interp.Execution}
    {base : Nat} {results : List val} (effect : HostReturnEffect before after base results)
    {raw : runtime.interp.Frame} {caller : SourceMachine.AFrame}
    (saved : FrameSlots before raw caller)
    (destination : base = raw.base.val + Compiler.slots ((caller.locals ++ caller.vals).map Compiler.valueType)) :
    FrameSlots after raw {caller with vals := caller.vals ++ results} := by
  have kept := effect.preserve_prefix saved (by rw [Compiler.encode_values_length,destination])
  have combined := WordsAt.append kept (by simpa only [ValuesAt,Compiler.encode_values_length,←destination] using effect.results)
  simpa only [FrameSlots,ValuesAt,Compiler.encode_values_append,List.append_assoc] using combined

end Itasca.Runtime.Interp
