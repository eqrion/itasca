import Exec.Interp.Relations.FrameStorePrefix
namespace Exec.Interp
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
    {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store before raw source) : FrameBinding store after raw source := by
  obtain ⟨inst,fn,compiled,signature,owner,member,found,functionAt,wasm,code,typed,moduleEq,resultTypes,locals,capacity⟩ := binding
  refine ⟨inst,fn,compiled,signature,effect.identity.trans owner,?_,found,functionAt,wasm,code,typed,moduleEq,resultTypes,locals,capacity.trans effect.capacity⟩
  simpa only [effect.frames] using member

theorem HostReturnEffect.resume {before after : runtime.interp.Execution}
    {base : Nat} {results : List val} (effect : HostReturnEffect before after base results)
    {raw : runtime.interp.Frame} {caller : Abs.AFrame}
    (saved : FrameSlots before raw caller)
    (destination : base = raw.base.val + Code.slots ((caller.locals ++ caller.vals).map Code.valueType)) :
    FrameSlots after raw {caller with vals := caller.vals ++ results} := by
  have kept := effect.preserve_prefix saved (by rw [Code.encodeValues_length,destination])
  have combined := WordsAt.append kept (by simpa only [ValuesAt,Code.encodeValues_length,←destination] using effect.results)
  simpa only [FrameSlots,ValuesAt,Code.encodeValues_append,List.append_assoc] using combined

theorem SavedFrame.resume_host {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {base : Nat} {raw : runtime.interp.Frame}
    {source : Abs.AFrame} {waiting : List valtype} {results : List val}
    (saved : SavedFrame store before raw source waiting base)
    (effect : HostReturnEffect before after base results)
    (types : results.map Code.valueType = waiting) (heights : Abs.FrameHeights source) :
    ActiveFrame store after raw {source with vals := source.vals ++ results} := by
  refine ⟨effect.preserve_binding saved.binding,effect.resume saved.slots saved.destination,?_⟩
  obtain ⟨compiled,functions,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,functions,targets,next,output,false,program,.ready (point.resume results types heights)⟩

theorem SavedFrames.host_preserved {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raws sources waiting boundary}
    (saved : SavedFrames store before raws sources waiting boundary)
    (effect : HostReturnEffect before after base results) (below : boundary ≤ base) :
    SavedFrames store after raws sources waiting boundary := by
  apply saved.transport
  · intro raw source binding member
    exact effect.preserve_binding binding
  · intro position bits represented bound
    exact effect.preserve_prefix represented (bound.trans below)

/-- A synchronous host call does not push a concrete Wasm frame. Its waiting
caller becomes active again after the checked result write, while every older
caller keeps its own saved continuation. -/
theorem host_return_stack {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raw : runtime.interp.Frame} {raws : List runtime.interp.Frame}
    {caller : Abs.AFrame} {rest : List Abs.AFrame} {waiting : List valtype}
    (frames : before.frames.val = raws.reverse ++ [raw])
    (saved : SavedFrame store before raw caller waiting base)
    (older : SavedFrames store before raws rest caller.resultTypes raw.base.val)
    (effect : HostReturnEffect before after base results)
    (types : results.map Code.valueType = waiting) (heights : Abs.FrameHeights caller) :
    FrameStackRel store after ({caller with vals := caller.vals ++ results} :: rest) ∧
      ReadyTop store after {caller with vals := caller.vals ++ results} := by
  refine ⟨.active (by simpa only [effect.frames] using frames)
    (saved.resume_host effect types heights) (older.host_preserved effect saved.base_le),?_⟩
  obtain ⟨compiled,functions,targets,next,output,program,point⟩ := saved.continuation
  refine ⟨raw,compiled,functions,targets,next,output,?_,program,point.resume results types heights⟩
  simp only [effect.frames,frames,List.getLast?_concat]

/-- The same host result can resume after new functions, signatures, and
instances were appended. This requires explicit preservation of old raw frame
metadata; decoded store extension alone does not supply that fact. -/
theorem host_return_stack_extended {M : Type} {beforeStore afterStore : runtime.store.Store M}
    (retained : FrameStorePrefix beforeStore afterStore) (bounds : FrameTypeBounds beforeStore)
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raw : runtime.interp.Frame} {raws : List runtime.interp.Frame}
    {caller : Abs.AFrame} {rest : List Abs.AFrame} {waiting : List valtype}
    (frames : before.frames.val = raws.reverse ++ [raw])
    (saved : SavedFrame beforeStore before raw caller waiting base)
    (older : SavedFrames beforeStore before raws rest caller.resultTypes raw.base.val)
    (effect : HostReturnEffect before after base results)
    (types : results.map Code.valueType = waiting) (heights : Abs.FrameHeights caller) :
    FrameStackRel afterStore after ({caller with vals := caller.vals ++ results} :: rest) ∧
      ReadyTop afterStore after {caller with vals := caller.vals ++ results} := by
  obtain ⟨stack,ready⟩ := host_return_stack frames saved older effect types heights
  exact ⟨stack.store_prefix retained bounds,ready.store_prefix retained⟩

end Exec.Interp
