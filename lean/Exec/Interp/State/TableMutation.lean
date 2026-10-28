import Exec.Interp.State.TableSource
import Exec.Interp.Relations.FrameStoreMetadata
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Itasca.Runtime.Store

/-- A table content update retains the object's reference type, maximum and
length; every word is either retained or the explicit replacement reference. -/
def TableMutation {M : Type} (before after : runtime.store.Store M)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64) : Prop :=
  ∃ words, after = {before with tables := before.tables.set address.index {object with elements := words}} ∧
    words.length = object.elements.length ∧
    ∀ word ∈ words.val, word ∈ object.elements.val ∨ word = replacement

end Itasca.Runtime.Interp
