import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Initialization.Initializer

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem StagedPrefix.set_fresh_instance {M : Type} {before after : runtime.store.Store M}
    (hprefix : StagedPrefix before after) (index : Usize) (inst : runtime.store.ModuleInst)
    (fresh : before.instances.length ≤ index.val) :
    StagedPrefix before { after with instances := after.instances.set index inst } := by
  constructor
  · exact hprefix.identity
  · exact hprefix.limits
  · exact hprefix.funcs
  · exact hprefix.types
  · exact hprefix.tables
  · exact hprefix.memories
  · exact hprefix.globals
  · simpa [alloc.vec.Vec.set_val_eq, List.take_set_of_le fresh] using hprefix.instances
  · exact hprefix.elems
  · exact hprefix.datas
  · exact hprefix.externs
  · exact hprefix.instanceItems

end Itasca.Runtime.Store
