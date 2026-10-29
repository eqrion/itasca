import Itasca.Runtime.Interp.Relations.FrameBindings
import Itasca.Runtime.Representation.FunctionTable
import Itasca.Runtime.Interp.Relations.FrameStack
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.SourceMachine.PureHead

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A frame's retained signature list belongs to its actual instance. -/
theorem FrameProgram.function_table {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions}
    (program : FrameProgram store raw compiled locals results functions)
    (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst) :
    FunctionTable store inst functions := by
  obtain ⟨actual, found, _, table⟩ := program.lookup
  have same : actual = inst := Option.some.inj (found.symm.trans lookup)
  exact same ▸ table

/-- Resolving a compiler CALL signature exposes the exact issued raw address,
function entry, and canonical signature consumed by interpreter dispatch. -/
theorem FrameProgram.resolve_call {M : Type} {store : runtime.store.Store M}
    {raw compiled locals results functions}
    (program : FrameProgram store raw compiled locals results functions)
    (inst : runtime.store.ModuleInst)
    (lookup : store.instances.val[raw.instance.val]? = some inst)
    (index : Nat) (ty : functype) (signature : functions[index]? = some ty) :
    ∃ address function rawType, inst.funcs.val[index]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some rawType ∧ Store.decodeFuncType rawType = ty :=
  (program.function_table inst lookup).resolve index ty signature

end Itasca.Runtime.Interp
