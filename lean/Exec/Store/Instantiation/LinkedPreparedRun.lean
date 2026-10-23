import Exec.Store.Instantiation.PreparedRun
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Empty address maps before linking the supplied external values. -/
def emptyInstance (module : runtime.compiler.ExecutableModule) : runtime.store.ModuleInst := {
  module := module, types := alloc.vec.Vec.new Usize,
  funcs := alloc.vec.Vec.new runtime.FuncAddr, tables := alloc.vec.Vec.new runtime.TableAddr,
  memories := alloc.vec.Vec.new runtime.MemoryAddr, globals := alloc.vec.Vec.new runtime.GlobalAddr,
  elems := alloc.vec.Vec.new Usize, datas := alloc.vec.Vec.new Usize }

/-- Preparation additionally retains the actual import-linking computation.
The supplied externals remain the caller's exact list, rather than an inferred
list satisfying only the final module's import types. -/
structure LinkedPreparedRun {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (platform : P) (ready : runtime.store.Store M)
    extends PreparedRun memory hooks floats allocator view before module platform ready where
  importsLength : imports.length = module.module.env.imports.length
  linkRun : runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
    (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Ok (), seed)
end Exec.Store
