import Exec.Store.Api.Write
import Exec.Store.Invariant.ValueDecode

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem decodeStore_global_update {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (globals : alloc.vec.Vec runtime.store.GlobalInst) :
    decodeStore view code {s with globals} =
      {decodeStore view code s with GLOBALS := globals.val.map decodeGlobal} := by rfl

theorem decodeStore_table_update {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (tables : alloc.vec.Vec runtime.store.TableInst) :
    decodeStore view code {s with tables} =
      {decodeStore view code s with TABLES := tables.val.map decodeTable} := by rfl

end Itasca.Runtime.Store
