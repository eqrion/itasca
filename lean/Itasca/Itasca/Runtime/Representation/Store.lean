import Itasca.Runtime.Representation.Definitions
import Itasca.Runtime.Representation.Values
import Itasca.Body.LoopDispatch
import Itasca.CodeEntry.Encoding
import Itasca.Runtime.Equations.Bytecode
import ItascaRust.Funs
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.SourceMachine.Preservation
import Itasca.Binary.ModuleUnique

open WebAssembly

/-! ## Store -/

section

/-! Concrete store decoding. `CodeInterpretation` supplies source function bodies
which are not retained in the compiled Rust module. Compilation constructs this
interpretation and its code relation; this parameter contains no execution
correctness assumption. The first index names the retained instance, so equal
compiled modules can carry distinct source certificates. All other objects decode directly from retained data. -/
namespace Itasca.Representation
open Aeneas Aeneas.Std

/-- Replacing the concrete memory vector changes only the decoded memory
component; function and module decoding do not depend on its opaque buffers. -/
theorem decode_store_memory_update {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (memories : alloc.vec.Vec (runtime.store.MemInst M)) :
    decodeStore view code {s with memories := memories} =
      {decodeStore view code s with MEMS := memories.val.map (decodeMemory view)} := by
  rfl

end Itasca.Representation

end

/-! ## StoreInvariant -/

section

/-! Structural store invariants used before attaching the compiler's source-code
certificate. These conditions describe retained objects and accounting; they do
not assert preservation, simulation, or any desired API theorem. -/
namespace Itasca.Representation
open Aeneas Aeneas.Std

theorem MemoryShape.length_bound {M : Type} {view : M → Slice U8}
    {m : runtime.store.MemInst M} (h : MemoryShape view m) :
    (view m.buf).length ≤ 4294967296 := by
  have hdiv := Nat.mod_add_div (view m.buf).length 65536
  rcases h with ⟨halign, hpages, _⟩
  omega

/-- Replacing one buffer by another lawful memory preserves the structural
store invariant when the aggregate byte counter is updated consistently. -/
theorem Shape.memory_replace {M : Type} {view : M → Slice U8}
    {s : runtime.store.Store M} (h : Shape view s) (index : Usize)
    (memory : runtime.store.MemInst M) (hm : MemoryShape view memory)
    (total : Usize)
    (hcount : total.val = ((s.memories.set index memory).val.map fun m => (view m.buf).length).sum)
    (hlimit : total.val ≤ s.limits.max_memory_bytes.val) :
    Shape view {s with memories := s.memories.set index memory, memory_bytes := total} where
  identity := h.identity
  functions := by simpa [FunctionShape] using h.functions
  memories := by
    intro m hmember
    simp only [alloc.vec.Vec.set_val_eq] at hmember
    rcases List.mem_or_eq_of_mem_set hmember with hold | heq
    · exact h.memories m hold
    · subst m; exact hm
  tables := by simpa [TableShape, ReferenceShape] using h.tables
  globals := by simpa [GlobalShape, ReferenceShape] using h.globals
  elements := by simpa [ReferenceShape] using h.elements
  instances := by simpa [InstanceShape] using h.instances
  canonicalTypes := h.canonicalTypes
  objectLimit := by simpa using h.objectLimit
  instanceLimit := h.instanceLimit
  instanceAccounting := h.instanceAccounting
  instanceItemLimit := h.instanceItemLimit
  signatureAccounting := h.signatureAccounting
  signatureLimit := h.signatureLimit
  memoryAccounting := hcount
  memoryLimit := hlimit
  tableAccounting := h.tableAccounting
  tableLimit := h.tableLimit

theorem Shape.memory_replace_same_length {M : Type} {view : M → Slice U8}
    {s : runtime.store.Store M} (h : Shape view s) (index : Usize)
    (hindex : index.val < s.memories.length) (memory : runtime.store.MemInst M)
    (hlen : (view memory.buf).length = (view (s.memories.val[index.val]).buf).length)
    (hmax : memory.maximum = (s.memories.val[index.val]).maximum) :
    Shape view {s with memories := s.memories.set index memory} := by
  have hm : MemoryShape view memory := by
    have hold := h.memories (s.memories.val[index.val]) (by simp)
    simpa only [MemoryShape, hlen, hmax] using hold
  apply h.memory_replace index memory hm s.memory_bytes ?_ h.memoryLimit
  rw [h.memoryAccounting, alloc.vec.Vec.set_val_eq, List.map_set, hlen]
  have hs := List.set_getElem_self («as» := s.memories.val.map fun m => (view m.buf).length)
    (i := index.val) (by simpa using hindex)
  simpa using (congrArg List.sum hs).symm

/-- Replacing one table by another lawful table preserves the structural
store invariant when the aggregate element counter is updated consistently. -/
theorem Shape.table_replace {M : Type} {view : M → Slice U8}
    {s : runtime.store.Store M} (h : Shape view s) (index : Usize)
    (table : runtime.store.TableInst) (ht : TableShape s table)
    (total : Usize)
    (hcount : total.val = ((s.tables.set index table).val.map fun t => t.elements.length).sum)
    (hlimit : total.val ≤ s.limits.max_table_elements.val) :
    Shape view {s with tables := s.tables.set index table, table_elements := total} where
  identity := h.identity
  functions := by simpa [FunctionShape] using h.functions
  memories := h.memories
  tables := by
    intro t hmember
    simp only [alloc.vec.Vec.set_val_eq] at hmember
    rcases List.mem_or_eq_of_mem_set hmember with hold | heq
    · simpa [TableShape, ReferenceShape] using h.tables t hold
    · subst t; simpa [TableShape, ReferenceShape] using ht
  globals := by simpa [GlobalShape, ReferenceShape] using h.globals
  elements := by simpa [ReferenceShape] using h.elements
  instances := by simpa [InstanceShape] using h.instances
  canonicalTypes := h.canonicalTypes
  objectLimit := by simpa using h.objectLimit
  instanceLimit := h.instanceLimit
  instanceAccounting := h.instanceAccounting
  instanceItemLimit := h.instanceItemLimit
  signatureAccounting := h.signatureAccounting
  signatureLimit := h.signatureLimit
  memoryAccounting := h.memoryAccounting
  memoryLimit := h.memoryLimit
  tableAccounting := hcount
  tableLimit := hlimit

/-- Replacing a global by a canonical value preserves structural validity. -/
theorem Shape.global_replace {M : Type} {view : M → Slice U8}
    {s : runtime.store.Store M} (h : Shape view s) (index : Usize)
    (global : runtime.store.GlobalInst) (hg : GlobalShape s global) :
    Shape view {s with globals := s.globals.set index global} where
  identity := h.identity
  functions := by simpa [FunctionShape] using h.functions
  memories := h.memories
  tables := by simpa [TableShape, ReferenceShape] using h.tables
  globals := by
    intro g hmember
    simp only [alloc.vec.Vec.set_val_eq] at hmember
    rcases List.mem_or_eq_of_mem_set hmember with hold | heq
    · simpa [GlobalShape, ReferenceShape] using h.globals g hold
    · subst g; simpa [GlobalShape, ReferenceShape] using hg
  elements := by simpa [ReferenceShape] using h.elements
  instances := by simpa [InstanceShape] using h.instances
  canonicalTypes := h.canonicalTypes
  objectLimit := by simpa using h.objectLimit
  instanceLimit := h.instanceLimit
  instanceAccounting := h.instanceAccounting
  instanceItemLimit := h.instanceItemLimit
  signatureAccounting := h.signatureAccounting
  signatureLimit := h.signatureLimit
  memoryAccounting := h.memoryAccounting
  memoryLimit := h.memoryLimit
  tableAccounting := h.tableAccounting
  tableLimit := h.tableLimit

theorem Shape.table_replace_same_length {M : Type} {view : M → Slice U8}
    {s : runtime.store.Store M} (h : Shape view s) (index : Usize)
    (hindex : index.val < s.tables.length) (table : runtime.store.TableInst)
    (ht : TableShape s table)
    (hlen : table.elements.length = (s.tables.val[index.val]).elements.length) :
    Shape view {s with tables := s.tables.set index table} := by
  apply h.table_replace index table ht s.table_elements ?_ h.tableLimit
  rw [h.tableAccounting, alloc.vec.Vec.set_val_eq, List.map_set, hlen]
  have hs := List.set_getElem_self («as» := s.tables.val.map fun t => t.elements.length)
    (i := index.val) (by simpa using hindex)
  simpa using (congrArg List.sum hs).symm

/-- Updating one nonnegative accounting contribution by an increment updates
its aggregate by exactly that increment. -/
theorem sum_set_add (values : List Nat) (index extra : Nat) (hi : index < values.length) :
    (values.set index (values[index] + extra)).sum = values.sum + extra := by
  induction values generalizing index with
  | nil => simp at hi
  | cons head tail ih =>
    cases index with
    | zero => simp; omega
    | succ index =>
      have hindex : index < tail.length := by simpa using hi
      simpa [List.sum_cons, Nat.add_assoc] using congrArg (head + ·) (ih index hindex)

theorem Shape.memory_extend {M : Type} {view : M → Slice U8}
    {s : runtime.store.Store M} (h : Shape view s) (index : Usize)
    (hindex : index.val < s.memories.length) (memory : runtime.store.MemInst M)
    (hm : MemoryShape view memory) (extra : Nat)
    (hlen : (view memory.buf).length = (view (s.memories.val[index.val]).buf).length + extra)
    (total : Usize) (hcount : total.val = s.memory_bytes.val + extra)
    (hlimit : total.val ≤ s.limits.max_memory_bytes.val) :
    Shape view {s with memories := s.memories.set index memory, memory_bytes := total} := by
  apply h.memory_replace index memory hm total ?_ hlimit
  rw [hcount, h.memoryAccounting, alloc.vec.Vec.set_val_eq, List.map_set, hlen]
  have hs := sum_set_add (s.memories.val.map fun m => (view m.buf).length) index.val extra
    (by simpa using hindex)
  simpa using hs.symm

theorem Shape.table_extend {M : Type} {view : M → Slice U8}
    {s : runtime.store.Store M} (h : Shape view s) (index : Usize)
    (hindex : index.val < s.tables.length) (table : runtime.store.TableInst)
    (hm : TableShape s table) (extra : Nat)
    (hlen : table.elements.length = (s.tables.val[index.val]).elements.length + extra)
    (total : Usize) (hcount : total.val = s.table_elements.val + extra)
    (hlimit : total.val ≤ s.limits.max_table_elements.val) :
    Shape view {s with tables := s.tables.set index table, table_elements := total} := by
  apply h.table_replace index table hm total ?_ hlimit
  rw [hcount, h.tableAccounting, alloc.vec.Vec.set_val_eq, List.map_set, hlen]
  have hs := sum_set_add (s.tables.val.map fun t => t.elements.length) index.val extra
    (by simpa using hindex)
  simpa using hs.symm

end Itasca.Representation

end

/-! ## FunctionTable -/

section

/-!
Correspondence between issued runtime functions and their source interpretation. Lookup and resolution certificates are shared by frame-stack and capacity proofs.
-/

namespace Itasca.Representation
open Aeneas Aeneas.Std

theorem FunctionTable.resolve {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {functions : List functype}
    (table : FunctionTable store inst functions) (index : Nat) (ty : functype)
    (signature : functions[index]? = some ty) :
    ∃ address function rawType, inst.funcs.val[index]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some rawType ∧ Itasca.Translation.Environment.funcType rawType = ty := by
  have within : index < functions.length := (List.getElem?_eq_some_iff.mp signature).1
  have addressBound : index < inst.funcs.val.length := by rw [table.length_eq]; exact within
  have related :=  table.get addressBound within
  obtain ⟨owned, function, rawType, found, typed, decoded⟩ := related
  have actualType : functions[index] = ty := by simpa only [List.getElem?_eq_getElem within, Option.some.injEq] using signature
  exact ⟨inst.funcs.val[index], function, rawType, List.getElem?_eq_getElem addressBound,
    owned, found, typed, decoded.trans actualType⟩

private theorem decode_function_type {M : Type} (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.FuncInst) (signature : Itasca.wasm_types.FuncType)
    (lookup : store.types.val[function.signature.val]? = some signature) :
    (Representation.decodeFunction code store function).TYPE = Itasca.Translation.Environment.funcType signature := by
  unfold Representation.decodeFunction
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, lookup, Option.map_some, Option.getD_some]
  cases function.code with
  | Host id => rfl
  | Wasm inst fn => dsimp only; split <;> rfl

/-- The concrete table produces the source module-binding relation exactly. -/
theorem FunctionTable.source {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {functions : List functype}
    (table : FunctionTable store inst functions) (view : M → Slice U8)
    (code : Representation.CodeInterpretation) :
    FunctionsMatch (Representation.decodeStore view code store) (Representation.decodeInstance store inst) functions := by
  change List.Forall₂ _ (inst.funcs.val.map (fun a => a.index.val)) functions
  unfold FunctionTable at table
  generalize addressesEq : inst.funcs.val = addresses at table ⊢
  clear addressesEq
  induction table with
  | nil => exact .nil
  | @cons address ty addresses types matching tail ih =>
    apply List.Forall₂.cons _ ih
    obtain ⟨_, function, signature, found, typed, decoded⟩ := matching
    refine ⟨Representation.decodeFunction code store function, ?_, (decode_function_type code store function signature typed).trans decoded⟩
    simp only [Representation.decodeStore, List.getElem?_map, found, Option.map_some]

end Itasca.Representation

end

/-! ## StoreCapacity -/

section

/-!
Source frame capacities for issued functions and decoded store signatures. Interpreter resource causes and store invariants share these certificates.
-/

namespace Itasca.Representation
open Aeneas Aeneas.Std

/-- Canonical type indices decode to exactly the source validation table. -/
theorem TypeEntries.capacity_decode {M : Type} {store : runtime.store.Store M}
    {source : List Itasca.wasm_types.FuncType} {indices : List Usize}
    (entries : TypeEntries store source indices) :
    indices.map (fun index => (store.types.val.map Itasca.Translation.Environment.funcType).getD index.val default) =
      source.map Itasca.Translation.Environment.funcType := by
  induction entries with
  | nil => rfl
  | @cons ty index types indices found rest ih =>
    simp only [List.map_cons]
    rw [ih]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, found, Option.map_some, Option.getD_some]

end Itasca.Representation

end
