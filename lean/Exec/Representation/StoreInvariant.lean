import Exec.Representation.Store

/-! Structural store invariants used before attaching the compiler's source-code
certificate. These conditions describe retained objects and accounting; they do
not assert preservation, simulation, or any desired API theorem. -/
namespace Exec.Store
open Aeneas Aeneas.Std

def MemoryShape {M : Type} (view : M → Slice U8) (m : runtime.store.Memory M) : Prop :=
  (view m.buf).length % 65536 = 0 ∧
  (view m.buf).length / 65536 ≤ 65536 ∧
  ∀ maximum, m.maximum = some maximum →
    (view m.buf).length / 65536 ≤ maximum.val ∧ maximum.val ≤ 65536

def ReferenceShape {M : Type} (s : runtime.store.Store M)
    (ty : Itasca.types.ElemType) (word : U64) : Prop :=
  word.val = 0 ∨ match ty with
    | .FuncRef => word.val - 1 < s.funcs.length
    | .ExternRef => word.val - 1 < s.externs.length

def GlobalShape {M : Type} (s : runtime.store.Store M) (g : runtime.store.GlobalInstance) : Prop :=
  match g.ty.valtype with
  | .I32 | .F32 => g.lo.val < 2^32 ∧ g.hi = 0#u64
  | .I64 | .F64 => g.hi = 0#u64
  | .V128 => True
  | .FuncRef => ReferenceShape s .FuncRef g.lo ∧ g.hi = 0#u64
  | .ExternRef => ReferenceShape s .ExternRef g.lo ∧ g.hi = 0#u64

def TableShape {M : Type} (s : runtime.store.Store M) (t : runtime.store.Table) : Prop :=
  t.elements.length ≤ U32.max ∧
  (∀ maximum, t.maximum = some maximum → t.elements.length ≤ maximum.val) ∧
  ∀ word ∈ t.elements.val, ReferenceShape s t.ty word

def InstanceShape {M : Type} (s : runtime.store.Store M) (i : runtime.store.Instance) : Prop :=
  i.types.length = i.module.module.env.types.length ∧
  i.funcs.length = i.module.module.env.func_types.length ∧
  i.tables.length = i.module.module.env.table_types.length ∧
  i.memories.length = i.module.module.env.mem_types.length ∧
  i.globals.length = i.module.module.env.global_types.length ∧
  i.elements.length = i.module.module.env.elements.length ∧
  i.data.length = i.module.module.tail.data.length ∧
  (∀ index ∈ i.types.val, index.val < s.types.length) ∧
  (∀ address ∈ i.funcs.val, address.store = s.id ∧ address.index.val < s.funcs.length) ∧
  (∀ address ∈ i.tables.val, address.store = s.id ∧ address.index.val < s.tables.length) ∧
  (∀ address ∈ i.memories.val, address.store = s.id ∧ address.index.val < s.memories.length) ∧
  (∀ address ∈ i.globals.val, address.store = s.id ∧ address.index.val < s.globals.length) ∧
  (∀ index ∈ i.elements.val, index.val < s.elems.length) ∧
  (∀ index ∈ i.data.val, index.val < s.datas.length)

def FunctionShape {M : Type} (s : runtime.store.Store M) (f : runtime.store.Function) : Prop :=
  f.signature.val < s.types.length ∧
  match f.code with
  | .Host _ => True
  | .Wasm inst function =>
    ∃ i, s.instances.val[inst.val]? = some i ∧
      function.val < i.module.module.env.func_type_indices.length

def instanceItems (i : runtime.store.Instance) : Nat :=
  i.types.length + i.funcs.length + i.tables.length + i.memories.length + i.globals.length +
    i.elements.length + i.data.length +
    (i.module.module.env.elements.val.map fun e => e.init.length).sum

structure Shape {M : Type} (view : M → Slice U8) (s : runtime.store.Store M) : Prop where
  identity : 0 < s.id.val
  functions : ∀ f ∈ s.funcs.val, FunctionShape s f
  memories : ∀ m ∈ s.memories.val, MemoryShape view m
  tables : ∀ t ∈ s.tables.val, TableShape s t
  globals : ∀ g ∈ s.globals.val, GlobalShape s g
  elements : ∀ e ∈ s.elems.val, ∀ word ∈ e.refs.val, ReferenceShape s e.ty word
  instances : ∀ i ∈ s.instances.val, InstanceShape s i
  canonicalTypes : (s.types.val.map decodeFuncType).Nodup
  objectLimit : s.funcs.length + s.types.length + s.tables.length + s.memories.length +
    s.globals.length + s.externs.length ≤ s.limits.max_objects.val
  instanceLimit : s.instances.length ≤ s.limits.max_instances.val
  instanceAccounting : s.instance_items.val = (s.instances.val.map instanceItems).sum
  instanceItemLimit : s.instance_items.val ≤ s.limits.max_instance_items.val
  signatureAccounting : s.signature_values.val =
    (s.types.val.map fun ty => ty.params.length + ty.results.length).sum
  signatureLimit : s.signature_values.val ≤ s.limits.max_signature_values.val
  memoryAccounting : s.memory_bytes.val = (s.memories.val.map fun m => (view m.buf).length).sum
  memoryLimit : s.memory_bytes.val ≤ s.limits.max_memory_bytes.val
  tableAccounting : s.table_elements.val = (s.tables.val.map fun t => t.elements.length).sum
  tableLimit : s.table_elements.val ≤ s.limits.max_table_elements.val

theorem MemoryShape.length_bound {M : Type} {view : M → Slice U8}
    {m : runtime.store.Memory M} (h : MemoryShape view m) :
    (view m.buf).length ≤ 4294967296 := by
  have hdiv := Nat.mod_add_div (view m.buf).length 65536
  rcases h with ⟨halign, hpages, _⟩
  omega

theorem new_shape {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (id : Usize) (limits : runtime.store.StoreLimits)
    (hid : 0 < id.val) :
    runtime.store.Store.with_identity ops id limits ⦃ s => Shape view s ⦄ := by
  simp only [runtime.store.Store.with_identity, WP.spec_ok]
  constructor <;> simp_all [alloc.vec.Vec.new]

/-- Replacing one buffer by another lawful memory preserves the structural
store invariant when the aggregate byte counter is updated consistently. -/
theorem Shape.memory_replace {M : Type} {view : M → Slice U8}
    {s : runtime.store.Store M} (h : Shape view s) (index : Usize)
    (memory : runtime.store.Memory M) (hm : MemoryShape view memory)
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
    (hindex : index.val < s.memories.length) (memory : runtime.store.Memory M)
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
    (table : runtime.store.Table) (ht : TableShape s table)
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
    (global : runtime.store.GlobalInstance) (hg : GlobalShape s global) :
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
    (hindex : index.val < s.tables.length) (table : runtime.store.Table)
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
    (hindex : index.val < s.memories.length) (memory : runtime.store.Memory M)
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
    (hindex : index.val < s.tables.length) (table : runtime.store.Table)
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

end Exec.Store
