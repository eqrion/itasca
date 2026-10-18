import Exec.Abs.Ownership.Core
import Exec.Spec.SegmentDrops
import Exec.Abs.Stateful.PayloadTyping
import Exec.Abs.Stateful.CopyStore
import Exec.Abs.Stateful.InitStore
import Exec.Abs.Stateful.MemoryGrow
import Exec.Abs.Stateful.TableGrow
namespace Exec.Abs.Ownership
open SpecExt Exec.Spec Stateful

def ReferencesOwned (bounds : Bounds) (values : List ref) : Prop :=
  ∀ value ∈ values, ValueOwned bounds (val_ref value)

structure StatefulHeapOwned (bounds : Bounds) (s : store) : Prop where
  globals : GlobalsOwned bounds s
  tables : ∀ object ∈ s.TABLES, ReferencesOwned bounds object.REFS
  elements : ∀ object ∈ s.ELEMS, ReferencesOwned bounds object.REFS
  functions : s.FUNCS.length ≤ bounds.functions

structure StatefulOwned (bounds : Bounds) (s : AState) : Prop where
  values : StateOwned bounds s
  heap : StatefulHeapOwned bounds s.store

theorem StatefulOwned.core {bounds s} (owned : StatefulOwned bounds s) : CoreOwned bounds s :=
  ⟨owned.values,owned.heap.globals⟩

theorem ReferencesOwned.modify {bounds values} (owned : ReferencesOwned bounds values)
    (index : Nat) (value : ref) (allowed : ValueOwned bounds (val_ref value)) :
    ReferencesOwned bounds (values.modify index (fun _ => value)) :=
  Segment.forall_modify _ _ _ _ owned (fun _ _ => allowed)

theorem ReferencesOwned.set {bounds values} (owned : ReferencesOwned bounds values)
    (index : Nat) (value : ref) (allowed : ValueOwned bounds (val_ref value)) :
    ReferencesOwned bounds (values.set index value) := by
  intro item member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact owned item member
  · exact allowed

theorem StatefulHeapOwned.metadata {bounds before after} (owned : StatefulHeapOwned bounds before)
    (globals : after.GLOBALS = before.GLOBALS) (tables : after.TABLES = before.TABLES)
    (elements : after.ELEMS = before.ELEMS) (functions : after.FUNCS = before.FUNCS) :
    StatefulHeapOwned bounds after := by
  exact ⟨by simpa only [GlobalsOwned,globals] using owned.globals,
    by simpa only [tables] using owned.tables, by simpa only [elements] using owned.elements,
    by simpa only [functions] using owned.functions⟩

theorem StatefulHeapOwned.table_set {bounds s} (owned : StatefulHeapOwned bounds s)
    (index : Nat) (object : tableinst) (references : ReferencesOwned bounds object.REFS) :
    StatefulHeapOwned bounds {s with TABLES := s.TABLES.set index object} := by
  refine ⟨owned.globals,?_,owned.elements,owned.functions⟩
  intro item member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact owned.tables item member
  · exact references

theorem StatefulHeapOwned.table_write {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index position : Nat) (value : ref) (allowed : ValueOwned bounds (val_ref value)) :
    StatefulHeapOwned bounds (Segment.tableWrite s f index position value) := by
  refine ⟨owned.globals,?_,owned.elements,owned.functions⟩
  apply Segment.forall_modify _ _ _ _ owned.tables
  intro object member
  exact member.modify position value allowed

theorem StatefulHeapOwned.table_fill {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index position : Nat) (value : ref) (count : Nat)
    (allowed : ValueOwned bounds (val_ref value)) :
    StatefulHeapOwned bounds (Segment.tableFill s f index position value count) := by
  induction count generalizing s position with
  | zero => exact owned
  | succ count ih => exact ih (owned.table_write f index position value allowed) (position+1)

theorem StatefulHeapOwned.elem_drop {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index : Nat) : StatefulHeapOwned bounds (droppedElementStore s f index) := by
  refine ⟨owned.globals,owned.tables,?_,owned.functions⟩
  apply Segment.forall_modify _ _ _ _ owned.elements
  intro object member
  simp [ReferencesOwned]

theorem StatefulHeapOwned.memory_fill {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (destination value count : Nat) :
    StatefulHeapOwned bounds (Segment.memoryFill s f destination value count) := by
  induction count generalizing s destination with
  | zero => exact owned
  | succ count ih =>
    exact ih (s := Segment.memoryWrite s f destination (Segment.fillByte value)) (owned.metadata rfl rfl rfl rfl) (Segment.next32 destination)

theorem StatefulHeapOwned.table_grow {bounds s} (owned : StatefulHeapOwned bounds s)
    (index : Nat) (object fresh : tableinst) (count : Nat) (value : ref)
    (member : object ∈ s.TABLES) (allowed : ValueOwned bounds (val_ref value))
    (growth : fun_growtable object count value (some fresh)) :
    StatefulHeapOwned bounds {s with TABLES := s.TABLES.set index fresh} := by
  apply owned.table_set
  cases growth with
  | fun_growtable_case_0 _ minimum maximum type refs count source size limit target freshWf oldWf targetWf =>
    subst object
    subst fresh
    have before := owned.tables _ member
    simp only [ReferencesOwned,List.mem_append,List.mem_replicate] at *
    intro reference present
    rcases present with previous | ⟨_,rfl⟩
    · exact before reference previous
    · exact allowed

theorem StatefulHeapOwned.table_init {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index elementIndex address destination source count : Nat) (object : eleminst)
    (mapped : f.MODULE.ELEMS[elementIndex]? = some address) (found : s.ELEMS[address]? = some object)
    (inside : source+count ≤ object.REFS.length) :
    StatefulHeapOwned bounds (Segment.tableInit s f index elementIndex destination source count) := by
  rw [Segment.tableInit_eq]
  refine ⟨owned.globals,?_,owned.elements,owned.functions⟩
  apply Segment.forall_modify _ _ _ _ owned.tables
  intro table before
  have exactSource : fun_elem ⟨s,f⟩ (.mk_uN elementIndex) = object := by
    simp [fun_elem,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
  dsimp only
  rw [exactSource]
  exact copyInto_forall _ _ _ _ _ _ before (owned.elements object (List.mem_of_getElem? found)) inside

theorem StatefulHeapOwned.table_copy {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index sourceIndex address sourceAddress destination source count : Nat)
    (object sourceObject : tableinst)
    (mapped : f.MODULE.TABLES[index]? = some address) (sourceMapped : f.MODULE.TABLES[sourceIndex]? = some sourceAddress)
    (found : s.TABLES[address]? = some object) (sourceFound : s.TABLES[sourceAddress]? = some sourceObject)
    (inside : source+count ≤ sourceObject.REFS.length ∧ destination+count ≤ object.REFS.length) :
    StatefulHeapOwned bounds (Segment.tableCopy s f index sourceIndex destination source count) := by
  simp only [Segment.tableCopy,List.getElem!_eq_getElem?_getD,mapped,sourceMapped,found,sourceFound,Option.getD_some]
  rw [←Segment.copyInto_eq_setSlice object.REFS sourceObject.REFS destination source count inside.1 inside.2]
  apply owned.table_set
  exact copyInto_forall _ _ _ _ _ _ (owned.tables object (List.mem_of_getElem? found))
    (owned.tables sourceObject (List.mem_of_getElem? sourceFound)) inside.1

theorem StatefulHeapOwned.memory_init {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index destination source count : Nat) :
    StatefulHeapOwned bounds (Segment.memoryInit s f index destination source count) := by
  induction count generalizing s destination source with
  | zero => exact owned
  | succ count ih =>
    apply ih
    exact owned.metadata rfl rfl rfl rfl

theorem StatefulHeapOwned.memory_copy {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (destination source count : Nat) :
    StatefulHeapOwned bounds (Segment.memoryCopy s f destination source count) :=
  owned.metadata rfl rfl rfl rfl

theorem StatefulHeapOwned.data_drop {bounds s} (owned : StatefulHeapOwned bounds s)
    (f : frame) (index : Nat) : StatefulHeapOwned bounds (droppedDataStore s f index) :=
  owned.metadata rfl rfl rfl rfl

end Exec.Abs.Ownership
