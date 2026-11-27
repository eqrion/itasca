import Itasca.Results.Definitions.Representation

namespace Itasca.Representation
open Aeneas Aeneas.Std

/-- Source function signatures use the same address/type relation as the
abstract machine's module typing context. -/
abbrev FunctionsMatch (store : _root_.store) (moduleInst : moduleinst)
    (functions : List functype) : Prop :=
  List.Forall₂ (fun address ty => ∃ fn, store.FUNCS[address]? = some fn ∧ fn.TYPE = ty)
    moduleInst.FUNCS functions


end Itasca.Representation

/-! Internal helper vocabulary used by construction proofs. -/

namespace Itasca.Representation
open Aeneas Aeneas.Std Itasca

/-- Slot encodings are simulation tools; public effects use source values. -/
def encodeValue : val → List Nat
  | .CONST _ (.mk_num__0 _ (.mk_uN bits)) => [bits]
  | .CONST ty (.mk_num__1 _ value) => [WebAssembly.Builtins.floatBits (sizenn ty) value]
  | .VCONST _ (.mk_uN bits) => [bits % 2 ^ 64, bits / 2 ^ 64]
  | .REF_NULL _ => [0]
  | .REF_FUNC_ADDR address | .REF_HOST_ADDR address => [address + 1]

def pairWords (ty : Itasca.wasm_types.ValueType) (pair : U64 × U64) : List Nat :=
  if Itasca.Translation.valueType ty = .V128 then [pair.1.val, pair.2.val] else [pair.1.val]

def offset (types : List valtype) (index : Nat) : Nat := slots (types.take index)

end Itasca.Representation

namespace Itasca.Representation
open Aeneas Aeneas.Std Itasca

def initializerWidth : Itasca.wasm_types.ValueType → U32
  | .V128 => 2#u32
  | _ => 1#u32

end Itasca.Representation

namespace Itasca.Representation
open Aeneas Aeneas.Std Itasca

def compilerStackWidth : Itasca.code.StackType → Nat
  | .Val ty => width (Itasca.Translation.valueType ty)
  | .Bot => 1

end Itasca.Representation

namespace Itasca.Representation
open Aeneas Aeneas.Std Itasca

def stackWords (values : List Itasca.code.StackType) : Nat :=
  (values.map compilerStackWidth).sum

end Itasca.Representation

namespace Itasca.Representation
open Aeneas Aeneas.Std Itasca

def encodeValues (values : List val) : List Nat := values.flatMap encodeValue

end Itasca.Representation

namespace Itasca.Representation
open Aeneas Aeneas.Std Itasca

def instanceItems (i : runtime.store.ModuleInst) : Nat :=
  i.types.length + i.funcs.length + i.tables.length + i.memories.length + i.globals.length +
    i.elems.length + i.datas.length +
    (i.module.module.env.elements.val.map fun e => e.init.length).sum

end Itasca.Representation


/-! Private store shape and compiled-frame accounting used by implementation
proofs. Public store mutations expose source extension and ownership retention. -/
namespace Itasca.Representation
open Aeneas Aeneas.Std Itasca

/-- A conservative source frame budget in 64-bit words: parameter/local storage
plus 1,000 words per encoded instruction-body byte, including the final `end`.
The implementation's 1,000-value signature cap permits at most 500 additional
operand values per byte; each value occupies at most two words. This deliberately
bounds storage rather than estimating the peak of a particular validation run.

Only the independent binary grammar connects bytes to the SpecTec body. No
validator state, reader execution, callback log or compiled slot counter is part
of this requirement. Different permitted encodings can give different sufficient
budgets for the same source body. -/
def SourceFrameCapacity (env : metadata.Env)
    (typeIndex : U32) (source : funccode) (words : Nat) : Prop :=
  ∃ (signature : wasm_types.FuncType) (declared : List wasm_types.ValueType)
      (data : Slice U8) (body : List instr),
    env.types.val[typeIndex.val]? = some signature ∧
    source = .FUNC (.mk_uN typeIndex.val) (declared.map (local.LOCAL ∘ Translation.valueType)) body ∧
    Body.BodyEncoding data body ∧
    words = slots ((signature.params.val ++ declared).map Translation.valueType) + 1000 * data.length


/-- The allocated compiled frame is bounded by the independently described
source frame requirement. This is separate from the emitted-code relation. -/
def CompiledFunctionCapacity (env : metadata.Env)
    (typeIndex : U32) (source : funccode) (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  ∃ words, SourceFrameCapacity env typeIndex source words ∧ compiled.slot_count.val ≤ words


def MemoryShape {M : Type} (view : M → Slice U8) (m : runtime.store.MemInst M) : Prop :=
  (view m.buf).length % 65536 = 0 ∧
  (view m.buf).length / 65536 ≤ 65536 ∧
  ∀ maximum, m.maximum = some maximum →
    (view m.buf).length / 65536 ≤ maximum.val ∧ maximum.val ≤ 65536

def ReferenceShape {M : Type} (s : runtime.store.Store M)
    (ty : Itasca.wasm_types.ElemType) (word : U64) : Prop :=
  word.val = 0 ∨ match ty with
    | .FuncRef => word.val - 1 < s.funcs.length
    | .ExternRef => word.val - 1 < s.externs.length

def GlobalShape {M : Type} (s : runtime.store.Store M) (g : runtime.store.GlobalInst) : Prop :=
  match g.ty.valtype with
  | .I32 | .F32 => g.lo.val < 2^32 ∧ g.hi = 0#u64
  | .I64 | .F64 => g.hi = 0#u64
  | .V128 => True
  | .FuncRef => ReferenceShape s .FuncRef g.lo ∧ g.hi = 0#u64
  | .ExternRef => ReferenceShape s .ExternRef g.lo ∧ g.hi = 0#u64

def TableShape {M : Type} (s : runtime.store.Store M) (t : runtime.store.TableInst) : Prop :=
  t.elements.length ≤ U32.max ∧
  (∀ maximum, t.maximum = some maximum → t.elements.length ≤ maximum.val) ∧
  ∀ word ∈ t.elements.val, ReferenceShape s t.ty word

def InstanceShape {M : Type} (s : runtime.store.Store M) (i : runtime.store.ModuleInst) : Prop :=
  i.types.length = i.module.module.env.types.length ∧
  i.funcs.length = i.module.module.env.func_types.length ∧
  i.tables.length = i.module.module.env.table_types.length ∧
  i.memories.length = i.module.module.env.mem_types.length ∧
  i.globals.length = i.module.module.env.global_types.length ∧
  i.elems.length = i.module.module.env.elements.length ∧
  i.datas.length = i.module.module.tail.data.length ∧
  (∀ index ∈ i.types.val, index.val < s.types.length) ∧
  (∀ address ∈ i.funcs.val, address.store = s.id ∧ address.index.val < s.funcs.length) ∧
  (∀ address ∈ i.tables.val, address.store = s.id ∧ address.index.val < s.tables.length) ∧
  (∀ address ∈ i.memories.val, address.store = s.id ∧ address.index.val < s.memories.length) ∧
  (∀ address ∈ i.globals.val, address.store = s.id ∧ address.index.val < s.globals.length) ∧
  (∀ index ∈ i.elems.val, index.val < s.elems.length) ∧
  (∀ index ∈ i.datas.val, index.val < s.datas.length)

def FunctionShape {M : Type} (s : runtime.store.Store M) (f : runtime.store.FuncInst) : Prop :=
  f.signature.val < s.types.length ∧
  match f.code with
  | .Host _ => True
  | .Wasm inst function =>
    ∃ i, s.instances.val[inst.val]? = some i ∧
      function.val < i.module.module.env.func_type_indices.length


structure Shape {M : Type} (view : M → Slice U8) (s : runtime.store.Store M) : Prop where
  identity : 0 < s.id.val
  functions : ∀ f ∈ s.funcs.val, FunctionShape s f
  memories : ∀ m ∈ s.memories.val, MemoryShape view m
  tables : ∀ t ∈ s.tables.val, TableShape s t
  globals : ∀ g ∈ s.globals.val, GlobalShape s g
  elements : ∀ e ∈ s.elems.val, ∀ word ∈ e.refs.val, ReferenceShape s e.ty word
  instances : ∀ i ∈ s.instances.val, InstanceShape s i
  canonicalTypes : (s.types.val.map Itasca.Translation.Environment.funcType).Nodup
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


/-- Concrete signature tables retain issued addresses and actual canonical
signature lookups. This is metadata correspondence, not execution correctness. -/
def FunctionTable {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (functions : List functype) : Prop :=
  List.Forall₂ (fun address ty => address.store = store.id ∧
    ∃ function signature, store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some signature ∧ Itasca.Translation.Environment.funcType signature = ty)
    inst.funcs.val functions


def TypeEntries {M : Type} (store : runtime.store.Store M) (source : List Itasca.wasm_types.FuncType)
    (indices : List Usize) : Prop :=
  List.Forall₂ (fun ty index => store.types.val[index.val]? = some ty) source indices


/-- Every defined function has a source-derived static frame requirement.
Host functions impose no Wasm frame requirement. -/
def FunctionCapacity {M : Type} (code : CodeInterpretation) (store : runtime.store.Store M)
    (function : runtime.store.FuncInst) : Prop :=
  ∀ instanceIndex functionIndex, function.code = .Wasm instanceIndex functionIndex →
    ∃ inst compiled typeIndex,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      Representation.CompiledFunctionCapacity inst.module.module.env typeIndex
        (code instanceIndex.val inst.module functionIndex.val) compiled ∧
      TypeEntries store inst.module.module.env.types.val inst.types.val ∧
      Representation.FunctionTable store inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType) ∧
      ∃ signature, inst.module.module.env.types.val[typeIndex.val]? = some signature ∧
        store.types.val[function.signature.val]? = some signature

/-- Static source frame bounds for all issued defined functions. -/
def FunctionCapacities {M : Type} (code : CodeInterpretation) (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, FunctionCapacity code store function


end Itasca.Representation
