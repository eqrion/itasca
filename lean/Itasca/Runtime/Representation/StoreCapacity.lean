import Itasca.Runtime.Representation.Values
import Itasca.Wasm2.Invariant
import Itasca.Profile.CodeEntry
import Itasca.Runtime.Equations
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Binary.UnicodeUnique

/-!
Sections, each formerly its own module: ValidatedStacks, FunctionCapacity, Store, StoreInvariant, FunctionTable, TypeEntries, NameSource, StoreCapacity.
-/

/-! ## ValidatedStacks -/

section

/-!
Independent validated source stacks and their maximum slot demand. Function-capacity certificates and compiler folds share this source-only bound.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A source-only successful validation trace, recording every operand stack.
Its reader equations use the empty visitor, independently of compiled code. -/
inductive ValidatedStacksWasm2 (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) : code.BodyState → List (List code.StackType) → Prop where
  | done {st} (typed : Wasm2.State data env ctx.locals index st)
      (closed : st.blocks.val = []) (finished : st.core.pos = Slice.len data) :
      ValidatedStacksWasm2 data env ctx index st [st.core.vals.val]
  | step {st next out samples}
      (typed : Wasm2.State data env ctx.locals index st)
      (pending : Wasm2.Pending data env ctx.locals index {core := {st.core with pos := next}})
      (start : pending.start = st.core.pos) (advance : next.val = st.core.pos.val + 1)
      (read : code.step_profile code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        {core := {st.core with pos := next}} data env ctx index
        (data.val[pending.start.val]'pending.inbounds) () = .ok (.Ok (), out, ()))
      (rest : ValidatedStacksWasm2 data env ctx index out samples) :
      ValidatedStacksWasm2 data env ctx index st (st.core.vals.val :: samples)

/-- Maximum word width of the actual validated operand samples, including
unreachable source positions. Scalars/references use one word and vectors two. -/
def maximumStackWords (samples : List (List code.StackType)) : Nat :=
  samples.foldr (fun stack bound => max (stackWords stack) bound) 0

end Itasca.Runtime.Compiler

end

/-! ## FunctionCapacity -/

section

/-!
Independent source frame demand and compiled-function capacity certificates. The compiler establishes these bounds and store capacity proofs retain them.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A source frame's word requirement: its parameter/local words plus the
maximum operand width in a complete canonical validation trace. The reader
trace uses the empty visitor and contains no compiled-code premise. -/
def SourceFrameCapacity (env : metadata.Env)
    (typeIndex : U32) (source : funccode) (words : Nat) : Prop :=
  ∃ (signature : wasm_types.FuncType) (declared : List wasm_types.ValueType)
      (data : Slice U8) (ctx : code.Context) (body : List instr)
      (samples : List (List code.StackType)),
    env.types.val[typeIndex.val]? = some signature ∧
    source = .FUNC (.mk_uN typeIndex.val) (declared.map (local.LOCAL ∘ Translate.valueType)) body ∧
    ctx.locals.val = signature.params.val ++ declared ∧
    ctx.results.val = signature.results.val ∧
    Profile.BodyEncoding data body ∧
    ValidatedStacksWasm2 data env ctx typeIndex (Wasm2.initial typeIndex) samples ∧
    words = slots ((signature.params.val ++ declared).map Translate.valueType) + maximumStackWords samples

/-- The allocated compiled frame is bounded by the independently described
source frame requirement. This is separate from the emitted-code relation. -/
def FunctionCapacity (env : metadata.Env)
    (typeIndex : U32) (source : funccode) (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  ∃ words, SourceFrameCapacity env typeIndex source words ∧ compiled.slot_count.val ≤ words

end Itasca.Runtime.Compiler

end

/-! ## Store -/

section

/-! Concrete store decoding. `CodeInterpretation` supplies source function bodies
which are not retained in the compiled Rust module. Compilation constructs this
interpretation and its code relation; this parameter contains no execution
correctness assumption. The first index names the retained instance, so equal
compiled modules can carry distinct source certificates. All other objects decode directly from retained data. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev CodeInterpretation := Nat → runtime.compiler.ExecutableModule → Nat → funccode

def decodeFuncType (ty : Itasca.wasm_types.FuncType) : functype :=
  .mk_functype (.mk_list (ty.params.val.map Interp.sourceType)) (.mk_list (ty.results.val.map Interp.sourceType))

def decodeElemType : Itasca.wasm_types.ElemType → reftype
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

def decodeMut : Itasca.wasm_types.Mut → «mut»
  | .Const => none
  | .Var => some .MUT

def decodeLimits (length : Nat) (maximum : Option U32) : limits :=
  .mk_limits (.mk_uN length) (maximum.map fun n => .mk_uN n.val)

def decodeRef (ty : Itasca.wasm_types.ElemType) (word : U64) : ref :=
  if word.val = 0 then .REF_NULL (decodeElemType ty)
  else match ty with
    | .FuncRef => .REF_FUNC_ADDR (word.val - 1)
    | .ExternRef => .REF_HOST_ADDR (word.val - 1)

def refVal : ref → val
  | .REF_NULL ty => .REF_NULL ty
  | .REF_FUNC_ADDR address => .REF_FUNC_ADDR address
  | .REF_HOST_ADDR address => .REF_HOST_ADDR address

def decodeWords (ty : Itasca.wasm_types.ValueType) (lo hi : U64) : val :=
  match ty with
  | .I32 => .CONST .I32 (.mk_num__0 .I32 (.mk_uN (lo.val % 2^32)))
  | .I64 => .CONST .I64 (.mk_num__0 .I64 (.mk_uN lo.val))
  | .F32 => .CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 (lo.val % 2^32)))
  | .F64 => .CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 lo.val))
  | .V128 => .VCONST .V128 (.mk_uN (lo.val + hi.val * 2^64))
  | .FuncRef => refVal (decodeRef .FuncRef lo)
  | .ExternRef => refVal (decodeRef .ExternRef lo)

def decodeGlobal (g : runtime.store.GlobalInst) : globalinst :=
  ⟨.mk_globaltype (decodeMut g.ty.mutability) (Interp.sourceType g.ty.valtype),
    decodeWords g.ty.valtype g.lo g.hi⟩

def decodeTable (t : runtime.store.TableInst) : tableinst :=
  ⟨.mk_tabletype (decodeLimits t.elements.length t.maximum) (decodeElemType t.ty),
    t.elements.val.map (decodeRef t.ty)⟩

def decodeBytes (bytes : List U8) : List byte := bytes.map fun b => .mk_byte b.val

def decodeMemory {M : Type} (view : M → Slice U8) (m : runtime.store.MemInst M) : meminst :=
  ⟨.PAGE (decodeLimits ((view m.buf).length / 65536) m.maximum), decodeBytes (view m.buf).val⟩

def decodeElement (e : runtime.store.ElemInst) : eleminst :=
  ⟨decodeElemType e.ty, e.refs.val.map (decodeRef e.ty)⟩

def decodeData (d : runtime.store.DataInst) : datainst := ⟨decodeBytes d.bytes.val⟩

def decodeNameChars : List U8 → List char
  | [] => []
  | a :: rest =>
      if a.val < 128 then .mk_char a.val :: decodeNameChars rest
      else match rest with
        | [] => []
        | b :: rest =>
            if a.val < 224 then .mk_char (64 * (a.val - 192) + (b.val - 128)) :: decodeNameChars rest
            else match rest with
              | [] => []
              | c :: rest =>
                  if a.val < 240 then
                    .mk_char (4096 * (a.val - 224) + 64 * (b.val - 128) + (c.val - 128)) :: decodeNameChars rest
                  else match rest with
                    | [] => []
                    | d :: rest =>
                        .mk_char (262144 * (a.val - 240) + 4096 * (b.val - 128) +
                          64 * (c.val - 128) + (d.val - 128)) :: decodeNameChars rest

def decodeName (bytes : List U8) : «name» := .mk_name (decodeNameChars bytes)

def decodeExport (inst : runtime.store.ModuleInst) (e : Itasca.metadata.Export) : exportinst :=
  ⟨decodeName e.name.val, match e.desc with
    | .Func i => .FUNC ((inst.funcs.val.map fun a => a.index.val).getD i.val 0)
    | .Table i => .TABLE ((inst.tables.val.map fun a => a.index.val).getD i.val 0)
    | .Memory i => .MEM ((inst.memories.val.map fun a => a.index.val).getD i.val 0)
    | .Global i => .GLOBAL ((inst.globals.val.map fun a => a.index.val).getD i.val 0)⟩

def decodeInstance {M : Type} (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) : moduleinst :=
  ⟨inst.types.val.map (fun i => (s.types.val.map decodeFuncType).getD i.val default),
    inst.funcs.val.map (fun a => a.index.val), inst.globals.val.map (fun a => a.index.val),
    inst.tables.val.map (fun a => a.index.val), inst.memories.val.map (fun a => a.index.val),
    inst.elems.val.map UScalar.val, inst.datas.val.map UScalar.val,
    inst.module.module.env.exports.val.map (decodeExport inst)⟩

def decodeFunction {M : Type} (code : CodeInterpretation) (s : runtime.store.Store M)
    (f : runtime.store.FuncInst) : funcinst :=
  let ty := (s.types.val.map decodeFuncType).getD f.signature.val default
  match f.code with
  | .Host id => ⟨ty, default, .HOST id.val⟩
  | .Wasm instIndex fn =>
    match s.instances.val[instIndex.val]? with
    | some inst => ⟨ty, decodeInstance s inst, code instIndex.val inst.module fn.val⟩
    | none => ⟨ty, default, .HOST 0⟩

def decodeStore {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) : _root_.store :=
  ⟨s.funcs.val.map (decodeFunction code s), s.globals.val.map decodeGlobal,
    s.tables.val.map decodeTable, s.memories.val.map (decodeMemory view),
    s.elems.val.map decodeElement, s.datas.val.map decodeData⟩

/-- Replacing the concrete memory vector changes only the decoded memory
component; function and module decoding do not depend on its opaque buffers. -/
theorem decode_store_memory_update {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (memories : alloc.vec.Vec (runtime.store.MemInst M)) :
    decodeStore view code {s with memories := memories} =
      {decodeStore view code s with MEMS := memories.val.map (decodeMemory view)} := by
  rfl

end Itasca.Runtime.Store

end

/-! ## StoreInvariant -/

section

/-! Structural store invariants used before attaching the compiler's source-code
certificate. These conditions describe retained objects and accounting; they do
not assert preservation, simulation, or any desired API theorem. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

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

def instanceItems (i : runtime.store.ModuleInst) : Nat :=
  i.types.length + i.funcs.length + i.tables.length + i.memories.length + i.globals.length +
    i.elems.length + i.datas.length +
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

end Itasca.Runtime.Store

end

/-! ## FunctionTable -/

section

/-!
Correspondence between issued runtime functions and their source interpretation. Lookup and resolution certificates are shared by frame-stack and capacity proofs.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Source function signatures use the same address/type relation as the
abstract machine's module typing context. -/
abbrev FunctionsMatch (store : _root_.store) (moduleInst : moduleinst)
    (functions : List functype) : Prop :=
  List.Forall₂ (fun address ty => ∃ fn, store.FUNCS[address]? = some fn ∧ fn.TYPE = ty)
    moduleInst.FUNCS functions

/-- Concrete signature tables retain issued addresses and actual canonical
signature lookups. This is metadata correspondence, not execution correctness. -/
def FunctionTable {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (functions : List functype) : Prop :=
  List.Forall₂ (fun address ty => address.store = store.id ∧
    ∃ function signature, store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some signature ∧ Store.decodeFuncType signature = ty)
    inst.funcs.val functions

theorem FunctionTable.resolve {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {functions : List functype}
    (table : FunctionTable store inst functions) (index : Nat) (ty : functype)
    (signature : functions[index]? = some ty) :
    ∃ address function rawType, inst.funcs.val[index]? = some address ∧
      address.store = store.id ∧ store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some rawType ∧ Store.decodeFuncType rawType = ty := by
  have within : index < functions.length := (List.getElem?_eq_some_iff.mp signature).1
  have addressBound : index < inst.funcs.val.length := by rw [table.length_eq]; exact within
  have related :=  table.get addressBound within
  obtain ⟨owned, function, rawType, found, typed, decoded⟩ := related
  have actualType : functions[index] = ty := by simpa only [List.getElem?_eq_getElem within, Option.some.injEq] using signature
  exact ⟨inst.funcs.val[index], function, rawType, List.getElem?_eq_getElem addressBound,
    owned, found, typed, decoded.trans actualType⟩

private theorem decode_function_type {M : Type} (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (function : runtime.store.FuncInst) (signature : Itasca.wasm_types.FuncType)
    (lookup : store.types.val[function.signature.val]? = some signature) :
    (Store.decodeFunction code store function).TYPE = Store.decodeFuncType signature := by
  unfold Store.decodeFunction
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, lookup, Option.map_some, Option.getD_some]
  cases function.code with
  | Host id => rfl
  | Wasm inst fn => dsimp only; split <;> rfl

/-- The concrete table produces the source module-binding relation exactly. -/
theorem FunctionTable.source {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {functions : List functype}
    (table : FunctionTable store inst functions) (view : M → Slice U8)
    (code : Store.CodeInterpretation) :
    FunctionsMatch (Store.decodeStore view code store) (Store.decodeInstance store inst) functions := by
  change List.Forall₂ _ (inst.funcs.val.map (fun a => a.index.val)) functions
  unfold FunctionTable at table
  generalize addressesEq : inst.funcs.val = addresses at table ⊢
  clear addressesEq
  induction table with
  | nil => exact .nil
  | @cons address ty addresses types matching tail ih =>
    apply List.Forall₂.cons _ ih
    obtain ⟨_, function, signature, found, typed, decoded⟩ := matching
    refine ⟨Store.decodeFunction code store function, ?_, (decode_function_type code store function signature typed).trans decoded⟩
    simp only [Store.decodeStore, List.getElem?_map, found, Option.map_some]

end Itasca.Runtime.Interp

end

/-! ## TypeEntries -/

section

/-!
Retained type-entry certificates for runtime stores. Store staging and source-capacity proofs consume the same independent signature evidence.
-/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

def TypeEntries {M : Type} (store : runtime.store.Store M) (source : List Itasca.wasm_types.FuncType)
    (indices : List Usize) : Prop :=
  List.Forall₂ (fun ty index => store.types.val[index.val]? = some ty) source indices

end Itasca.Runtime.Store

end

/-! ## NameSource -/

section

/-! Store names use the same independent Unicode decoding as the source grammar. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

theorem decode_name_chars_source (bytes : List U8) :
    decodeNameChars bytes = ModuleBinary.decodeChars bytes := by
  induction bytes using decodeNameChars.induct <;>
    (try simp only [decodeNameChars, ModuleBinary.decodeChars]) <;>
    (try simp_all only [ite_false])
  all_goals
    unfold decodeNameChars ModuleBinary.decodeChars
    simp_all only [ite_true, ite_false]

theorem decode_name_source (bytes : List U8) :
    decodeName bytes = ModuleBinary.nameOfBytes bytes := by
  simp only [decodeName, ModuleBinary.nameOfBytes, decode_name_chars_source]

end Itasca.Runtime.Store

end

/-! ## StoreCapacity -/

section

/-!
Source frame capacities for issued functions and decoded store signatures. Interpreter resource causes and store invariants share these certificates.
-/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
/-- Every defined function has a source-derived static frame requirement.
Host functions impose no Wasm frame requirement. -/
def FunctionCapacity {M : Type} (code : CodeInterpretation) (store : runtime.store.Store M)
    (function : runtime.store.FuncInst) : Prop :=
  ∀ instanceIndex functionIndex, function.code = .Wasm instanceIndex functionIndex →
    ∃ inst compiled typeIndex,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      Compiler.FunctionCapacity inst.module.module.env typeIndex
        (code instanceIndex.val inst.module functionIndex.val) compiled ∧
      TypeEntries store inst.module.module.env.types.val inst.types.val ∧
      Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType) ∧
      ∃ signature, inst.module.module.env.types.val[typeIndex.val]? = some signature ∧
        store.types.val[function.signature.val]? = some signature

/-- Static source frame bounds for all issued defined functions. -/
def FunctionCapacities {M : Type} (code : CodeInterpretation) (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, FunctionCapacity code store function

/-- Canonical type indices decode to exactly the source validation table. -/
theorem TypeEntries.capacity_decode {M : Type} {store : runtime.store.Store M}
    {source : List Itasca.wasm_types.FuncType} {indices : List Usize}
    (entries : TypeEntries store source indices) :
    indices.map (fun index => (store.types.val.map decodeFuncType).getD index.val default) =
      source.map decodeFuncType := by
  induction entries with
  | nil => rfl
  | @cons ty index types indices found rest ih =>
    simp only [List.map_cons]
    rw [ih]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, found, Option.map_some, Option.getD_some]

end Itasca.Runtime.Store

end
