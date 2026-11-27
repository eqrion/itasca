import Aeneas
import ItascaRust.Funs
import ItascaRust.Types
import Itasca.Results.Definitions.Foundations
import Itasca.Results.Definitions.Validation
import WebAssembly

open WebAssembly

/-!
# Decoding the API into source objects

Values, handles, signatures, instances and stores decode to SpecTec objects.
CodeInterpretation supplies source bodies for compiled functions. These are the
representation connections needed to state what the concrete API does; they do
not assert execution correctness. Frame layout and capacity certificates are internal.
-/

section RepresentationLayout

/-!
## Slot layout

Widths and their sums express the source-value storage demands used by
resource contracts. Concrete frame offsets belong to the implementation proofs.
-/

namespace Itasca.Representation

def width : valtype → Nat
  | .V128 => 2
  | _ => 1

def slots : List valtype → Nat
  | [] => 0
  | t :: ts => width t + slots ts

end Itasca.Representation

end RepresentationLayout

section RepresentationValues

/-!
## Value representation and ownership

Widths, source types and owned-value predicates connect Rust values to specification values.
-/

namespace Itasca.Representation

def valueType : val → valtype
  | .CONST ty _ => valtype_numtype ty
  | .VCONST _ _ => .V128
  | .REF_NULL .FUNCREF | .REF_FUNC_ADDR _ => .FUNCREF
  | .REF_NULL .EXTERNREF | .REF_HOST_ADDR _ => .EXTERNREF

end Itasca.Representation

namespace Itasca.Representation

open Aeneas Aeneas.Std

def rawType : runtime.Value → Itasca.wasm_types.ValueType
  | .I32 _ => .I32
  | .I64 _ => .I64
  | .F32 _ => .F32
  | .F64 _ => .F64
  | .V128 _ => .V128
  | .FuncRef _ => .FuncRef
  | .ExternRef _ => .ExternRef

def ValueOwnedFits (store : Usize) : runtime.Value → Prop
  | .FuncRef (some a) => a.store = store ∧ a.index.val < Usize.max ∧ a.index.val < U64.max
  | .ExternRef (some a) => a.store = store ∧ a.index.val < Usize.max ∧ a.index.val < U64.max
  | _ => True

def sourceValue : runtime.Value → val
  | .I32 bits => .CONST .I32 (.mk_num__0 .I32 (.mk_uN bits.val))
  | .I64 bits => .CONST .I64 (.mk_num__0 .I64 (.mk_uN bits.val))
  | .F32 bits => .CONST .F32 (.mk_num__1 .F32 (WebAssembly.Builtins.floatOfBits 32 bits.val))
  | .F64 bits => .CONST .F64 (.mk_num__1 .F64 (WebAssembly.Builtins.floatOfBits 64 bits.val))
  | .V128 bits => .VCONST .V128 (.mk_uN bits.val)
  | .FuncRef none => .REF_NULL .FUNCREF
  | .FuncRef (some address) => .REF_FUNC_ADDR address.index.val
  | .ExternRef none => .REF_NULL .EXTERNREF
  | .ExternRef (some address) => .REF_HOST_ADDR address.index.val

end Itasca.Representation

end RepresentationValues

section RepresentationStore

/-!
## Decoded stores

Code interpretations supply source bodies. Store decoding relates retained API
objects to source semantics without assuming execution correctness.
-/

namespace Itasca.Representation

open Aeneas Aeneas.Std

abbrev CodeInterpretation := Nat → runtime.compiler.ExecutableModule → Nat → funccode

def decodeLimits (length : Nat) (maximum : Option U32) : limits :=
  .mk_limits (.mk_uN length) (maximum.map fun n => .mk_uN n.val)

def decodeRef (ty : Itasca.wasm_types.ElemType) (word : U64) : ref :=
  if word.val = 0 then .REF_NULL (Itasca.Translation.referenceType ty)
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
  | .F32 => .CONST .F32 (.mk_num__1 .F32 (WebAssembly.Builtins.floatOfBits 32 (lo.val % 2^32)))
  | .F64 => .CONST .F64 (.mk_num__1 .F64 (WebAssembly.Builtins.floatOfBits 64 lo.val))
  | .V128 => .VCONST .V128 (.mk_uN (lo.val + hi.val * 2^64))
  | .FuncRef => refVal (decodeRef .FuncRef lo)
  | .ExternRef => refVal (decodeRef .ExternRef lo)

def decodeGlobal (g : runtime.store.GlobalInst) : globalinst :=
  ⟨.mk_globaltype (Itasca.Translation.mutability g.ty.mutability) (Itasca.Translation.valueType g.ty.valtype),
    decodeWords g.ty.valtype g.lo g.hi⟩

def decodeTable (t : runtime.store.TableInst) : tableinst :=
  ⟨.mk_tabletype (decodeLimits t.elements.length t.maximum) (Itasca.Translation.referenceType t.ty),
    t.elements.val.map (decodeRef t.ty)⟩

def decodeBytes (bytes : List U8) : List byte := bytes.map fun b => .mk_byte b.val

def decodeMemory {M : Type} (view : M → Slice U8) (m : runtime.store.MemInst M) : meminst :=
  ⟨.PAGE (decodeLimits ((view m.buf).length / 65536) m.maximum), decodeBytes (view m.buf).val⟩

def decodeElement (e : runtime.store.ElemInst) : eleminst :=
  ⟨Itasca.Translation.referenceType e.ty, e.refs.val.map (decodeRef e.ty)⟩

def decodeData (d : runtime.store.DataInst) : datainst := ⟨decodeBytes d.bytes.val⟩

def decodeExport (inst : runtime.store.ModuleInst) (e : Itasca.metadata.Export) : exportinst :=
  ⟨Itasca.Binary.nameOfBytes e.name.val, match e.desc with
    | .Func i => .FUNC ((inst.funcs.val.map fun a => a.index.val).getD i.val 0)
    | .Table i => .TABLE ((inst.tables.val.map fun a => a.index.val).getD i.val 0)
    | .Memory i => .MEM ((inst.memories.val.map fun a => a.index.val).getD i.val 0)
    | .Global i => .GLOBAL ((inst.globals.val.map fun a => a.index.val).getD i.val 0)⟩

def decodeInstance {M : Type} (s : runtime.store.Store M) (inst : runtime.store.ModuleInst) : moduleinst :=
  ⟨inst.types.val.map (fun i => (s.types.val.map Itasca.Translation.Environment.funcType).getD i.val default),
    inst.funcs.val.map (fun a => a.index.val), inst.globals.val.map (fun a => a.index.val),
    inst.tables.val.map (fun a => a.index.val), inst.memories.val.map (fun a => a.index.val),
    inst.elems.val.map UScalar.val, inst.datas.val.map UScalar.val,
    inst.module.module.env.exports.val.map (decodeExport inst)⟩

def decodeFunction {M : Type} (code : CodeInterpretation) (s : runtime.store.Store M)
    (f : runtime.store.FuncInst) : funcinst :=
  let ty := (s.types.val.map Itasca.Translation.Environment.funcType).getD f.signature.val default
  match f.code with
  | .Host id => ⟨ty, default, .HOST id.val⟩
  | .Wasm instIndex fn =>
    match s.instances.val[instIndex.val]? with
    | some inst => ⟨ty, decodeInstance s inst, code instIndex.val inst.module fn.val⟩
    | none => ⟨ty, default, .HOST 0⟩

def decodeStore {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) : WebAssembly.store :=
  ⟨s.funcs.val.map (decodeFunction code s), s.globals.val.map decodeGlobal,
    s.tables.val.map decodeTable, s.memories.val.map (decodeMemory view),
    s.elems.val.map decodeElement, s.datas.val.map decodeData⟩

end Itasca.Representation

end RepresentationStore
