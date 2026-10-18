import Exec.Representation.Values
import Exec.Platform.Memory

/-! Concrete store decoding. `CodeInterpretation` supplies source function bodies
which are not retained in the compiled Rust module. Compilation constructs this
interpretation and its code relation; this parameter contains no execution
correctness assumption. The first index names the retained instance, so equal
compiled modules can carry distinct source certificates. All other objects decode directly from retained data. -/
namespace Exec.Store
open Aeneas Aeneas.Std

abbrev CodeInterpretation := Nat → runtime.compiler.ExecutableModule → Nat → funccode

def decodeVal : runtime.Value → val := Interp.sourceValue

def decodeFuncType (ty : Itasca.types.FuncType) : functype :=
  .mk_functype (.mk_list (ty.params.val.map Interp.sourceType)) (.mk_list (ty.results.val.map Interp.sourceType))

def decodeElemType : Itasca.types.ElemType → reftype
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

def decodeMut : Itasca.types.Mut → «mut»
  | .Const => none
  | .Var => some .MUT

def decodeLimits (length : Nat) (maximum : Option U32) : limits :=
  .mk_limits (.mk_uN length) (maximum.map fun n => .mk_uN n.val)

def decodeRef (ty : Itasca.types.ElemType) (word : U64) : ref :=
  if word.val = 0 then .REF_NULL (decodeElemType ty)
  else match ty with
    | .FuncRef => .REF_FUNC_ADDR (word.val - 1)
    | .ExternRef => .REF_HOST_ADDR (word.val - 1)

def refVal : ref → val
  | .REF_NULL ty => .REF_NULL ty
  | .REF_FUNC_ADDR address => .REF_FUNC_ADDR address
  | .REF_HOST_ADDR address => .REF_HOST_ADDR address

def decodeWords (ty : Itasca.types.ValueType) (lo hi : U64) : val :=
  match ty with
  | .I32 => .CONST .I32 (.mk_num__0 .I32 (.mk_uN (lo.val % 2^32)))
  | .I64 => .CONST .I64 (.mk_num__0 .I64 (.mk_uN lo.val))
  | .F32 => .CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 (lo.val % 2^32)))
  | .F64 => .CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 lo.val))
  | .V128 => .VCONST .V128 (.mk_uN (lo.val + hi.val * 2^64))
  | .FuncRef => refVal (decodeRef .FuncRef lo)
  | .ExternRef => refVal (decodeRef .ExternRef lo)

def decodeGlobal (g : runtime.store.GlobalInstance) : globalinst :=
  ⟨.mk_globaltype (decodeMut g.ty.mutability) (Interp.sourceType g.ty.valtype),
    decodeWords g.ty.valtype g.lo g.hi⟩

def decodeTable (t : runtime.store.Table) : tableinst :=
  ⟨.mk_tabletype (decodeLimits t.elements.length t.maximum) (decodeElemType t.ty),
    t.elements.val.map (decodeRef t.ty)⟩

def decodeBytes (bytes : List U8) : List byte := bytes.map fun b => .mk_byte b.val

def decodeMemory {M : Type} (view : M → Slice U8) (m : runtime.store.Memory M) : meminst :=
  ⟨.PAGE (decodeLimits ((view m.buf).length / 65536) m.maximum), decodeBytes (view m.buf).val⟩

def decodeElement (e : runtime.store.ElemInstance) : eleminst :=
  ⟨decodeElemType e.ty, e.refs.val.map (decodeRef e.ty)⟩

def decodeData (d : runtime.store.DataInstance) : datainst := ⟨decodeBytes d.bytes.val⟩

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

def decodeExport (inst : runtime.store.Instance) (e : Itasca.module.Export) : exportinst :=
  ⟨decodeName e.name.val, match e.desc with
    | .Func i => .FUNC ((inst.funcs.val.map fun a => a.index.val).getD i.val 0)
    | .Table i => .TABLE ((inst.tables.val.map fun a => a.index.val).getD i.val 0)
    | .Memory i => .MEM ((inst.memories.val.map fun a => a.index.val).getD i.val 0)
    | .Global i => .GLOBAL ((inst.globals.val.map fun a => a.index.val).getD i.val 0)⟩

def decodeInstance {M : Type} (s : runtime.store.Store M) (inst : runtime.store.Instance) : moduleinst :=
  ⟨inst.types.val.map (fun i => (s.types.val.map decodeFuncType).getD i.val default),
    inst.funcs.val.map (fun a => a.index.val), inst.globals.val.map (fun a => a.index.val),
    inst.tables.val.map (fun a => a.index.val), inst.memories.val.map (fun a => a.index.val),
    inst.elements.val.map UScalar.val, inst.data.val.map UScalar.val,
    inst.module.module.env.exports.val.map (decodeExport inst)⟩

def decodeFunction {M : Type} (code : CodeInterpretation) (s : runtime.store.Store M)
    (f : runtime.store.Function) : funcinst :=
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

theorem decodeStore_lengths {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) :
    (decodeStore view code s).FUNCS.length = s.funcs.length ∧
    (decodeStore view code s).GLOBALS.length = s.globals.length ∧
    (decodeStore view code s).TABLES.length = s.tables.length ∧
    (decodeStore view code s).MEMS.length = s.memories.length ∧
    (decodeStore view code s).ELEMS.length = s.elems.length ∧
    (decodeStore view code s).DATAS.length = s.datas.length := by simp [decodeStore]

/-- Replacing the concrete memory vector changes only the decoded memory
component; function and module decoding do not depend on its opaque buffers. -/
theorem decodeStore_memory_update {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (memories : alloc.vec.Vec (runtime.store.Memory M)) :
    decodeStore view code {s with memories := memories} =
      {decodeStore view code s with MEMS := memories.val.map (decodeMemory view)} := by
  rfl


end Exec.Store
