import Exec.Theorems.Composition.Supported.SupportedTotal
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- The fetched direct call is tied to its source opcode, not only to an
unindexed raw store boundary. -/
def DirectHostInstruction {M : Type} (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (op : instr) : Prop :=
  ∃ (index offset : U32) (address : runtime.FuncAddr) (function : runtime.store.Function) (host : U64),
    op=.CALL (.mk_uN index.val) ∧
    compiled.code.val[raw.pc.val]?=some (.Call index offset) ∧
    inst.funcs.val[index.val]?=some address ∧ store.funcs.val[address.index.val]?=some function ∧
    function.code=.Host host

/-- The normalized source point and concrete frame needed to discharge a host
boundary. All fields come from the existing execution invariant. -/
structure HostFrameSite {M : Type} (emission : StructuredMachine.FunctionEmission) (allowed : instr → Prop)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (expected : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) where
  index : Usize
  raw : runtime.interp.Frame
  inst : runtime.store.Instance
  compiled : runtime.bytecode.CompiledFunction
  context : _root_.context
  targets : List Code.LabelTarget
  next : Nat
  output : List valtype
  last : index.val+1=exec.frames.length
  frameAt : exec.frames.val[index.val]?=some raw
  instanceAt : store.instances.val[raw.instance.val]?=some inst
  compiledAt : inst.module.functions.val[raw.function.val]?=some compiled
  program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes context.FUNCS
  slots : FrameSlots exec raw f
  moduleEq : f.module=Store.decodeInstance store inst
  point : StructuredMachine.FramePoint emission (Store.decodeStore view code store) raw f compiled context targets next output
  machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec
    ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩ expected raw.pc.val false
  owned : Abs.Ownership.StateOwned (Store.ownershipBounds store)
    ⟨Store.decodeStore view code store,ambient,f::rest,[]⟩

/-- Actual common dispatch yields one of these sites or an ordinary checked
step. Source-only normalization is retained for the later eventful join. -/
inductive StructuredHostSite {M : Type} (emission : StructuredMachine.FunctionEmission) (allowed : instr → Prop)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (expected : List valtype) : Nat → Bool → Abs.AState → Prop where
  | ready {ambient : frame} {f : Abs.AFrame} {rest : List Abs.AFrame} {op : instr} {after : List instr}
      (site : HostFrameSite emission allowed view code exec store expected ambient {f with code:=op::after} rest)
      (kind : DirectHostInstruction store site.raw site.inst site.compiled op ∨
        ∃ table type : U32, op=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val) ∧
          SourceIndirectHostBoundary store ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩) :
      StructuredHostSite emission allowed view code exec store expected site.raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩
  | normalize {count pc s ambient before after rest}
      (chain : ErasedSteps count before after)
      (site : StructuredHostSite emission allowed view code exec store expected pc false ⟨s,ambient,after::rest,[]⟩) :
      StructuredHostSite emission allowed view code exec store expected pc false ⟨s,ambient,before::rest,[]⟩
end Exec.Theorems
