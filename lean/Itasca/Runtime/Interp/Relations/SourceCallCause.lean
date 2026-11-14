import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.SourceMachine.Float.Results
import Itasca.Runtime.SourceMachine.Memory.Decode
import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.SourceMachine.Simd.Source
import Itasca.Runtime.Interp.Machine.Emission.Local
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.Interp.Calls.IndirectResolve
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Spec.SegmentInitCases

/-!
Sections, each formerly its own module: HeadCoverage, SourceCallCause.
-/

/-! ## HeadCoverage -/

section

namespace Itasca.Runtime.Interp
open Aeneas.Std

/-- Source forms remaining after zero-byte normalization. -/
def ReadyInstruction : instr → Prop
  | .NOP | .DROP | .BLOCK _ _ => False
  | _ => True

/-- Ready source heads the interpreter dispatches, as recovered from the compiler certificate.
Indices and constant words come from emitted syntax, not assumptions. -/
inductive DispatchHead : instr → Prop where
  | numeric (op : SourceMachine.Numeric.Instruction) : DispatchHead op.source
  | ordinary (op : OrdinaryOpcode) : DispatchHead op.source
  | loop (bt : blocktype) (body : List instr) : DispatchHead (.LOOP bt body)
  | call (index : U32) : DispatchHead (.CALL (.mk_uN index.val))
  | return_ : DispatchHead .RETURN
  | unreachable : DispatchHead .UNREACHABLE
  | float32 (bits : U32) : DispatchHead (.CONST .F32 (.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 bits.val)))
  | float64 (bits : U64) : DispatchHead (.CONST .F64 (.mk_num__1 .F64 (SpecExt.Builtins.floatOfBits 64 bits.val)))
  | select : DispatchHead (.SELECT none)
  | globalGet (index : U32) : DispatchHead (.GLOBAL_GET (.mk_uN index.val))
  | globalSet (index : U32) : DispatchHead (.GLOBAL_SET (.mk_uN index.val))
  | load (op : SourceMachine.Memory.Load) (argument : memarg) : DispatchHead (op.source argument)
  | store (op : SourceMachine.Memory.Store) (argument : memarg) : DispatchHead (op.source argument)
  | float (op : SourceMachine.Float.Instruction) : DispatchHead op.source
  | stateful (op : SourceMachine.Stateful.Instruction) : DispatchHead op.source
  | indirect (table type : U32) : DispatchHead (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val))
  | simd {op} : SourceMachine.SimdInstr op → DispatchHead op
  | typedSelect (ty : valtype) : DispatchHead (.SELECT (some [ty]))
  | branchTable (depths : List labelidx) (fallback : labelidx) : DispatchHead (.BR_TABLE depths fallback)

end Itasca.Runtime.Interp

end

/-! ## SourceCallCause -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Storage retained by suspended source callers. Arguments passed to the
callee have already been removed from these operand lists. -/
def suspendedSourceWords : List SourceMachine.AFrame → Nat
  | [] => 0
  | f :: rest => Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType) + suspendedSourceWords rest

/-- A reachable source call identifies its callee and shared argument position.
This predicate uses only source configurations, values, and addresses. -/
def SourceCallSite (initial : SourceMachine.AState) (address : funcaddr) (base : Nat) : Prop :=
  ∃ (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
      (target : Nat) (after : List instr) (front args : List val) (callee : funcinst)
      (params results : List valtype) (count : Nat),
    Spec.StepsHN count (SourceMachine.decode initial) [] (SourceMachine.decode ⟨initial.store, initial.ambient,
      {f with code := .CALL (.mk_uN target) :: after, vals := front ++ args} :: rest, []⟩) ∧
    f.module.FUNCS[target]? = some address ∧
    initial.store.FUNCS[address]? = some callee ∧
    callee.TYPE = .mk_functype (.mk_list params) (.mk_list results) ∧
    args.map Compiler.valueType = params ∧
    base = suspendedSourceWords rest + Compiler.slots ((f.locals ++ front).map Compiler.valueType)

theorem SourceCallSite.prepend {before middle : SourceMachine.AState} {address base count}
    (steps : Spec.StepsHN count (SourceMachine.decode before) [] (SourceMachine.decode middle))
    (sameStore : middle.store = before.store) (sameAmbient : middle.ambient = before.ambient)
    (site : SourceCallSite middle address base) :
    SourceCallSite before address base := by
  obtain ⟨f, rest, target, after, front, args, callee, params, results, tailCount, tail, lookup, functionFound, signature, arguments, offset⟩ := site
  exact ⟨f, rest, target, after, front, args, callee, params, results, count + tailCount,
    by simpa only [sameStore, sameAmbient, List.nil_append] using steps.trans tail, lookup,
    by simpa only [sameStore] using functionFound, signature, arguments, offset⟩

/-- A rejected direct call retains its precise concrete cause together with
source provenance of the shared callee argument position. -/
def SourceDirectCallCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (before : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (caller : runtime.store.ModuleInst)
    (callerCode : runtime.bytecode.CompiledFunction) (source : SourceMachine.AState)
    (error : runtime.ExecError) : Prop :=
  ∃ (target offset pc : U32) (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction),
    callerCode.code.val[raw.pc.val]? = some (.Call target offset) ∧
    caller.funcs.val[target.val]? = some address ∧
    store.funcs.val[address.index.val]? = some function ∧
    function.code = .Wasm instanceIndex functionIndex ∧
    store.instances.val[instanceIndex.val]? = some inst ∧
    inst.module.functions.val[functionIndex.val]? = some compiled ∧
    base.val = raw.base.val + offset.val ∧ pc.val = raw.pc.val + 1 ∧
    CallCause allocator hooks
      { before with frames := before.frames.set frameIndex { raw with pc := pc } }
      store platform base compiled error ∧
    SourceCallSite source address.index.val base.val

theorem SourceDirectCallCause.concrete {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {before : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {frameIndex : Usize}
    {raw : runtime.interp.Frame} {caller : runtime.store.ModuleInst}
    {callerCode : runtime.bytecode.CompiledFunction} {source : SourceMachine.AState} {error : runtime.ExecError}
    (cause : SourceDirectCallCause allocator hooks before store platform frameIndex raw caller callerCode source error) :
    DirectCallCause allocator hooks before store platform frameIndex raw caller callerCode error := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    inst, compiled, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site⟩ := cause
  exact ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    inst, compiled, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection⟩

theorem SourceDirectCallCause.prepend {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {frameIndex : Usize}
    {raw : runtime.interp.Frame} {caller : runtime.store.ModuleInst}
    {compiled : runtime.bytecode.CompiledFunction} {before after : SourceMachine.AState} {error : runtime.ExecError} {count}
    (steps : Spec.StepsHN count (SourceMachine.decode before) [] (SourceMachine.decode after))
    (sameStore : after.store = before.store) (sameAmbient : after.ambient = before.ambient)
    (cause : SourceDirectCallCause allocator hooks exec store platform frameIndex raw caller compiled after error) :
    SourceDirectCallCause allocator hooks exec store platform frameIndex raw caller compiled before error := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    inst, code, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site⟩ := cause
  exact ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    inst, code, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site.prepend steps sameStore sameAmbient⟩
end Itasca.Runtime.Interp

end
