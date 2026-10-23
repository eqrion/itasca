import Exec.Interp.Calls.DirectCallCause
import Exec.Interp.Relations.StackRelation
import Exec.Spec.Counted
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Storage retained by suspended source callers. Arguments passed to the
callee have already been removed from these operand lists. -/
def suspendedSourceWords : List Abs.AFrame → Nat
  | [] => 0
  | f :: rest => Code.slots ((f.locals ++ f.vals).map Code.valueType) + suspendedSourceWords rest

/-- A reachable source call identifies its callee and shared argument position.
This predicate uses only source configurations, values, and addresses. -/
def SourceCallSite (initial : Abs.AState) (address : funcaddr) (base : Nat) : Prop :=
  ∃ (f : Abs.AFrame) (rest : List Abs.AFrame)
      (target : Nat) (after : List instr) (front args : List val) (callee : funcinst)
      (params results : List valtype) (count : Nat),
    Spec.StepsHN count (Abs.decode initial) [] (Abs.decode ⟨initial.store, initial.ambient,
      {f with code := .CALL (.mk_uN target) :: after, vals := front ++ args} :: rest, []⟩) ∧
    f.module.FUNCS[target]? = some address ∧
    initial.store.FUNCS[address]? = some callee ∧
    callee.TYPE = .mk_functype (.mk_list params) (.mk_list results) ∧
    args.map Code.valueType = params ∧
    base = suspendedSourceWords rest + Code.slots ((f.locals ++ front).map Code.valueType)

theorem SourceCallSite.prepend {before middle : Abs.AState} {address base count}
    (steps : Spec.StepsHN count (Abs.decode before) [] (Abs.decode middle))
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
    (callerCode : runtime.bytecode.CompiledFunction) (source : Abs.AState)
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
    {callerCode : runtime.bytecode.CompiledFunction} {source : Abs.AState} {error : runtime.ExecError}
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
    {compiled : runtime.bytecode.CompiledFunction} {before after : Abs.AState} {error : runtime.ExecError} {count}
    (steps : Spec.StepsHN count (Abs.decode before) [] (Abs.decode after))
    (sameStore : after.store = before.store) (sameAmbient : after.ambient = before.ambient)
    (cause : SourceDirectCallCause allocator hooks exec store platform frameIndex raw caller compiled after error) :
    SourceDirectCallCause allocator hooks exec store platform frameIndex raw caller compiled before error := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    inst, code, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site⟩ := cause
  exact ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    inst, code, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection, site.prepend steps sameStore sameAmbient⟩
end Exec.Interp
