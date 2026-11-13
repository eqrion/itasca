import Itasca.Runtime.Interp.Calls.DirectCall
import Itasca.Runtime.Interp.Calls.ReturnRefinement
import Itasca.Runtime.SourceMachine.Sim.Host
import Itasca.Runtime.Interp.Relations.StackRelation
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.SourceMachine.Indirect.HostSimulation
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.State.StatefulOperandSlots
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Representation.StoreCapacity

/-!
Sections, each formerly its own module: CallRefinement, CallStack, ReturnResult, CallCauses, DirectCallCause, IndirectCall, IndirectCallNext, IndirectCallSlots, IndirectResolve.
-/

/-! ## CallRefinement -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def callCallee (address : Nat) (moduleInst : moduleinst) (results : List valtype)
    (args defaults : List val) (body : List instr) : SourceMachine.AFrame :=
  ⟨address, results, args ++ defaults, moduleInst, [⟨results, results, [], 0, []⟩], body, []⟩

/-- Source address resolution and declaration metadata determine the next
abstract call state; no abstract-step equality is required from callers. -/
theorem call_next (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (index address : Nat)
    (moduleInst : moduleinst) (params results localTypes : List valtype)
    (typeIndex : idx) (body : List instr) (front args defaults : List val)
    (resolve : f.module.FUNCS[index]? = some address)
    (lookup : s.FUNCS[address]? = some
      ⟨⟨.mk_list params, .mk_list results⟩, moduleInst, .FUNC typeIndex (localTypes.map local.LOCAL) body⟩)
    (argumentTypes : args.map Compiler.valueType = params)
    (default : SourceMachine.defaultLocals (localTypes.map local.LOCAL) = some defaults) :
    SourceMachine.astep ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after, vals := front ++ args } :: rest, []⟩ =
      .next ⟨s, ambient, callCallee address moduleInst results args defaults body ::
        { f with code := after, vals := front } :: rest, []⟩ := by
  have types : args.map SourceMachine.valueType = params := by
    have eq : SourceMachine.valueType = Compiler.valueType := by
      funext v; cases v <;> try rfl
      case REF_NULL ty => cases ty <;> rfl
    rw [eq, argumentTypes]
  have length : params.length = args.length := by rw [← argumentTypes, List.length_map]
  simp [SourceMachine.astep, SourceMachine.call, resolve, lookup, length, types, default, callCallee]

end Itasca.Runtime.Interp

end

/-! ## CallStack -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Updating the active PC retains the frame's metadata and allocated region. -/
theorem FrameBinding.advance {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source) (index : Usize) (pc : U32)
    (lookup : exec.frames.val[index.val]? = some raw) :
    FrameBinding store { exec with frames := exec.frames.set index { raw with pc := pc } }
      { raw with pc := pc } source := by
  obtain ⟨inst, fn, compiled, signature, identity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, identity, ?_, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩
  have within := (List.getElem?_eq_some_iff.mp lookup).1
  simp only [alloc.vec.Vec.set_val_eq]
  apply List.mem_of_getElem? (i := index.val)
  simp [within]

/-- Fetch changes only the last frame's PC. All older frame bindings survive. -/
theorem FrameBinding.advance_older {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source) (index : Usize) (updated : runtime.interp.Frame)
    (last : index.val + 1 = exec.frames.length)
    (older : raw ∈ exec.frames.val.dropLast) :
    FrameBinding store { exec with frames := exec.frames.set index updated } raw source := by
  obtain ⟨inst, fn, compiled, signature, identity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, identity, ?_, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩
  simp only [alloc.vec.Vec.set_val_eq]
  have kept : (exec.frames.val.set index.val updated).dropLast = exec.frames.val.dropLast := by
    rw [List.dropLast_eq_take, List.length_set, List.take_set_of_le (by change exec.frames.length - 1 ≤ index.val; omega), ← List.dropLast_eq_take]
  exact List.mem_of_mem_dropLast (kept ▸ older)

end Itasca.Runtime.Interp

end

/-! ## ReturnResult -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem return_invocation_result (s : _root_.store) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front results : List val)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩)
    (split : f.vals = front ++ results)
    (types : results.map SourceMachine.valueType = f.resultTypes)
    (expected : List valtype)
    (invariant : SourceMachine.InvocationResult expected ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩) :
    SourceMachine.InvocationResult expected (returnedState s ambient rest results) := by
  have step : SourceMachine.astep ⟨s, ambient, { f with code := .RETURN :: after } :: rest, []⟩ =
      .next (returnedState s ambient rest results) := by
    simpa only [← split] using return_next s ambient f rest after front results types
  exact SourceMachine.instruction_result s ambient f rest .RETURN after _ expected .ret typed invariant step

theorem function_end_invocation_result (s : _root_.store) (ambient : frame)
    (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩)
    (types : f.vals.map SourceMachine.valueType = f.resultTypes)
    (expected : List valtype)
    (invariant : SourceMachine.InvocationResult expected ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) :
    SourceMachine.InvocationResult expected (returnedState s ambient rest f.vals) := by
  apply SourceMachine.return_frame_result typed invariant
  have length : f.resultTypes.length = f.vals.length := by rw [← types, List.length_map]
  cases rest <;> simp [SourceMachine.returnFrame, SourceMachine.AFrame.arity, length, types, returnedState, SourceMachine.advance]

/-- Returning changes only the caller's operand values, so the fixed source
code bound is retained independently of the returned value contents. -/
theorem returned_state_code_bound {bound : Nat} {s : _root_.store} {ambient : frame}
    {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (bounded : SourceMachine.CodeBound bound ⟨s, ambient, f :: rest, []⟩) (results : List val) :
    SourceMachine.CodeBound bound (returnedState s ambient rest results) := by
  cases rest with
  | nil => exact ⟨bounded.positive, by simp [returnedState, Forall], bounded.functions⟩
  | cons caller rest =>
    refine ⟨bounded.positive, ?_, bounded.functions⟩
    intro frame member
    simp only [returnedState, List.mem_cons] at member
    rcases member with rfl | member
    · exact bounded.frames caller (by simp)
    · exact bounded.frames frame (by simp [member])

end Itasca.Runtime.Interp

end

/-! ## CallCauses -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Each defined-call rejection has a concrete resource or interrupt cause.
Allocation witnesses name exactly the slot/frame vectors used at entry. -/
def CallCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (before : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (base : Usize)
    (code : runtime.bytecode.CompiledFunction) : runtime.ExecError → Prop
  | .Terminated => ∃ after, hooks.interrupt platform = .ok (.Terminate, after)
  | .Exhausted .CallStack => store.limits.max_frames.val ≤ before.frames.length
  | .Exhausted .Values => store.limits.max_values.val < base.val + code.slot_count.val
  | .Exhausted .Allocation =>
      (before.slots.length < base.val + code.slot_count.val ∧
        ∃ n : Usize, n.val = base.val + code.slot_count.val - before.slots.length ∧
          allocator.reserve before.slots n = .ok (false, before.slots)) ∨
      allocator.reserve before.frames 1#usize = .ok (false, before.frames)
  | _ => False

theorem call_wasm_causes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some code)
    (params : code.param_slots.val ≤ code.local_slots.val)
    (locals : code.local_slots.val ≤ code.slot_count.val) :
    runtime.interp.call memory hooks floats allocator exec store platform address base
      ⦃ out => ∀ error, out.1 = .Err error →
        CallCause allocator hooks exec store platform base code error ⦄ := by
  obtain ⟨⟨decision, afterPlatform⟩, hdecision, _⟩ := WP.spec_imp_exists (interrupts platform)
  unfold runtime.interp.call
  rw [interrupt_eq memory hooks platform afterPlatform decision hdecision]
  cases decision with
  | Terminate =>
    simp [interruptResult, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CallCause]
    exact ⟨afterPlatform, hdecision⟩
  | Continue =>
    simp only [interruptResult, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step with vec_index_given store.funcs address.index function hf as ⟨found, hfound⟩
    subst found
    rw [hw]
    dsimp only
    split
    · simp [CallCause]
      scalar_tac
    · rename_i room
      step with vec_index_given store.instances instanceIndex inst hi as ⟨found, hfound⟩
      subst found
      step with vec_index_given inst.module.functions functionIndex code hc as ⟨found, hfound⟩
      subst found
      simp only [lift, bind_ok]
      have hchecked := Usize.checked_add_bv_spec base (UScalar.cast .Usize code.slot_count)
      cases hend : Usize.checked_add base (UScalar.cast .Usize code.slot_count) with
      | none =>
        simp only [hend] at hchecked
        simp [CallCause]
        scalar_tac
      | some bound =>
        simp only [hend] at hchecked ⊢
        step with ensure_effect allocator allocation exec bound store.limits.max_values
          as ⟨result, afterEnsure, heffect⟩
        cases result with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          have hbound : bound.val = base.val + code.slot_count.val := by
            simpa only [U32.cast_Usize_val_eq] using hchecked.2.1
          cases error <;> simp only [EnsureEffect] at heffect
          all_goals try contradiction
          case Exhausted resource =>
            cases resource <;> simp only [EnsureEffect] at heffect
            all_goals try contradiction
            case Values =>
              simp only [CallCause]
              omega
            case Allocation =>
              apply Or.inl
              obtain ⟨hlimit, hneeded, hstate, n, hn, hr⟩ := heffect
              exact ⟨by omega, n, by omega, hr⟩
        | Ok unit =>
          cases unit
          obtain ⟨hlimit, hslots, hrest⟩ := heffect
          have hlength : afterEnsure.slots.length =
              exec.slots.length + (bound.val - exec.slots.length) := by
            change afterEnsure.slots.val.length = _
            rw [hslots, List.length_append, List.length_replicate]
          have hframes : afterEnsure.frames = exec.frames := by
            have h := congrArg runtime.interp.Execution.frames hrest
            exact h
          have hbound : bound.val = base.val + code.slot_count.val := by
            simpa only [U32.cast_Usize_val_eq] using hchecked.2.1
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
          step as ⟨start, hstart⟩
          step with init_locals_effect afterEnsure base code.local_slots start
            (by omega) (by scalar_tac) as ⟨afterInit, hinit⟩
          obtain ⟨hwords, hfields⟩ := hinit
          have hframes' : afterInit.frames = exec.frames := by
            have h := congrArg runtime.interp.Execution.frames hfields
            exact h.trans hframes
          obtain ⟨answer, hreserve⟩ := allocation.reserve_eq afterInit.frames 1#usize
          unfold runtime.reserve
          rw [hreserve, bind_ok]
          cases answer with
          | false =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CallCause]
            exact Or.inr (by simpa only [hframes'] using hreserve)
          | true =>
            simp [core.result.Result.Insts.CoreOpsTry.branch]
            have hcapacity : afterInit.frames.length < Usize.max := by
              rw [hframes']
              scalar_tac
            step
            simp


end Itasca.Runtime.Interp

end

/-! ## DirectCallCause -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A rejected direct call records the fetched instruction, resolved callee,
exact caller-PC update and callee base, and the concrete rejection cause. -/
def DirectCallCause {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (before : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (caller : runtime.store.ModuleInst)
    (callerCode : runtime.bytecode.CompiledFunction) (error : runtime.ExecError) : Prop :=
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
      store platform base compiled error

end Itasca.Runtime.Interp

end

/-! ## IndirectCall -/

section

set_option maxRecDepth 4096

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Actual indirect resolution checks the table position, null reference, and
interned signature before delegating to the ordinary call implementation. -/
theorem execute_call_indirect_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (instanceIndex functionIndex base : Usize) (entry index callee : U32)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (table type : U32) (tableAddress : runtime.TableAddr) (object : runtime.store.TableInst)
    (position : U32) (signature calleeBase : Usize)
    (instanceFound : store.instances.val[instanceIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[functionIndex.val]? = some compiled)
    (pairFound : compiled.indirect.val[entry.val]? = some (table,type))
    (tableMapped : inst.tables.val[table.val]? = some tableAddress)
    (tableFound : store.tables.val[tableAddress.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length)
    (signatureFound : inst.types.val[type.val]? = some signature)
    (baseOffset : calleeBase.val = base.val+callee.val)
    (targets : ∀ reference : U64, object.elements.val[position.val]? = some reference →
      reference ≠ 0#u64 → ∃ address : Usize, ∃ function : runtime.store.FuncInst,
        (UScalar.cast .Usize reference).val = address.val+1 ∧
        store.funcs.val[address.val]? = some function)
    (cause : Prop) (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P → Prop)
    (outside : ¬position.val < object.elements.length →
      post (.Err (.Trap .TableOutOfBounds),exec,store,platform))
    (null : object.elements.val[position.val]? = some (0#u64) →
      post (.Err (.Trap .UninitializedElement),exec,store,platform))
    (mismatch : ∀ (reference : U64) (address : Usize) (function : runtime.store.FuncInst),
      object.elements.val[position.val]? = some reference → reference ≠ 0#u64 →
      (UScalar.cast .Usize reference).val = address.val+1 →
      store.funcs.val[address.val]? = some function → function.signature ≠ signature →
      post (.Err (.Trap .IndirectCallTypeMismatch),exec,store,platform))
    (called : ∀ (reference : U64) (address : Usize) (function : runtime.store.FuncInst),
      object.elements.val[position.val]? = some reference → reference ≠ 0#u64 →
      (UScalar.cast .Usize reference).val = address.val+1 →
      store.funcs.val[address.val]? = some function → function.signature = signature →
      DivSpec cause (runtime.interp.call memory hooks floats allocator exec store platform
        {store := store.id,index := address} calleeBase) post) :
    DivSpec cause (runtime.interp.execute_call_indirect memory hooks floats allocator exec store platform
      instanceIndex functionIndex base entry index callee) post := by
  unfold runtime.interp.execute_call_indirect
  step with vec_index_given store.instances instanceIndex inst instanceFound as ⟨found,hfound⟩
  subst found
  step with vec_index_given inst.module.functions functionIndex compiled functionFound as ⟨found,hfound⟩
  subst found
  simp only [lift,bind_ok]
  step with vec_index_given compiled.indirect (UScalar.cast .Usize entry) (table,type)
    (by simpa only [U32.cast_Usize_val_eq] using pairFound) as ⟨foundTable,foundType,hfoundTable,hfoundType⟩
  subst foundTable
  subst foundType
  step with vec_index_given inst.tables (UScalar.cast .Usize table) tableAddress
    (by simpa only [U32.cast_Usize_val_eq] using tableMapped) as ⟨found,hfound⟩
  subst found
  step as ⟨slot,slotEq⟩
  have slotValue : slot.val = base.val+index.val := by scalar_tac
  have inputFound : exec.slots.val[slot.val]? = some exec.slots.val[base.val+index.val]! := by
    rw [slotValue,getElem!_pos exec.slots.val _ indexBound]
    exact List.getElem?_eq_getElem indexBound
  step with vec_index_given exec.slots slot exec.slots.val[base.val+index.val]! inputFound as ⟨word,wordEq⟩
  have wordInput : UScalar.cast .U32 word = position := by simpa only [wordEq] using input
  simp only [wordInput]
  step with vec_index_given store.tables tableAddress.index object tableFound as ⟨found,hfound⟩
  subst found
  simp only [alloc.vec.Vec.len]
  split
  · rename_i h
    have bound : ¬position.val < object.elements.length := by scalar_tac
    simpa [runtime.ExecError.Insts.CoreConvertFromTrap.from] using outside bound
  · rename_i h
    have bound : position.val < object.elements.length := by scalar_tac
    have refFound : object.elements.val[position.val]? = some object.elements.val[position.val]! := by
      rw [getElem!_pos object.elements.val _ bound]
      exact List.getElem?_eq_getElem bound
    step with vec_index_given object.elements (UScalar.cast .Usize position)
      object.elements.val[position.val]! (by simpa only [U32.cast_Usize_val_eq] using refFound)
      as ⟨reference,referenceEq⟩
    have selected : object.elements.val[position.val]? = some reference := by simpa only [referenceEq] using refFound
    split
    · rename_i zero
      simpa [runtime.ExecError.Insts.CoreConvertFromTrap.from] using null (by simpa only [zero] using selected)
    · rename_i nonzero
      obtain ⟨address,function,addressEq,targetFound⟩ := targets reference selected nonzero
      step as ⟨actualAddress,actualEq⟩
      have sameAddress : actualAddress = address := by scalar_tac
      subst actualAddress
      step with vec_index_given store.funcs address function targetFound as ⟨found,hfound⟩
      subst found
      step with vec_index_given inst.types (UScalar.cast .Usize type) signature
        (by simpa only [U32.cast_Usize_val_eq] using signatureFound) as ⟨found,hfound⟩
      subst found
      split
      · rename_i different
        have ne : function.signature ≠ signature := by simpa using different
        simpa [runtime.ExecError.Insts.CoreConvertFromTrap.from] using
          mismatch reference address function selected nonzero addressEq targetFound ne
      · rename_i same
        have eq : function.signature = signature := UScalar.eq_of_val_eq (by simpa using same)
        step as ⟨actualBase,hbase⟩
        have sameBase : actualBase = calleeBase := by
          apply UScalar.eq_of_val_eq
          simpa only [U32.cast_Usize_val_eq,baseOffset] using hbase
        subst actualBase
        exact called reference address function selected nonzero addressEq targetFound eq

end Itasca.Runtime.Interp

end

/-! ## IndirectCallNext -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem indirect_call_next (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (table type position address : Nat)
    (moduleInst : moduleinst) (params results localTypes : List valtype)
    (typeIndex : idx) (body : List instr) (front args defaults : List val)
    (resolved : SourceMachine.Indirect.resolve s f table type position = some address)
    (bounded : position < 2^32)
    (lookup : s.FUNCS[address]? = some
      ⟨⟨.mk_list params, .mk_list results⟩, moduleInst, .FUNC typeIndex (localTypes.map local.LOCAL) body⟩)
    (argumentTypes : args.map Compiler.valueType = params)
    (default : SourceMachine.defaultLocals (localTypes.map local.LOCAL) = some defaults) :
    SourceMachine.Indirect.step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after, vals:=(front++args)++[SourceMachine.integerVal .I32 position]}::rest,[]⟩
      {f with vals:=(front++args)++[SourceMachine.integerVal .I32 position]} rest table type after =
    .next ⟨s,ambient,callCallee address moduleInst results args defaults body ::
      {f with code:=after,vals:=front}::rest,[]⟩ := by
  have types : args.map SourceMachine.valueType = params := by
    simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using argumentTypes
  have length : params.length = args.length := by rw [← argumentTypes,List.length_map]
  have decoded : SourceMachine.integer numtype.I32 (SourceMachine.integerVal .I32 position)=some position := SourceMachine.integer_accepts .I32 position bounded
  have resolved' : SourceMachine.Indirect.resolve s {f with vals:=(front++args)++[SourceMachine.integerVal .I32 position]} table type position=some address := resolved
  simp only [SourceMachine.Indirect.step,SourceMachine.pop_append,decoded,resolved']
  simp [SourceMachine.Indirect.invoke,lookup,length,types,default,callCallee]
end Itasca.Runtime.Interp

end

/-! ## IndirectCallSlots -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem indirect_call_slots {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front args : List val} {params : List valtype} {position : Nat} {offset index : U32}
    (slots : FrameSlots exec raw f)
    (values : f.vals=(front++args)++[SourceMachine.integerVal .I32 position])
    (argumentTypes : args.map Compiler.valueType=params)
    (basePosition : offset.val=Compiler.slots ((f.locals++front).map Compiler.valueType))
    (indexPosition : index.val=offset.val+Compiler.slots params)
    (bounded : position<2^32) :
    ∃ selector : U32, selector.val=position ∧ raw.base.val+index.val<exec.slots.length ∧
      UScalar.cast .U32 exec.slots.val[raw.base.val+index.val]! = selector := by
  have read := Stateful.frame_read_suffix_word slots values
    (src:=index) (by simp only [List.map_append,Compiler.slots_append,argumentTypes] at basePosition ⊢;omega)
    (show Compiler.encodeValues [SourceMachine.integerVal .I32 position]=[position] from rfl) 0 (by simp)
  obtain ⟨inside,word⟩ := read
  simp only [Nat.add_zero,List.getElem!_cons_zero] at inside word
  let selector : U32 := UScalar.ofNatCore position bounded
  refine ⟨selector,rfl,inside,?_⟩
  apply UScalar.eq_of_val_eq
  simp only [UScalar.cast_val_eq,word]
  exact Nat.mod_eq_of_lt bounded
end Itasca.Runtime.Interp

end

/-! ## IndirectResolve -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

/-- An actual table range failure is an unresolved source indirect call. -/
theorem indirect_resolve_outside {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (f : SourceMachine.AFrame) (table type position : Nat)
    (object : runtime.store.TableInst)
    (tableEq : fun_table ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN table) = Store.decodeTable object)
    (outside : object.elements.length ≤ position) :
    SourceMachine.Indirect.resolve (Store.decodeStore view code store) f table type position = none := by
  simp [SourceMachine.Indirect.resolve,tableEq,Store.decodeTable,List.getElem?_eq_none outside]

/-- A null runtime table word is exactly a null source reference. -/
theorem indirect_resolve_null {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (f : SourceMachine.AFrame) (table type position : Nat)
    (object : runtime.store.TableInst)
    (tableEq : fun_table ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN table) = Store.decodeTable object)
    (selected : object.elements.val[position]? = some (0#u64)) :
    SourceMachine.Indirect.resolve (Store.decodeStore view code store) f table type position = none := by
  simp [SourceMachine.Indirect.resolve,tableEq,Store.decodeTable,selected,Store.decodeRef]

/-- Nonnull reference resolution retains the entire encoded address and uses
the exact source type comparison of the selected runtime function. -/
theorem indirect_resolve_reference {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (f : SourceMachine.AFrame) (table type position : Nat)
    (object : runtime.store.TableInst) (reference : U64) (address : Usize)
    (function : runtime.store.FuncInst)
    (tableEq : fun_table ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN table) = Store.decodeTable object)
    (funcref : object.ty = .FuncRef)
    (selected : object.elements.val[position]? = some reference)
    (word : reference.val = address.val+1)
    (found : store.funcs.val[address.val]? = some function) :
    SourceMachine.Indirect.resolve (Store.decodeStore view code store) f table type position =
      if fun_type ⟨Store.decodeStore view code store,f.toFrame⟩ (.mk_uN type) =
          (Store.decodeFunction code store function).TYPE then some address.val else none := by
  unfold SourceMachine.Indirect.resolve
  rw [tableEq]
  simp [Store.decodeTable,selected,Store.decodeRef,funcref,word,Store.decodeStore,found]

end Itasca.Runtime.Interp

end
