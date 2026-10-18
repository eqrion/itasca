import Exec.Interp.Calls.CallRefinement

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_call_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex : Usize) (raw : runtime.interp.Frame) (index offset : U32)
    (caller : runtime.store.Instance) (address : runtime.FuncAddr) (calleeBase : Usize)
    (callerLookup : store.instances.val[raw.instance.val]? = some caller)
    (addressLookup : caller.funcs.val[index.val]? = some address)
    (baseOffset : calleeBase.val = raw.base.val + offset.val)
    (callerCode : runtime.bytecode.CompiledFunction)
    (last : frameIndex.val + 1 = exec.frames.length)
    (frameLookup : exec.frames.val[frameIndex.val]? = some raw)
    (codeLookup : caller.module.functions.val[raw.function.val]? = some callerCode)
    (fetched : callerCode.code.val[raw.pc.val]? = some (.Call index offset))
    (pcBound : raw.pc.val < U32.max)
    (function : runtime.store.Function) (instanceIndex functionIndex : Usize)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (hi : store.instances.val[instanceIndex.val]? = some inst)
    (hc : inst.module.functions.val[functionIndex.val]? = some compiled)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after body : List instr) (front args defaults : List val)
    (moduleInst : moduleinst) (params results localTypes : List valtype) (typeIndex : idx)
    (resolve : f.module.FUNCS[index.val]? = some address.index.val)
    (lookup : s.FUNCS[address.index.val]? = some
      ⟨⟨.mk_list params, .mk_list results⟩, moduleInst, .FUNC typeIndex (localTypes.map local.LOCAL) body⟩)
    (argumentTypes : args.map Code.valueType = params)
    (default : Abs.defaultLocals (localTypes.map local.LOCAL) = some defaults)
    (typed : Abs.ATyped ⟨s, ambient,
      { f with code := .CALL (.mk_uN index.val) :: after, vals := front ++ args } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ args })
    (argumentOffset : offset.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (parameterSlots : compiled.param_slots.val = Code.slots params)
    (localSlots : compiled.local_slots.val = compiled.param_slots.val + Code.slots localTypes)
    (capacity : compiled.local_slots.val ≤ compiled.slot_count.val) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
          CallEntryEffect { exec with frames := exec.frames.set frameIndex { raw with pc := pc } }
            out.2.1 instanceIndex functionIndex calleeBase compiled) ∧
        FrameSlots out.2.1 raw { f with code := after, vals := front } ∧
        FrameSlots out.2.1 ⟨instanceIndex, functionIndex, 0#u32, calleeBase⟩
          (callCallee address.index.val moduleInst results args defaults body) ∧
        Abs.NextSim
          ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after, vals := front ++ args } :: rest, []⟩
          ⟨s, ambient, callCallee address.index.val moduleInst results args defaults body ::
            { f with code := after, vals := front } :: rest, []⟩) ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw caller callerCode
    (.Call index offset) last frameLookup callerLookup codeLookup fetched pcBound
  intro pc hpc
  apply WP.spec_mono (dispatch_call_refines memory hooks floats allocator allocation interrupts
    { exec with frames := exec.frames.set frameIndex { raw with pc := pc } }
    store platform frameIndex raw index offset caller address calleeBase callerLookup addressLookup baseOffset
    function instanceIndex functionIndex inst compiled hf hw hi hc s ambient f rest after body front args defaults
    moduleInst params results localTypes typeIndex resolve lookup argumentTypes default typed slots
    argumentOffset parameterSlots localSlots capacity)
  intro out effect
  refine ⟨effect.1, ?_⟩
  intro success
  have actual := effect.2 success
  exact ⟨⟨pc, hpc, actual.1⟩, actual.2⟩

end Exec.Interp
