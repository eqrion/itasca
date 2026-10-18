import Exec.Interp.Calls.DirectCall
import Exec.Interp.Calls.CallFrames
import Exec.Abs.Sim.Instruction

namespace Exec.Interp
open Aeneas Aeneas.Std

def callCallee (address : Nat) (moduleInst : moduleinst) (results : List valtype)
    (args defaults : List val) (body : List instr) : Abs.AFrame :=
  ⟨address, results, args ++ defaults, moduleInst, [⟨results, results, [], 0, []⟩], body, []⟩

/-- Source address resolution and declaration metadata determine the next
abstract call state; no abstract-step equality is required from callers. -/
theorem call_next (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (index address : Nat)
    (moduleInst : moduleinst) (params results localTypes : List valtype)
    (typeIndex : idx) (body : List instr) (front args defaults : List val)
    (resolve : f.module.FUNCS[index]? = some address)
    (lookup : s.FUNCS[address]? = some
      ⟨⟨.mk_list params, .mk_list results⟩, moduleInst, .FUNC typeIndex (localTypes.map local.LOCAL) body⟩)
    (argumentTypes : args.map Code.valueType = params)
    (default : Abs.defaultLocals (localTypes.map local.LOCAL) = some defaults) :
    Abs.astep ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after, vals := front ++ args } :: rest, []⟩ =
      .next ⟨s, ambient, callCallee address moduleInst results args defaults body ::
        { f with code := after, vals := front } :: rest, []⟩ := by
  have types : args.map Abs.valueType = params := by
    have eq : Abs.valueType = Code.valueType := by funext v; cases v <;> try rfl
                                                   case REF_NULL ty => cases ty <;> rfl
    rw [eq, argumentTypes]
  have length : params.length = args.length := by rw [← argumentTypes, List.length_map]
  simp [Abs.astep, Abs.call, resolve, lookup, length, types, default, callCallee]

/-- Actual direct-call dispatch implements the source CALL and retains the
suspended caller's live values. Resource refusals and interrupts remain errors;
the successful path has a positive counted source simulation. -/
theorem dispatch_call_refines {M P F A : Type}
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
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex
      raw.instance raw.function raw.base (.Call index offset) ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () →
        CallEntryEffect exec out.2.1 instanceIndex functionIndex calleeBase compiled ∧
        FrameSlots out.2.1 raw { f with code := after, vals := front } ∧
        FrameSlots out.2.1 ⟨instanceIndex, functionIndex, 0#u32, calleeBase⟩
          (callCallee address.index.val moduleInst results args defaults body) ∧
        Abs.NextSim
          ⟨s, ambient, { f with code := .CALL (.mk_uN index.val) :: after, vals := front ++ args } :: rest, []⟩
          ⟨s, ambient, callCallee address.index.val moduleInst results args defaults body ::
            { f with code := after, vals := front } :: rest, []⟩) ⦄ := by
  have step := call_next s ambient f rest after index.val address.index.val moduleInst params results
    localTypes typeIndex body front args defaults resolve lookup argumentTypes default
  have simulation := Abs.instruction_simulation s ambient { f with vals := front ++ args } rest
    (.CALL (.mk_uN index.val)) after _ (.call _) typed step
  have arguments : ValuesAt exec.slots.val calleeBase.val args := by
    have values : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ args) := by
      simpa only [FrameSlots, List.append_assoc] using slots
    have words : WordsAt exec.slots.val raw.base.val
        (Code.encodeValues (f.locals ++ front) ++ Code.encodeValues args) := by
      simpa only [ValuesAt, Code.encodeValues_append] using values
    simpa only [ValuesAt, Code.encodeValues_length, baseOffset, argumentOffset] using words.append_right
  apply WP.spec_mono (direct_call_wasm_effect memory hooks floats allocator allocation interrupts
    exec store platform raw.instance raw.base index offset caller address calleeBase
    callerLookup addressLookup baseOffset function instanceIndex functionIndex inst compiled
    hf hw hi hc (by omega) capacity)
  intro out effect
  refine ⟨effect.1, ?_⟩
  intro success
  have entered := effect.2 success
  refine ⟨entered, ?_, ?_, simulation⟩
  · exact entered.caller_values slots (by rw [baseOffset, argumentOffset]) (by omega) capacity
  · have values := entered.callee_values arguments (by rw [argumentTypes, parameterSlots]) localSlots capacity default
    simpa [FrameSlots, callCallee] using values

end Exec.Interp
