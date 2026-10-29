import Itasca.Runtime.Interp.Calls.DirectCall
import Itasca.Runtime.Interp.Calls.CallFrames
import Itasca.Runtime.SourceMachine.Sim.Instruction

namespace Itasca.Runtime.Interp
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

end Itasca.Runtime.Interp
