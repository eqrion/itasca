import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Abs.Indirect.Definition
import Itasca.Runtime.Interp.Relations.TypedOperands
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem indirect_call_next (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (table type position address : Nat)
    (moduleInst : moduleinst) (params results localTypes : List valtype)
    (typeIndex : idx) (body : List instr) (front args defaults : List val)
    (resolved : Abs.Indirect.resolve s f table type position = some address)
    (bounded : position < 2^32)
    (lookup : s.FUNCS[address]? = some
      ⟨⟨.mk_list params, .mk_list results⟩, moduleInst, .FUNC typeIndex (localTypes.map local.LOCAL) body⟩)
    (argumentTypes : args.map Code.valueType = params)
    (default : Abs.defaultLocals (localTypes.map local.LOCAL) = some defaults) :
    Abs.Indirect.step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after, vals:=(front++args)++[Abs.integerVal .I32 position]}::rest,[]⟩
      {f with vals:=(front++args)++[Abs.integerVal .I32 position]} rest table type after =
    .next ⟨s,ambient,callCallee address moduleInst results args defaults body ::
      {f with code:=after,vals:=front}::rest,[]⟩ := by
  have types : args.map Abs.valueType = params := by
    simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using argumentTypes
  have length : params.length = args.length := by rw [← argumentTypes,List.length_map]
  have decoded : Abs.integer numtype.I32 (Abs.integerVal .I32 position)=some position := Abs.integer_accepts .I32 position bounded
  have resolved' : Abs.Indirect.resolve s {f with vals:=(front++args)++[Abs.integerVal .I32 position]} table type position=some address := resolved
  simp only [Abs.Indirect.step,Abs.pop_append,decoded,resolved']
  simp [Abs.Indirect.invoke,lookup,length,types,default,callCallee]
end Itasca.Runtime.Interp
