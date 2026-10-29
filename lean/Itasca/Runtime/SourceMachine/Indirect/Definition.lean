import Itasca.Runtime.Spec.IndirectCallSource
import Itasca.Runtime.SourceMachine.Sim.Call
namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec

def resolve (s : store) (f : AFrame) (table type position : Nat) : Option Nat :=
  match (fun_table ⟨s,f.toFrame⟩ (.mk_uN table)).REFS[position]? with
  | some (.REF_FUNC_ADDR address) =>
    match s.FUNCS[address]? with
    | some function => if fun_type ⟨s,f.toFrame⟩ (.mk_uN type)=function.TYPE then some address else none
    | none => none
  | _ => none

theorem resolve_iff (s : store) (f : AFrame) (table type position address : Nat) :
    resolve s f table type position=some address ↔ IndirectTarget s f.toFrame table type position address := by
  unfold resolve IndirectTarget
  split
  · rename_i actual reference
    split
    · rename_i function lookup
      split
      · rename_i signature
        constructor
        · intro equal;cases equal;exact ⟨reference,function,lookup,signature⟩
        · rintro ⟨other,fn,found,same⟩
          have addressEq := Option.some.inj (reference.symm.trans other)
          cases addressEq
          rfl
      · rename_i signature
        constructor
        · intro impossible;cases impossible
        · rintro ⟨other,fn,found,same⟩
          have addressEq := Option.some.inj (reference.symm.trans other)
          cases addressEq
          have fnEq := Option.some.inj (lookup.symm.trans found)
          cases fnEq
          exact (signature same).elim
    · rename_i missing
      constructor
      · intro impossible;cases impossible
      · rintro ⟨other,fn,found,same⟩
        have addressEq := Option.some.inj (reference.symm.trans other)
        cases addressEq
        rw [missing] at found
        cases found
  · rename_i reference missing
    constructor
    · intro impossible;cases impossible
    · rintro ⟨found,_⟩
      exact (missing address found).elim

/-- Direct and indirect calls share the exact resolved-address installation. -/
def invoke (s : AState) (f : AFrame) (rest : List AFrame) (address : Nat) (after : List instr) : AResult :=
  match s.store.FUNCS[address]? with
  | none => .stuck
  | some function =>
    let ⟨.mk_list params, .mk_list results⟩ := function.TYPE
    if params.length ≤ f.vals.length then
      let args := f.vals.drop (f.vals.length - params.length)
      if args.map valueType = params then
        let caller := { f with vals := f.vals.take (f.vals.length - params.length), code := after }
        match function.CODE with
        | .HOST _ => .host address args results { s with frames := caller :: rest }
        | .FUNC _ locals body =>
          match defaultLocals locals with
          | none => .stuck
          | some defaults =>
            let label : Label := {
              branchTypes := results
              resultTypes := results
              cont := []
              height := 0
              after := [] }
            let callee : AFrame := {
              fa := address
              resultTypes := results
              locals := args ++ defaults
              module := function.MODULE
              labels := [label]
              code := body
              vals := [] }
            .next { s with frames := callee :: caller :: rest }
      else .stuck
    else .stuck

def step (s : AState) (f : AFrame) (rest : List AFrame) (table type : Nat) (after : List instr) : AResult :=
  match pop f.vals with
  | none => .stuck
  | some (front,value) => match integer .I32 value with
    | none => .stuck
    | some position => match resolve s.store f table type position with
      | none => .trap
      | some address => invoke s {f with vals:=front} rest address after

end Itasca.Runtime.Abs.Indirect
