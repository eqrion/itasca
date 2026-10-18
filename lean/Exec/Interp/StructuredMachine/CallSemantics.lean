import Exec.Interp.StructuredMachine.Execution
import Exec.Interp.Machines.Core.CoreOwnership
namespace Exec.Interp.StructuredMachine

/-- Defined calls retain source code coverage and reference provenance. The
callee and caller stack effects are established separately by the actual call. -/
structure CallSemantics (supported : Abs.AState → Prop)
    (owned : Abs.Ownership.Bounds → Abs.AState → Prop) : Prop where
  covered : ∀ (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (index : Nat) (after : List instr) (frames : List Abs.AFrame),
    supported ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ →
    Abs.astep ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ = .next ⟨s,ambient,frames,[]⟩ →
    supported ⟨s,ambient,frames,[]⟩
  ownership : ∀ (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (index : Nat) (after : List instr) (frames : List Abs.AFrame),
    Abs.astep ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ = .next ⟨s,ambient,frames,[]⟩ →
    ∀ bounds, owned bounds ⟨s,ambient,{f with code := .CALL (.mk_uN index)::after}::rest,[]⟩ →
    owned bounds ⟨s,ambient,frames,[]⟩
end Exec.Interp.StructuredMachine
