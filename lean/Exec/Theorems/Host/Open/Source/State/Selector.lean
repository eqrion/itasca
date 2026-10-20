import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Exec.Interp.Relations.SourceValueInjective
noncomputable section
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- Canonical immutable host selection from source identity and source values.
Ownership is fixed by the entered store identity. No execution or store outcome
is used to choose code; unrepresentable source requests select empty code. -/
def sourceSelector (select : Selector) (owner : Usize) (identity : Nat) (arguments : List val) : Code := by
  classical
  exact if h : ∃rawIdentity : U64,∃rawArgs : Slice runtime.Value,
      rawIdentity.val=identity ∧ (∀v∈rawArgs.val,OwnedBy owner v) ∧ rawArgs.val.map sourceValue=arguments
    then select h.choose h.choose_spec.choose
    else []

/-- Canonical source selection agrees with every owned concrete representation,
including reference identities and all floating-point bit patterns. -/
theorem sourceSelector_agrees (select : Selector) (owner : Usize)
    (identity : U64) (arguments : Slice runtime.Value)
    (owned : ∀v∈arguments.val,OwnedBy owner v) :
    sourceSelector select owner identity.val (arguments.val.map sourceValue)=select identity arguments := by
  classical
  unfold sourceSelector
  split
  · rename_i h
    have facts := h.choose_spec.choose_spec
    have identityEq : h.choose=identity := by
      have same := facts.1
      scalar_tac
    have argsEq : h.choose_spec.choose=arguments :=
      sourceSlice_injective_owned owner _ arguments facts.2.1 owned facts.2.2
    exact congrArg₂ select identityEq argsEq
  · rename_i missing
    exact False.elim (missing ⟨identity,arguments,rfl,owned,rfl⟩)

/-- Source host control contains only immutable chosen code, source arguments,
and a program counter. It does not retain mutable store or memory access. -/
structure SourceHostState where
  pc : Nat
  code : Code
  identity : Nat
  arguments : List val

def sourceHostEntry (select : Selector) (owner : Usize) (identity : Nat) (arguments : List val) : SourceHostState :=
  ⟨0,sourceSelector select owner identity arguments,identity,arguments⟩

def HostStateRepresents (owner : Usize) (source : SourceHostState) (raw : HostState) : Prop :=
  source.pc=raw.pc ∧ source.code=raw.code ∧ source.identity=raw.identity.val ∧
    source.arguments=raw.arguments.val.map sourceValue ∧ (∀v∈raw.arguments.val,OwnedBy owner v)

theorem sourceHostEntry_represents (select : Selector) (owner : Usize)
    (identity : U64) (arguments : Slice runtime.Value)
    (owned : ∀v∈arguments.val,OwnedBy owner v) :
    HostStateRepresents owner (sourceHostEntry select owner identity.val (arguments.val.map sourceValue))
      ⟨0,select identity arguments,identity,arguments⟩ :=
  ⟨rfl,sourceSelector_agrees select owner identity arguments owned,rfl,rfl,owned⟩
end Exec.Theorems.OpenReentrantControl
