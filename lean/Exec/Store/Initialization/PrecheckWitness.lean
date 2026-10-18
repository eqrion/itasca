import Exec.Store.Initialization.PrecheckErrors
namespace Exec.Store
open Aeneas Aeneas.Std

/-- An actual active element offset resolves beyond its actual target table.
The expression, local target map, store target, and payload are retained. -/
def ElementBoundsFailure {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.Instance) : Prop :=
  ∃ (index : Usize) (segment : Itasca.module.Element) (target : U32)
      (offset : Itasca.types.ConstExpr) (words : List U64) (address : runtime.TableAddr)
      (table : runtime.store.Table),
    inst.module.module.env.elements.val[index.val]? = some segment ∧
    segment.mode = .Active target offset ∧
    Interp.InitializerResolution store inst offset .I32 words ∧
    inst.tables.val[target.val]? = some address ∧
    store.tables.val[address.index.val]? = some table ∧
    table.elements.length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length

/-- The corresponding exact source-offset witness for an active data segment. -/
def DataBoundsFailure {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (inst : runtime.store.Instance) : Prop :=
  ∃ (index : Usize) (segment : Itasca.module.Data) (target : U32)
      (offset : Itasca.types.ConstExpr) (words : List U64) (address : runtime.MemoryAddr)
      (memory : runtime.store.Memory M),
    inst.module.module.tail.data.val[index.val]? = some segment ∧
    segment.mode = .Active target offset ∧
    Interp.InitializerResolution store inst offset .I32 words ∧
    inst.memories.val[target.val]? = some address ∧
    store.memories.val[address.index.val]? = some memory ∧
    (view memory.buf).length < ((words[0]?).getD 0#u64).val % 2^32 + segment.init.length

def PrecheckCause {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (inst : runtime.store.Instance) (error : runtime.ExecError) : Prop :=
  ResourceError error ∨
  (error = .Trap .TableOutOfBounds ∧ ElementBoundsFailure store inst) ∨
  (error = .Trap .MemoryOutOfBounds ∧ DataBoundsFailure view store inst)

theorem PrecheckCause.precommit {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {inst error} (cause : PrecheckCause view store inst error) :
    PrecommitError .Wasm1 error := by
  rcases cause with resource | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact resource.precommit
  · rfl
  · rfl

/-- If a rejected precommit computation reports a trap, a retained active
source segment and resolved target explain its precise bounds failure. -/
def PrecommitBoundsEvidence {M : Type} (view : M → Slice U8) (store : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (error : runtime.ExecError) : Prop :=
  ∀ trap, error = .Trap trap → ∃ (index : Usize) (inst : runtime.store.Instance),
    store.instances.val[index.val]? = some inst ∧ inst.module = module ∧
    PrecheckCause view store inst error

end Exec.Store
