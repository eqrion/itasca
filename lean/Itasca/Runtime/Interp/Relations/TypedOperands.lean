import Itasca.Runtime.Interp.ValueSlots
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Interp.Relations.Regions
import Itasca.Runtime.SourceMachine.Sim.Host
import Itasca.Runtime.SourceMachine.Sim.Control
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay
import Itasca.Runtime.SourceMachine.Numeric.Decode

/-!
Sections, each formerly its own module: Arguments, ExecutionLoop, TypeSlots, Marshal, Conditional, Unreachable, Capacity, ConstCodePoint, TypedOperands.
-/

/-! ## Arguments -/

section

/-! Argument checking tests scalar tags and the owning-store identity of
references. Address validity is a separate store/issued-handle invariant. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

noncomputable section
local instance : DecidableEq Itasca.wasm_types.ValueType := Classical.decEq _

def OwnedBy (id : Usize) : runtime.Value → Prop
  | .FuncRef (some address) => address.store = id
  | .ExternRef (some address) => address.store = id
  | _ => True

def ArgumentMatches (id : Usize) (value : runtime.Value) (ty : Itasca.wasm_types.ValueType) : Prop :=
  OwnedBy id value ∧ rawType value = ty

/-- Accepted arguments retain exactly their runtime type tags. -/
theorem argument_matches_rawtypes {id : Usize} {args : List runtime.Value} {types : List Itasca.wasm_types.ValueType}
    (matched : List.Forall₂ (ArgumentMatches id) args types) : types = args.map rawType := by
  induction matched with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, head.2, ih]

noncomputable def checkOwner (id : Usize) (value : runtime.Value) :
    core.result.Result Unit runtime.ExecError := by
  classical
  exact if OwnedBy id value then .Ok () else .Err .WrongStore

noncomputable def checkArgument (id : Usize) (value : runtime.Value)
    (ty : Itasca.wasm_types.ValueType) : core.result.Result Unit runtime.ExecError := by
  classical
  exact if OwnedBy id value then
    if rawType value = ty then .Ok () else .Err .BadArguments
  else .Err .WrongStore

noncomputable def checkArguments (id : Usize) : List runtime.Value → List Itasca.wasm_types.ValueType →
    core.result.Result Unit runtime.ExecError
  | [], [] => .Ok ()
  | value :: values, ty :: types =>
      match checkArgument id value ty with
      | .Ok _ => checkArguments id values types
      | .Err error => .Err error
  | _, _ => .Err .BadArguments

theorem check_argument_ok_iff (id : Usize) (value : runtime.Value) (ty : Itasca.wasm_types.ValueType) :
    checkArgument id value ty = .Ok () ↔ ArgumentMatches id value ty := by
  classical
  simp [checkArgument, ArgumentMatches]
  split <;> simp_all

theorem check_arguments_ok_iff (id : Usize) (values : List runtime.Value)
    (types : List Itasca.wasm_types.ValueType) :
    checkArguments id values types = .Ok () ↔ List.Forall₂ (ArgumentMatches id) values types := by
  induction values generalizing types with
  | nil => cases types <;> simp [checkArguments]
  | cons value values ih =>
    cases types with
    | nil => simp [checkArguments]
    | cons ty types =>
      simp only [checkArguments, List.forall₂_cons]
      have hok := check_argument_ok_iff id value ty
      cases hc : checkArgument id value ty with
      | Ok unit =>
        cases unit
        have hm : ArgumentMatches id value ty := hok.mp hc
        simpa [hm] using ih types
      | Err error => simp_all

@[step] theorem check_value_eq {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (value : runtime.Value) :
    runtime.store.Store.check_value memory store value ⦃ out => out = checkOwner store.id value ⦄ := by
  cases value <;> simp only [runtime.store.Store.check_value, checkOwner, OwnedBy]
  all_goals try simp
  all_goals cases ‹Option _› <;> simp [runtime.store.Store.check, checkOwner, OwnedBy]
  all_goals split <;> simp_all

@[step] theorem value_type_eq (value : runtime.Value) :
    runtime.Value.value_type value ⦃ out => out = rawType value ⦄ := by
  cases value <;> simp [runtime.Value.value_type, rawType]

theorem value_type_ne_eq (left right : Itasca.wasm_types.ValueType) :
    core.cmp.PartialEq.ne.trait_default wasm_types.ValueType.Insts.CoreCmpPartialEqValueType left right =
      .ok (if left = right then false else true) := by
  classical
  cases left <;> cases right <;>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, wasm_types.ValueType.Insts.CoreCmpPartialEqValueType,
      Itasca.wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

def checkSequence (first rest : core.result.Result Unit runtime.ExecError) :
    core.result.Result Unit runtime.ExecError :=
  match first with
  | .Ok _ => rest
  | .Err error => .Err error

@[step] theorem check_values_loop_effect {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
    (values : Slice runtime.Value) (types : Slice Itasca.wasm_types.ValueType)
    (position : Usize) (status : core.result.Result Unit runtime.ExecError)
    (lengths : values.length = types.length) (bound : position.val ≤ values.length) :
    runtime.interp.check_values_loop memory store values types position status
      ⦃ out => out = checkSequence status
        (checkArguments store.id (values.val.drop position.val) (types.val.drop position.val)) ⦄ := by
  unfold runtime.interp.check_values_loop
  apply loop.spec_decr_nat (fun p => values.length - p.1.val)
    (fun p => p.1.val ≤ values.length ∧
      checkSequence p.2 (checkArguments store.id (values.val.drop p.1.val) (types.val.drop p.1.val)) =
        checkSequence status (checkArguments store.id (values.val.drop position.val) (types.val.drop position.val)))
  · rintro ⟨index, current⟩ ⟨hi, hcheck⟩
    dsimp only at hi hcheck
    unfold runtime.interp.check_values_loop.body
    dsimp only
    split
    · have hv : index.val < values.val.length := by change index.val < values.length; scalar_tac
      have ht : index.val < types.val.length := by change index.val < types.length; scalar_tac
      cases current with
      | Err error => simpa [core.result.Result.is_ok, checkSequence] using hcheck
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        simp only [checkSequence] at hcheck
        rw [List.drop_eq_getElem_cons hv, List.drop_eq_getElem_cons ht] at hcheck
        step as ⟨value, hvalue⟩
        step with check_value_eq memory store value as ⟨result, hresult⟩
        subst result
        by_cases owned : OwnedBy store.id value
        · simp only [checkOwner, owned, ↓reduceIte, core.result.Result.is_ok, bind_ok]
          step with value_type_eq value as ⟨actualType, htype⟩
          subst actualType
          step as ⟨expectedType, hexpected⟩
          rw [value_type_ne_eq]
          split
          · rename_i matching
            simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok]
            step as ⟨next, hnext⟩
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            simpa [checkSequence, checkArguments, checkArgument, ← hvalue, ← hexpected,
              owned, matching, hnext] using hcheck
          · rename_i mismatch
            simp only [Bool.false_eq_true, ↓reduceIte, lift, bind_ok]
            step as ⟨next, hnext⟩
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            simpa [checkSequence, checkArguments, checkArgument, ← hvalue, ← hexpected,
              owned, mismatch] using hcheck
        · simp only [checkOwner, owned, ↓reduceIte, core.result.Result.is_ok, bind_ok, Bool.false_eq_true]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          simpa [checkSequence, checkArguments, checkArgument, ← hvalue, owned] using hcheck
    · have hend : index.val = values.length := by scalar_tac
      have htypes : index.val = types.length := by omega
      cases current with
      | Err error => simpa [checkSequence] using hcheck
      | Ok unit =>
        cases unit
        have hvdrop : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by change values.length ≤ index.val; omega)
        have htdrop : types.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by change types.length ≤ index.val; omega)
        simpa [checkSequence, hvdrop, htdrop, checkArguments] using hcheck
  · exact ⟨bound, rfl⟩

/-- The public checker rejects a length mismatch before inspecting any value;
otherwise it returns the first owner/tag error in argument order. -/
@[step] theorem check_values_effect {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
    (values : Slice runtime.Value) (types : Slice Itasca.wasm_types.ValueType) :
    runtime.interp.check_values memory store values types ⦃ out =>
      out = if values.length = types.length then checkArguments store.id values.val types.val
        else .Err .BadArguments ⦄ := by
  unfold runtime.interp.check_values
  by_cases he : values.length = types.length
  · have hlen : values.len = types.len := by scalar_tac
    simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    step with check_values_loop_effect memory store values types 0#usize (.Ok ()) he (by simp)
      as ⟨out, hout⟩
    simpa [he, checkSequence] using hout
  · have hlen : (values.len != types.len) = true := by scalar_tac
    simp [hlen, he]

/-- Accepted arguments have precisely the expected tags, and every non-null
reference carries the store's identity. This does not assume valid addresses. -/
theorem check_values_accepts_iff {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (store : runtime.store.Store M)
    (values : Slice runtime.Value) (types : Slice Itasca.wasm_types.ValueType) :
    runtime.interp.check_values memory store values types ⦃ out =>
      out = .Ok () ↔ List.Forall₂ (ArgumentMatches store.id) values.val types.val ⦄ := by
  step with check_values_effect memory store values types as ⟨out, hout⟩
  subst out
  split
  · exact check_arguments_ok_iff store.id values.val types.val
  · rename_i hn
    constructor
    · intro h; cases h
    · intro h
      exact False.elim (hn h.length_eq)

end
end Itasca.Runtime.Interp

end

/-! ## ExecutionLoop -/

section

/-! Actual execution-loop trace and safety composition. The body contract is a
local proof interface, to be discharged by the concrete instruction refinements. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

abbrev ExecutionState (M P : Type) :=
  runtime.interp.Execution × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError
abbrev ExecutionResult (M P : Type) :=
  Usize × alloc.vec.Vec U64 × alloc.vec.Vec runtime.interp.Frame × alloc.vec.Vec runtime.Value ×
    alloc.vec.Vec runtime.Value × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError

def finishExecution {M P : Type} (state : ExecutionState M P) : ExecutionResult M P :=
  (state.1.store, state.1.slots, state.1.frames, state.1.host_args, state.1.host_results,
    state.2.1, state.2.2.1, state.2.2.2)

def ActiveExecution {M P : Type} (state : ExecutionState M P) : Prop :=
  0 < state.1.frames.length ∧ state.2.2.2 = .Ok ()

variable {M P F A : Type}
  (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
  (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)

def executionBody (state : ExecutionState M P) :
    Result (ControlFlow (ExecutionState M P) (ExecutionResult M P)) :=
  runtime.interp.invoke_with_loop1.body memory hooks floats allocator
    state.1 state.2.1 state.2.2.1 state.2.2.2

/-- A running iteration invokes exactly one instruction step. -/
theorem execution_body_active (state : ExecutionState M P) (active : ActiveExecution state) :
    executionBody memory hooks floats allocator state = (do
      let (status, exec, store, platform) ← runtime.interp.step memory hooks floats allocator
        state.1 state.2.1 state.2.2.1
      .ok (.cont (exec, store, platform, status))) := by
  obtain ⟨frames, status⟩ := active
  have hframes : state.1.frames.len > 0#usize := by scalar_tac
  simp [executionBody, runtime.interp.invoke_with_loop1.body, hframes, status,
    core.result.Result.is_ok]

/-- Finite returns have exact concrete step histories; divergence is allowed,
and panic or out-of-bounds failure is excluded by the local step contract, which
may itself diverge. -/
theorem execution_loop_trace_safe
    (invariant : ExecutionState M P → Prop) (post : ExecutionResult M P → Prop)
    (stepSafe : ∀ exec store platform, invariant (exec, store, platform, .Ok ()) →
      0 < exec.frames.length →
      runtime.interp.step memory hooks floats allocator exec store platform
        ⦃ (status, exec', store', platform') => invariant (exec', store', platform', status) ⦄div)
    (finished : ∀ state, invariant state → ¬ActiveExecution state → post (finishExecution state))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError)
    (initial : invariant (exec, store, platform, status)) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator exec store platform status
      ⦃ result => ∃ count, NormalTrace (executionBody memory hooks floats allocator)
        count (exec, store, platform, status) result ∧ post result ⦄div := by
  change loop (executionBody memory hooks floats allocator) (exec, store, platform, status) ⦃ _ ⦄div
  apply loop_trace_dspec _ invariant post ?_ _ initial
  rintro ⟨current, currentStore, currentPlatform, currentStatus⟩ hinv
  unfold executionBody runtime.interp.invoke_with_loop1.body
  dsimp only
  split
  · have hframes : 0 < current.frames.length := by scalar_tac
    cases currentStatus with
    | Ok u =>
      cases u
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
      step with stepSafe current currentStore currentPlatform hinv hframes
      simpa only [WP.dspec_ok]
    | Err error =>
      have hp := finished (current, currentStore, currentPlatform, .Err error) hinv (by simp [ActiveExecution])
      simpa [core.result.Result.is_ok, finishExecution] using hp
  · have hframes : current.frames.length = 0 := by scalar_tac
    have hp := finished (current, currentStore, currentPlatform, currentStatus) hinv (by simp [ActiveExecution, hframes])
    simpa [finishExecution] using hp

/-- Every normal return stops at an invariant state with either no remaining
frames or a reported error. This is the outer-loop interface used by invocation. -/
theorem execution_loop_stops
    (invariant : ExecutionState M P → Prop)
    (stepSafe : ∀ exec store platform, invariant (exec, store, platform, .Ok ()) →
      0 < exec.frames.length →
      runtime.interp.step memory hooks floats allocator exec store platform
        ⦃ (status, exec', store', platform') => invariant (exec', store', platform', status) ⦄div)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError)
    (initial : invariant (exec, store, platform, status)) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator exec store platform status
      ⦃ result => ∃ state, invariant state ∧ ¬ActiveExecution state ∧ finishExecution state = result ⦄div := by
  apply WP.dspec_mono (execution_loop_trace_safe memory hooks floats allocator invariant
    (fun result => ∃ state, invariant state ∧ ¬ActiveExecution state ∧ finishExecution state = result)
    stepSafe (by intro state hi hs; exact ⟨state, hi, hs, rfl⟩)
    exec store platform status initial)
  rintro result ⟨count, trace, finalState⟩
  exact finalState

end Itasca.Runtime.Interp

end

/-! ## TypeSlots -/

section

/-! Signature slot counting terminates on arbitrary type sequences. Overflow is the
sole error, with an exact mathematical size witness. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def typeSlots (types : List Itasca.wasm_types.ValueType) : Nat :=
  Compiler.slots (types.map sourceType)

@[step] theorem type_slots_effect (types : Slice Itasca.wasm_types.ValueType) :
    runtime.interp.type_slots types ⦃ result =>
      match result with
      | .Ok amount => amount.val = typeSlots types.val
      | .Err error => error = .Exhausted .Values ∧ Usize.max < typeSlots types.val ⦄ := by
  unfold runtime.interp.type_slots
  step with value_type_slots types as ⟨slots, hs⟩
  cases slots <;> simpa [typeSlots, valueTypeSlots, core.option.Option.ok_or] using hs

end Itasca.Runtime.Interp

end

/-! ## Marshal -/

section

/-! API argument marshalling into the interpreter's live slot region. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem written_outside (words : List U64) (position index : Nat)
    (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (outside : index < position ∨ position + Compiler.width (sourceType ty) ≤ index) :
    (written words position ty lo hi)[index]? = words[index]? := by
  have hp : index ≠ position := by have := Compiler.width_positive (sourceType ty); omega
  unfold written
  split
  · rename_i hv
    have hh : index ≠ position + 1 := by simp only [hv, Compiler.width] at outside; omega
    simp [hp, hh]
  · simp [hp]

theorem written_represents (words : List U64) (position : Nat)
    (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (bound : position + Compiler.width (sourceType ty) ≤ words.length) :
    WordsAt (written words position ty lo hi) position (pairWords ty (lo, hi)) := by
  intro index hindex
  by_cases hv : sourceType ty = .V128
  · simp only [pairWords, hv, ↓reduceIte, List.length_cons, List.length_nil] at hindex
    have hhigh : position + 1 < words.length := by simp only [hv, Compiler.width] at bound; omega
    have hz : position < words.length := by omega
    have hj : index = 0 ∨ index = 1 := by omega
    rcases hj with rfl | rfl
    · exact ⟨by rw [written_length]; omega, by simp [pairWords, hv, written_low words position ty lo hi hz]⟩
    · exact ⟨by rw [written_length]; omega, by simp [pairWords, hv, written_high words position ty lo hi hv hhigh]⟩
  · have hw : Compiler.width (sourceType ty) = 1 := by cases ty <;> simp_all [sourceType, Compiler.width]
    have hz : position < words.length := by omega
    simp only [pairWords, hv, ↓reduceIte, List.length_cons, List.length_nil] at hindex
    have hj : index = 0 := by omega
    subst index
    exact ⟨by rw [written_length]; omega, by simp [pairWords, hv, written_low words position ty lo hi hz]⟩

/-- Writing one owned, representable argument establishes its source value
region and preserves every word outside that region. -/
@[step] theorem encode_slot_represents (slots : Slice U64) (position : Usize)
    (value : runtime.Value) (store : Usize) (owned : ValueOwnedFits store value)
    (bound : position.val + Compiler.width (sourceType (rawType value)) ≤ slots.length) :
    runtime.interp.encode_slot slots position (rawType value) value ⦃ after =>
      after.length = slots.length ∧
      WordsAt after.val position.val (Compiler.encodeValue (sourceValue value)) ∧
      ∀ index, index < position.val ∨ position.val + Compiler.width (sourceType (rawType value)) ≤ index →
        after.val[index]? = slots.val[index]? ⦄ := by
  obtain ⟨⟨lo, hi⟩, he, hwords⟩ := WP.spec_imp_exists (encode_value_spec value store owned)
  step with encode_slot_spec slots position (rawType value) value lo hi he bound as ⟨after, ha⟩
  refine ⟨?_, ?_, ?_⟩
  · change after.val.length = slots.val.length
    rw [ha, written_length]
  · rw [ha, ← hwords]
    exact written_represents slots.val position.val (rawType value) lo hi bound
  · intro index outside
    rw [ha]
    exact written_outside slots.val position.val index (rawType value) lo hi outside


def argumentWords (args : List runtime.Value) (count : Nat) : List Nat :=
  Compiler.encodeValues ((args.take count).map sourceValue)

theorem argument_words_step {args : List runtime.Value} {index : Nat} {value : runtime.Value}
    (lookup : args[index]? = some value) :
    argumentWords args (index + 1) = argumentWords args index ++ Compiler.encodeValue (sourceValue value) := by
  simp [argumentWords, List.take_add_one, lookup, Compiler.encode_values_append, Compiler.encodeValues]

theorem argument_words_bound (args : List runtime.Value) (count : Nat) :
    (argumentWords args count).length ≤ (Compiler.encodeValues (args.map sourceValue)).length := by
  rw [argumentWords, Compiler.encode_values_length, Compiler.encode_values_length]
  simp only [List.map_map, List.map_take]
  exact Compiler.offset_le _ _

@[step] theorem marshal_arguments_loop (words : alloc.vec.Vec U64)
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (index slot : Usize) (store : Usize)
    (typed : types.val = args.val.map rawType)
    (owned : ∀ value ∈ args.val, ValueOwnedFits store value)
    (bound : (Compiler.encodeValues (args.val.map sourceValue)).length ≤ words.length)
    (indexBound : index.val ≤ args.length)
    (position : slot.val = (argumentWords args.val index.val).length)
    (initialWords : WordsAt words.val 0 (argumentWords args.val index.val)) :
    runtime.interp.invoke_with_loop0 words args types index slot ⦃ after =>
      after.length = words.length ∧ ValuesAt after.val 0 (args.val.map sourceValue) ⦄ := by
  unfold runtime.interp.invoke_with_loop0
  apply loop.spec_decr_nat (fun p => args.length - p.2.1.val)
    (fun p => p.1.length = words.length ∧ p.2.1.val ≤ args.length ∧
      p.2.2.val = (argumentWords args.val p.2.1.val).length ∧
      WordsAt p.1.val 0 (argumentWords args.val p.2.1.val))
  · rintro ⟨current, i, offset⟩ ⟨hlen, hi, hoffset, hpref⟩
    dsimp only at hlen hi hoffset hpref
    unfold runtime.interp.invoke_with_loop0.body
    dsimp only
    split
    · have hib : i.val < args.val.length := by change i.val < args.length; scalar_tac
      have hit : i.val < types.length := by change i.val < types.val.length; rw [typed, List.length_map]; exact hib
      simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
      step as ⟨ty, hty⟩
      step as ⟨value, hvalue⟩
      have hlookup : args.val[i.val]? = some value := by simp [List.getElem?_eq_getElem hib, hvalue]
      have htype : ty = rawType value := by simpa [typed, ← hvalue] using hty
      have hnextWords := argument_words_step hlookup
      have hcapacity : offset.val + Compiler.width (sourceType (rawType value)) ≤ current.length := by
        have hb := argument_words_bound args.val (i.val + 1)
        rw [hnextWords, List.length_append, Compiler.encode_value_length, source_value_type] at hb
        omega
      have hv : ValueOwnedFits store value := owned value (by rw [hvalue]; exact List.getElem_mem hib)
      rw [htype]
      step with encode_slot_represents current.slice offset value store hv (by simpa only [alloc.vec.Vec.length, alloc.vec.Vec.val] using hcapacity)
        as ⟨after, hafterLen, hencoded, houtside⟩
      step with width_spec (rawType value) as ⟨width, hwidth⟩
      step as ⟨nextSlot, hnextSlot⟩
      step as ⟨next, hnext⟩
      refine ⟨?_, by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simpa [alloc.vec.Vec.val] using hafterLen.trans hlen
      · rw [hnext, hnextWords, List.length_append, Compiler.encode_value_length, source_value_type]
        scalar_tac
      · rw [hnext, hnextWords]
        apply WordsAt.append
        · apply hpref.congr_region hafterLen
          intro j hj
          apply houtside
          exact Or.inl (by omega)
        · simpa [hoffset, alloc.vec.Vec.val] using hencoded
    · have he : i.val = args.length := by scalar_tac
      have ht : args.val.take i.val = args.val := List.take_of_length_le (by change args.length ≤ i.val; omega)
      exact ⟨hlen, by simpa [ValuesAt, argumentWords, ht] using hpref⟩
  · exact ⟨rfl, indexBound, position, initialWords⟩


/-- The actual invocation argument loop produces the specification encoding
of every accepted argument, starting at slot zero. -/
@[step] theorem marshal_arguments (words : alloc.vec.Vec U64)
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (store : Usize) (typed : types.val = args.val.map rawType)
    (owned : ∀ value ∈ args.val, ValueOwnedFits store value)
    (bound : (Compiler.encodeValues (args.val.map sourceValue)).length ≤ words.length) :
    runtime.interp.invoke_with_loop0 words args types 0#usize 0#usize ⦃ after =>
      after.length = words.length ∧ ValuesAt after.val 0 (args.val.map sourceValue) ⦄ := by
  apply marshal_arguments_loop words args types 0#usize 0#usize store typed owned bound
  · simp
  · simp [argumentWords, Compiler.encodeValues]
  · intro j hj
    simp [argumentWords, Compiler.encodeValues] at hj

end Itasca.Runtime.Interp

end

/-! ## Conditional -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem JumpEffect.exact {before after : runtime.interp.Execution} {index : Usize}
    {raw : runtime.interp.Frame} {target : U32}
    (effect : JumpEffect before after index.val target)
    (lookup : before.frames.val[index.val]? = some raw) :
    after = { before with frames := before.frames.set index { raw with pc := target } } := by
  obtain ⟨found, foundAt, frames, unchanged⟩ := effect
  have same : found = raw := Option.some.inj (foundAt.symm.trans lookup)
  subst found
  have frameEq : after.frames = before.frames.set index { raw with pc := target } :=
    alloc.vec.Vec.ext _ _ (by simpa only [alloc.vec.Vec.set_val_eq] using frames)
  have exactState := congrArg (fun e : runtime.interp.Execution => { e with frames := after.frames }) unchanged
  change after = { before with frames := after.frames } at exactState
  simpa only [frameEq] using exactState

theorem dispatch_jump_if_zero_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (cond target : U32) (value : Nat)
    (lookup : exec.frames.val[index.val]? = some raw)
    (bound : value < 2 ^ 32)
    (input : WordsAt exec.slots.val (raw.base.val + cond.val) [value]) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.JumpIfZero cond target) ⦃ out => out.1 = .Ok () ∧
      out.2.1 = (if value = 0 then { exec with frames := exec.frames.set index { raw with pc := target } } else exec) ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  have frameBound : index.val < exec.frames.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have slotBound : raw.base.val + cond.val < exec.slots.length := by simpa using (input 0 (by simp)).1
  have bits : exec.slots.val[raw.base.val + cond.val]!.val = value := by simpa using (input 0 (by simp)).2
  have cast : (UScalar.cast .U32 exec.slots.val[raw.base.val + cond.val]!).val = value := by
    simp only [UScalar.cast_val_eq, UScalarTy.numBits, bits, Nat.mod_eq_of_lt bound]
  have zero : UScalar.cast .U32 exec.slots.val[raw.base.val + cond.val]! = 0#u32 ↔ value = 0 := by scalar_tac
  simp only [runtime.interp.dispatch]
  obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
    (jump_if_zero_effect exec index raw.base cond target frameBound slotBound)
  simp only [zero] at effect
  have exactState : out.2 = (if value = 0 then { exec with frames := exec.frames.set index { raw with pc := target } } else exec) := by
    by_cases equal : value = 0
    · simp only [if_pos equal] at effect ⊢
      exact effect.exact lookup
    · simpa only [if_neg equal] using effect
  rw [result, bind_ok]
  rcases out with ⟨answer, nextExec⟩
  with_unfolding_all apply WP.spec.ret
  exact ⟨success, exactState, rfl, rfl⟩

/-- A guarded branch with an operand transfer first removes its condition.
The false path skips the transfer/jump pair; the true path reaches BR. -/
theorem dispatch_branch_guard_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (cond target : U32) (value : Nat)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (front : List val)
    (lookup : exec.frames.val[index.val]? = some raw)
    (bound : value < 2 ^ 32)
    (position : cond.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩)
    (slots : FrameSlots exec raw { f with vals := front ++ [SourceMachine.integerVal .I32 value] }) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.JumpIfZero cond target) ⦃ out => out.1 = .Ok () ∧
      out.2.1 = (if value = 0 then { exec with frames := exec.frames.set index { raw with pc := target } } else exec) ∧
      FrameSlots out.2.1 raw { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      SourceMachine.NextSim
        ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩
        ⟨s, ambient, { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } :: rest, []⟩ ⦄ := by
  have allValues : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ [SourceMachine.integerVal .I32 value]) := by
    simpa only [FrameSlots, List.append_assoc] using slots
  have input : WordsAt exec.slots.val (raw.base.val + cond.val) [value] := by
    simpa only [position, ValuesAt, Compiler.encodeValues, List.flatMap_cons, List.flatMap_nil,
      SourceMachine.integerVal, Compiler.encodeValue, List.append_nil] using allValues.operands
  have step : SourceMachine.astep
      ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩ = .next
      ⟨s, ambient, { f with code := if value = 0 then after else .BR (.mk_uN depth) :: after, vals := front } :: rest, []⟩ := by
    have hb : value < 4294967296 := bound
    simp [SourceMachine.astep, SourceMachine.pop_append, SourceMachine.integerVal, SourceMachine.integer, numtype_Inn, hb, SourceMachine.advance]
  have simulation := SourceMachine.instruction_simulation s ambient { f with vals := front ++ [SourceMachine.integerVal .I32 value] } rest
    (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed step
  apply WP.spec_mono (dispatch_jump_if_zero_exact memory hooks floats allocator exec store platform index raw cond target value lookup bound input)
  intro out effect
  obtain ⟨success, exactState, sameStore, samePlatform⟩ := effect
  refine ⟨success, exactState, ?_, sameStore, samePlatform, simulation⟩
  rw [exactState]
  split <;> exact allValues.locals

theorem dispatch_jump_if_non_zero_exact {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (cond target : U32) (value : Nat)
    (lookup : exec.frames.val[index.val]? = some raw)
    (bound : value < 2 ^ 32)
    (input : WordsAt exec.slots.val (raw.base.val + cond.val) [value]) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index
      raw.instance raw.function raw.base (.JumpIfNonZero cond target) ⦃ out => out.1 = .Ok () ∧
      out.2.1 = (if value = 0 then exec else { exec with frames := exec.frames.set index { raw with pc := target } }) ∧
      out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  have frameBound : index.val < exec.frames.length := List.getElem?_eq_some_iff.mp lookup |>.1
  have slotBound : raw.base.val + cond.val < exec.slots.length := by simpa using (input 0 (by simp)).1
  have bits : exec.slots.val[raw.base.val + cond.val]!.val = value := by simpa using (input 0 (by simp)).2
  have cast : (UScalar.cast .U32 exec.slots.val[raw.base.val + cond.val]!).val = value := by
    simp only [UScalar.cast_val_eq, UScalarTy.numBits, bits, Nat.mod_eq_of_lt bound]
  have zero : UScalar.cast .U32 exec.slots.val[raw.base.val + cond.val]! = 0#u32 ↔ value = 0 := by scalar_tac
  simp only [runtime.interp.dispatch]
  obtain ⟨out, result, success, effect⟩ := WP.spec_imp_exists
    (jump_if_non_zero_effect exec index raw.base cond target frameBound slotBound)
  simp only [zero] at effect
  have exactState : out.2 = (if value = 0 then exec else { exec with frames := exec.frames.set index { raw with pc := target } }) := by
    by_cases equal : value = 0
    · simp only [if_pos equal] at effect ⊢
      exact effect
    · simp only [if_neg equal] at effect ⊢
      exact effect.exact lookup
  rw [result, bind_ok]
  rcases out with ⟨answer, nextExec⟩
  with_unfolding_all apply WP.spec.ret
  exact ⟨success, exactState, rfl, rfl⟩


end Itasca.Runtime.Interp

end

/-! ## Unreachable -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem dispatch_unreachable_eq {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base .Unreachable =
      .ok (.Err (.Trap .Unreachable), exec, store, platform) := by
  simp [runtime.interp.dispatch, runtime.interp.execute_unreachable, core.convert.IntoFrom.into,
    runtime.ExecError.Insts.CoreConvertFromTrap.from]

/-- The actual explicit trap has a positive counted SpecTec derivation through
all active labels and suspended frames, preserving the concrete store. -/
theorem step_unreachable_refines {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (pcBound : raw.pc.val < U32.max)
    (fetched : compiled.code.val[raw.pc.val]? = some .Unreachable)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Err (.Trap .Unreachable) ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        out.2.1 = { exec with frames := exec.frames.set index { raw with pc := pc } }) ∧
      ∃ n, 0 < n ∧ Spec.StepsHN n
        (SourceMachine.decode ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) []
        ⟨⟨s, ambient⟩, [.TRAP]⟩ ⦄ := by
  have frameTyped : SourceMachine.FrameTyped s { f with code := .UNREACHABLE :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  obtain ⟨wf, labels, values, code⟩ := SourceMachine.frame_typed_wf frameTyped
  have remaining : Forall SourceMachine.FrameWf rest := by
    cases typed.frames with | cons _ h => exact SourceMachine.frames_typed_wf h
  have simulation := SourceMachine.unreachable_simulation s ambient f rest after typed.store typed.ambient wf labels values
    (fun i hi => code i (by simp [hi])) remaining
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    .Unreachable last hf hi hc fetched pcBound
  intro pc hpc
  rw [dispatch_unreachable_eq]
  exact ⟨rfl, rfl, rfl, ⟨pc, hpc, rfl⟩, simulation⟩

end Itasca.Runtime.Interp

end

/-! ## Capacity -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A represented region ends within storage, including an empty region at a
known valid base. -/
theorem WordsAt.end_le {words : List U64} {base : Nat} {bits : List Nat}
    (represented : WordsAt words base bits) (start : base ≤ words.length) :
    base + bits.length ≤ words.length := by
  by_cases empty : bits.length = 0
  · omega
  · have last := (represented (bits.length - 1) (by omega)).1
    omega

/-- The allocated capacity is for the function actually selected by the frame. -/
theorem FrameBinding.capacity {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (instanceLookup : store.instances.val[raw.instance.val]? = some inst)
    (functionLookup : inst.module.functions.val[raw.function.val]? = some compiled) :
    raw.base.val + compiled.slot_count.val ≤ exec.slots.length := by
  obtain ⟨actual, fn, actualCode, signature, _, _, hi, _, _, hc, _, _, _, _, capacity⟩ := binding
  have same : actual = inst := Option.some.inj (hi.symm.trans instanceLookup)
  subst actual
  have sameCode : actualCode = compiled := Option.some.inj (hc.symm.trans functionLookup)
  exact sameCode ▸ capacity

theorem FrameBinding.base_bound {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (binding : FrameBinding store exec raw source) : raw.base.val ≤ exec.slots.val.length := by
  obtain ⟨_, _, compiled, _, _, _, _, _, _, _, _, _, _, _, capacity⟩ := binding
  change raw.base.val + compiled.slot_count.val ≤ exec.slots.val.length at capacity
  omega

/-- Live-value capacity follows from representation and frame allocation. -/
theorem FrameSlots.capacity {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : SourceMachine.AFrame}
    (represented : FrameSlots exec raw source) (binding : FrameBinding store exec raw source) :
    raw.base.val + Compiler.slots ((source.locals ++ source.vals).map Compiler.valueType) ≤ exec.slots.length := by
  have bound := represented.end_le binding.base_bound
  simpa only [Compiler.encode_values_length] using bound

end Itasca.Runtime.Interp

end

/-! ## ConstCodePoint -/

section

namespace Itasca.Runtime.Interp
open Aeneas.Std

theorem linear_emission_const32_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (value : U32)
    (h : Compiler.LinearEmission locals before
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))) emitted after) :
    ∃ dst,
      emitted = [.Const32 dst value] ∧ after = before ++ [.I32] ∧
      dst.val = Compiler.slots locals + Compiler.slots before := by
  generalize equality : instr.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) = instruction at h
  cases h with
  | const32 stack dst word position =>
    simp only [instr.CONST.injEq, num_.mk_num__0.injEq, uN.mk_uN.injEq, and_self_left] at equality
    have same : word = value := by scalar_tac
    subst word
    exact ⟨dst, rfl, rfl, position⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Compiler.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decode_instruction_source, SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => simp_all

theorem linear_emission_const64_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (value : U64)
    (h : Compiler.LinearEmission locals before
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))) emitted after) :
    ∃ dst,
      emitted = [.Const64 dst value] ∧ after = before ++ [.I64] ∧
      dst.val = Compiler.slots locals + Compiler.slots before := by
  generalize equality : instr.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) = instruction at h
  cases h with
  | const64 stack dst word position =>
    simp only [instr.CONST.injEq, num_.mk_num__0.injEq, uN.mk_uN.injEq, and_self_left] at equality
    have same : word = value := by scalar_tac
    subst word
    exact ⟨dst, rfl, rfl, position⟩
  | binary stack ity op left right hl hr => cases op <;> simp_all [Compiler.IntegerBinary.source]
  | numeric stack op a b ha hb =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decode_instruction_source, SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => simp_all

end Itasca.Runtime.Interp

end

/-! ## TypedOperands -/

section

namespace Itasca.Runtime.Interp

/-- Static integer operand types and generated source value typing determine
actual integer tags, bit bounds, and the untouched prefix. -/
theorem frame_integer_suffix {s : store} {frame : SourceMachine.AFrame} {incoming : List valtype}
    (typed : SourceMachine.FrameTyped s frame incoming) (frontTypes : List valtype) (ty : Inn)
    (shape : frame.vals.map Compiler.valueType = frontTypes ++ [Compiler.integerType ty]) :
    ∃ front bits,
      frame.vals = front ++ [SourceMachine.integerVal ty bits] ∧ front.map Compiler.valueType = frontTypes ∧
      bits < 2 ^ SourceMachine.integerWidth ty := by
  cases typed with
  | mk C bindings localTypes locals values returns code wf =>
    have types : frame.vals.map SourceMachine.valueType = frontTypes ++ [Compiler.integerType ty] := by
      simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using shape
    rw [types] at values
    obtain ⟨front, operands, split, frontTyped, operandsTyped⟩ := SourceMachine.results_typed_split values
    cases operandsTyped with
    | cons valueTyped tail =>
      cases tail
      have typeEq : Compiler.integerType ty = valtype_numtype (numtype_Inn ty) := by cases ty <;> rfl
      rw [typeEq] at valueTyped
      obtain ⟨bits, valueEq, bound⟩ := SourceMachine.integer_val_inv valueTyped
      subst_vars
      refine ⟨front, bits, split, ?_, bound⟩
      simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs] using SourceMachine.results_type_of_typed frontTyped

end Itasca.Runtime.Interp

end
