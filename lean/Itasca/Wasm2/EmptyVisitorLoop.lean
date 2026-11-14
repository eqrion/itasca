import Itasca.Wasm2.TableAdapters
import Itasca.Handler.SimplePrefix
import Itasca.Support.Result
import Itasca.Binary.Wasm1.EncodingComplete

/-!
Sections, each formerly its own module: ResultStack, ResultStackSemantics, Suffix, Prefix, EmptyVisitorLoop.
-/

/-! ## ResultStack -/

section

/-!
# Descriptor stack operations

Specs of the extracted operand-stack operations that take a `signature.ResultType` descriptor:
`code.check_func_type`, `code.push_results` and `code.pop_results`. `push_results.spec` and
`pop_results.concrete` and `.polymorphic` describe their effect on the stack for a resolved
descriptor, and the semantic and totality statements are in `Wasm2/ResultStackSemantics`.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.check_func_type` accepts exactly the function types within the parameter and result
limits and reports which limit is exceeded otherwise. -/
@[step]
theorem code.check_func_type.spec (ft : wasm_types.FuncType) :
    code.check_func_type ft ⦃ r =>
      match r with
      | .Ok _ => ft.params.val.length ≤ 1000 ∧ ft.results.val.length ≤ 1000
      | .Err .TooManyParams => 1000 < ft.params.val.length
      | .Err .TooManyResults => 1000 < ft.results.val.length
      | .Err _ => False ⦄ := by
  unfold code.check_func_type
  simp only [limits.MAX_MULTI_VALUE_PARAMS, limits.MAX_MULTI_VALUE_RESULTS]
  step*

/-- Pushing a resolved descriptor has exactly the shared stack primitive's
    effect, with no intermediate runtime vector. -/
theorem code.push_results.spec (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (ts : List wasm_types.ValueType)
    (hts : Wasm2.resolve env view = some ts)
    (hcap : st.vals.val.length + ts.length ≤ Usize.max) :
    code.push_results st env view ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = st.vals.val ++ ts.map code.StackType.Val ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨r, hr, ht⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  cases r with
  | Err e => simp [hts] at ht
  | Ok n =>
    obtain ⟨ts', he, hn⟩ := ht
    have heq : ts' = ts := by simpa [hts] using he.symm
    subst ts'
    unfold code.push_results
    rw [hr]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step
    split
    · scalar_tac
    · cases view with
      | Empty => simp_all [Wasm2.resolve]
      | One t =>
        simp [Wasm2.resolve] at hts
        subst ts
        step*
        all_goals simp_all
      | «Type» index part =>
        by_cases hi : index.val < env.types.val.length
        · cases part <;> simp [Wasm2.resolve, List.getElem?_eq_getElem hi] at hts
          all_goals subst ts
          all_goals step*
          all_goals simp_all [alloc.vec.Vec.deref]
        · simp [Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

end Itasca

end

/-! ## ResultStackSemantics -/

section

/-!
# Descriptor stack operations, semantics and totality

Semantic specs of `code.pop_results` and `code.push_results`. `code.pop_results.realizes` relates
a successful pop to the backward stack interpretation, `.complete` gives acceptance from
independent stack compatibility, and `.total` and `code.push_results.total` show that neither
panics or diverges on arbitrary descriptors and environments.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Descriptor pops preserve the backward stack interpretation, including
mixed concrete/`Bot` stacks and implicit operands at an unreachable base. -/
theorem code.pop_results.realizes (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (expected : List wasm_types.ValueType)
    (outer segment : List code.StackType)
    (hts : Wasm2.resolve env view = some expected)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_results st env view ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        (r.1 = .Ok () → ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
          Sequence.Realizes (Control.polymorphic st) segment
            (ts ++ expected.map Translate.valueType)) ⦄ := by
  cases view with
  | Empty =>
    simp [Wasm2.resolve] at hts
    subst expected
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, segment, hvals, le_refl _, by simp⟩
  | One t =>
    simp [Wasm2.resolve] at hts
    subst expected
    obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hl, ht⟩ := WP.spec_imp_exists
      (code.pop_with_type.realizes st outer segment t hvals hbase)
    cases res <;> simp [code.pop_results, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · exact ⟨hc, hp, rest, hv, hl, ht.2⟩
    · exact ⟨hc, hp, rest, hv, hl⟩
  | «Type» index part =>
    by_cases hi : index.val < env.types.val.length
    · cases part <;> simp [Wasm2.resolve, List.getElem?_eq_getElem hi] at hts
      all_goals subst expected
      all_goals unfold code.pop_results
      all_goals step
      all_goals split
      all_goals first | scalar_tac | skip
      all_goals step
      all_goals step with code.pop_types.realizes st outer segment _ hvals hbase
      all_goals simp_all [alloc.vec.Vec.deref]
      all_goals intro hok; simpa [hok] using r_post4
    · simp [Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

/-- Independent stack compatibility suffices for descriptor-pop acceptance. -/
theorem code.pop_results.complete (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (expected : List wasm_types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype)
    (hts : Wasm2.resolve env view = some expected)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (ts ++ expected.map Translate.valueType)) :
    code.pop_results st env view ⦃ r =>
      r.1 = .Ok () ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        Sequence.Realizes (Control.polymorphic st) rest ts ⦄ := by
  cases view with
  | Empty =>
    simp [Wasm2.resolve] at hts
    subst expected
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, trivial, segment, hvals, le_refl _, by simpa using ht⟩
  | One t =>
    simp [Wasm2.resolve] at hts
    subst expected
    obtain ⟨v, s, rest, hr, hc, hp, hv, hl, _, ht'⟩ :=
      code.pop_with_type.complete st outer segment ts t hvals hbase (by simpa using ht)
    simpa [code.pop_results, hr, core.result.Result.Insts.CoreOpsTry.branch]
      using And.intro hc (And.intro hp ⟨rest, hv, hl, ht'⟩)
  | «Type» index part =>
    by_cases hi : index.val < env.types.val.length
    · cases part <;> simp [Wasm2.resolve, List.getElem?_eq_getElem hi] at hts
      all_goals subst expected
      all_goals unfold code.pop_results
      all_goals step
      all_goals split
      all_goals first | scalar_tac | skip
      all_goals step
      all_goals first
        | step with code.pop_types.complete st outer segment ts (alloc.vec.Vec.deref ft.params) hvals hbase (by simpa [alloc.vec.Vec.deref, ft_post, r_post] using ht)
        | step with code.pop_types.complete st outer segment ts (alloc.vec.Vec.deref ft.results) hvals hbase (by simpa [alloc.vec.Vec.deref, ft_post, r_post] using ht)
      all_goals simp_all
    · simp [Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

/-- No descriptor, including an invalid type index, can make a bounded pop
panic or diverge. Frame bounds are preserved even on rejection. -/
@[step]
theorem code.pop_results.total (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (hshape : Control.Shape st) :
    code.pop_results st env view ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
        r.2.vals.val.length ≤ st.vals.val.length ⦄ := by
  cases view with
  | Empty => simp [code.pop_results, hshape]
  | One t =>
    unfold code.pop_results
    step with code.pop_with_type.total st t hshape
    step*
  | «Type» index part =>
    unfold code.pop_results
    step
    split
    · simp [hshape]
    · cases part <;> step
      all_goals step with code.pop_types.total st _ hshape
      all_goals simp_all

/-- The explicit capacity guard makes descriptor pushes total for arbitrary
environments, including invalid descriptors and oversized stored signatures. -/
@[step]
theorem code.push_results.total (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (hshape : Control.Shape st) :
    code.push_results st env view ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      (r.1 = .Ok () → ∃ ts, Wasm2.resolve env view = some ts ∧
        r.2.vals.val = st.vals.val ++ ts.map code.StackType.Val) ⦄ := by
  obtain ⟨res, hr, hs⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  cases res with
  | Err e =>
    simp [code.push_results, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hshape]
  | Ok n =>
    obtain ⟨ts, hts, hn⟩ := hs
    by_cases hcap : st.vals.val.length + ts.length ≤ Usize.max
    · obtain ⟨⟨r, s⟩, hrun, hok, hv, hc, hp⟩ := WP.spec_imp_exists
        (code.push_results.spec st env view ts hts hcap)
      rw [hrun, WP.spec_ok]
      refine ⟨hshape.replace_operands hc ?_, hc, hp, fun _ => ⟨ts, hts, hv⟩⟩
      have hb := hshape.base_le
      simp only [hv, List.length_append, List.length_map]
      omega
    · unfold code.push_results
      rw [hr]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step
      split
      · simp [hshape]
      · scalar_tac

end Itasca

end

/-! ## Suffix -/

section

/-!
# Operand suffix compatibility

The non-destructive operand check that `br_table` applies to each target. `Wasm2.Fits`
and `Wasm2.Suffix` independently specify that the top of an operand stack is compatible with a
signature, `code.check_suffix_loop.spec` is the exact contract of the extracted loop, and
`code.check_suffix.spec` and `.complete` give soundness, totality and completeness of
`code.check_suffix`.
-/

open Aeneas Aeneas.Std

set_option maxRecDepth 2048

namespace Itasca.Wasm2

/-- Compatibility from the top of an operand stack downwards. Each target is
compared to the original operands; a `Bot` is never specialized to one target. -/
def Fits : Bool → List code.StackType → List wasm_types.ValueType → Prop
  | _, _, [] => True
  | poly, [], _ :: _ => poly = true
  | poly, v :: vs, t :: ts =>
      Sequence.Accepts v (Translate.valueType t) ∧ Fits poly vs ts

@[simp] theorem Fits.nil (poly : Bool) (vs : List code.StackType) : Fits poly vs [] := by
  cases vs <;> trivial

@[simp] theorem Fits.unreachable (ts : List wasm_types.ValueType) : Fits true [] ts := by
  cases ts <;> trivial

/-- Independent compatibility of a signature with the current operand suffix. -/
def Suffix (st : code.OpIterState) (ts : List wasm_types.ValueType) : Prop :=
  Fits (Control.polymorphic st)
    (st.vals.val.drop (Control.base st).val).reverse ts.reverse

end Itasca.Wasm2

namespace Itasca

/-- Exact loop contract: rejection is equivalent to incompatibility of the
remaining signature with the unchanged stack slice. -/
theorem code.check_suffix_loop.spec (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (ts : List wasm_types.ValueType)
    (hts : Wasm2.resolve env view = some ts) (stack i : Usize)
    (hb : (Control.base st).val ≤ stack.val) (hs : stack.val ≤ st.vals.val.length)
    (hi : i.val ≤ ts.length) :
    code.check_suffix_loop st.vals st.ctrls st.pos env view (Control.base st) stack i ⦃ r =>
      r = .Ok () ↔ Wasm2.Fits (Control.polymorphic st)
        ((st.vals.val.take stack.val).drop (Control.base st).val).reverse
        (ts.take i.val).reverse ⦄ := by
  unfold code.check_suffix_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => (Control.base st).val ≤ p.1.val ∧ p.1.val ≤ st.vals.val.length ∧
      p.2.val ≤ ts.length ∧
      (Wasm2.Fits (Control.polymorphic st)
          ((st.vals.val.take stack.val).drop (Control.base st).val).reverse
          (ts.take i.val).reverse ↔
        Wasm2.Fits (Control.polymorphic st)
          ((st.vals.val.take p.1.val).drop (Control.base st).val).reverse
          (ts.take p.2.val).reverse))
  · rintro ⟨s, j⟩ ⟨hb', hs', hj, he⟩
    dsimp only at hb' hs' hj he
    unfold code.check_suffix_loop.body
    dsimp only
    split
    · rename_i hz
      simpa [hz] using he.symm
    · rename_i hnz
      step
      have hj' : i2.val < ts.length := by omega
      have hjstep : j.val = i2.val + 1 := by omega
      have ht : (ts.take j.val).reverse = ts[i2.val] :: (ts.take i2.val).reverse := by
        rw [hjstep, List.take_succ_eq_append_getElem hj']
        simp
      rw [signature.ResultType.get.complete view env ts hts i2]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        List.getElem?_eq_getElem hj']
      split
      · rename_i hbase
        have hempty : ((st.vals.val.take s.val).drop (Control.base st).val).reverse = [] := by
          rw [hbase]
          simp
        step with code.cur_polymorphic.spec st
        subst b
        split
        · rename_i hpoly
          simp only [WP.spec_ok]
          refine ⟨hb', hs', by omega, ?_, by omega⟩
          simpa [hempty, ht, hpoly, Wasm2.Fits] using he
        · rename_i hpoly
          simp only [WP.spec_ok]
          simpa [hempty, ht, Wasm2.Fits, hpoly] using he.symm
      · rename_i hbase
        have hbne : s.val ≠ (Control.base st).val := fun h => hbase (UScalar.eq_of_val_eq h)
        step
        have hidx : stack1.val < st.vals.val.length := by omega
        have hbstep : (Control.base st).val ≤ stack1.val := by omega
        have hsstep : s.val = stack1.val + 1 := by omega
        have hv : ((st.vals.val.take s.val).drop (Control.base st).val).reverse =
            st.vals.val[stack1.val] ::
              ((st.vals.val.take stack1.val).drop (Control.base st).val).reverse := by
          rw [hsstep, List.take_succ_eq_append_getElem hidx,
            List.drop_append_of_le_length (by simp; omega)]
          simp
        step as ⟨operand, hop⟩
        rw [hop]
        clear hop
        split
        · rename_i actual hactual
          step with core.cmp.PartialEq.ne.trait_default.spec
            wasm_types.ValueType.Insts.CoreCmpPartialEqValueType _ _ (wasm_types.ValueType.eq_spec _ _)
            as ⟨different, hdifferent⟩
          split
          · rename_i hne
            have hbad : Translate.valueType actual ≠ Translate.valueType ts[i2.val] :=
              fun h => (hdifferent.mp hne) (Translate.valueType_injective h)
            simp only [WP.spec_ok]
            simpa [hv, ht, hactual, Wasm2.Fits, Sequence.Accepts, eq_comm, hbad] using he.symm
          · rename_i heq
            have hequal : actual = ts[i2.val] := by simpa [heq] using hdifferent
            simp only [WP.spec_ok]
            refine ⟨hbstep, by omega, by omega, ?_, by omega⟩
            simpa [hv, ht, hactual, Wasm2.Fits, Sequence.Accepts, eq_comm, hequal] using he
        · rename_i hbot
          simp only [WP.spec_ok]
          refine ⟨hbstep, by omega, by omega, ?_, by omega⟩
          simpa [hv, ht, hbot, Wasm2.Fits, Sequence.Accepts] using he
  · exact ⟨hb, hs, hi, Iff.rfl⟩

/-- The actual non-destructive suffix checker is total, sound, and complete
for the independently specified operand compatibility relation. -/
theorem code.check_suffix.spec (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (hshape : Control.Shape st) :
    code.check_suffix st env view ⦃ r =>
      r = .Ok () ↔ ∃ ts, Wasm2.resolve env view = some ts ∧ Wasm2.Suffix st ts ⦄ := by
  unfold code.check_suffix
  step with code.cur_base.spec st
  subst base
  obtain ⟨r, hr, ht⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  rw [hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ht.2]
  | Ok n =>
    obtain ⟨ts, hts, hn⟩ := ht
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_mono (code.check_suffix_loop.spec st env view ts hts
      (alloc.vec.Vec.len st.vals) n hshape.base_le (by simp) (by omega))
    intro res hs
    simpa [hts, hn, Wasm2.Suffix] using hs

end Itasca

end

/-! ## Prefix -/

section

/-!
# Typed instruction prefixes

`TypedPrefix` says that the instructions read so far in a frame are well formed and typed by the
generated `Instrs_ok` rules for every interpretation of the current operand stack. `ResumePrefix`
is the form kept for a suspended parent frame. `TypedPrefix.append` extends a prefix by one typed
instruction, and `ResumePrefix.finish` appends the finished child construct to a suspended
parent.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A frame starts with its parameter vector. Function bodies use the empty
vector because function parameters are locals, not initial operands. -/
structure TypedPrefix (C : context) (inputs : List valtype) (ops : List instr)
    (poly : Bool) (vals : List code.StackType) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Sequence.Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list inputs) (.mk_list ts))

/-- A frame with no instructions is a typed prefix of its parameter vector. -/
theorem TypedPrefix.start (C : context) (hC : wf_context C) (inputs : List wasm_types.ValueType) :
    TypedPrefix C (inputs.map Translate.valueType) [] false
      (inputs.map code.StackType.Val) := by
  constructor
  · simp [Forall]
  · intro ts ht
    obtain ⟨pre, hp, rfl⟩ := (Sequence.realizes_append_concrete false [] inputs ts).mp
      (by simpa using ht)
    have he := (Sequence.realizes_empty pre).mp hp
    subst pre
    simpa using Instrs_ok.frame C [] (inputs.map Translate.valueType) [] []
      (.empty C hC) hC (by simp [Forall])

/-- Appending a typed instruction to a typed prefix gives a typed prefix. -/
theorem TypedPrefix.append {C inputs ops poly poly' vals vals'}
    (h : TypedPrefix C inputs ops poly vals) (hC : wf_context C)
    (op : instr) (hwf : wf_instr op)
    (hstep : ∀ out, Sequence.Realizes poly' vals' out →
      ∃ before, Sequence.Realizes poly vals before ∧
        Instrs_ok C [op] (.mk_functype (.mk_list before) (.mk_list out))) :
    TypedPrefix C inputs (ops ++ [op]) poly' vals' := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro out hout
    obtain ⟨before, hin, hop⟩ := hstep out hout
    exact .seq C ops [op] inputs out before (h.typed before hin) hop hC
      h.wellFormed (by simpa [Forall] using hwf)

/-- A suspended parent remembers the child's parameters and, for if, its i32
condition, even though those operands have been popped from the physical stack. -/
structure ResumePrefix (C : context) (inputs : List valtype) (ops : List instr)
    (poly : Bool) (vals : List code.StackType) (args : List valtype) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Sequence.Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list inputs) (.mk_list (ts ++ args)))

/-- Popping the child's arguments from a typed prefix gives the parent's resume prefix. -/
theorem ResumePrefix.after_pop {C inputs ops poly before after args}
    (h : TypedPrefix C inputs ops poly before)
    (hpop : ∀ ts, Sequence.Realizes poly after ts →
      Sequence.Realizes poly before (ts ++ args)) :
    ResumePrefix C inputs ops poly after args :=
  ⟨h.wellFormed, fun ts ht => h.typed _ (hpop ts ht)⟩

/-- A finished child construct typed from the saved arguments to its results extends the suspended
parent to a typed prefix. -/
theorem ResumePrefix.finish {C inputs ops poly vals args}
    (h : ResumePrefix C inputs ops poly vals args) (hC : wf_context C)
    (op : instr) (results : List wasm_types.ValueType) (hwf : wf_instr op)
    (hop : Instr_ok C op
      (.mk_functype (.mk_list args) (.mk_list (results.map Translate.valueType)))) :
    TypedPrefix C inputs (ops ++ [op]) poly (vals ++ results.map code.StackType.Val) := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro ts ht
    obtain ⟨pre, hp, rfl⟩ := (Sequence.realizes_append_concrete poly vals results ts).mp ht
    exact .seq C ops [op] inputs (pre ++ results.map Translate.valueType) (pre ++ args)
      (h.typed pre hp)
      (.frame C [op] pre args (results.map Translate.valueType)
        (.instr C op args _ hop hC hwf) hC (by simpa [Forall] using hwf))
      hC h.wellFormed (by simpa [Forall] using hwf)

end Itasca.Wasm2

end

/-! ## EmptyVisitorLoop -/

section

/-!
# Body loop with the empty visitor

Proof-side views of the extracted visiting loop `code.body_loop_loop` instantiated with
`code.EmptyOpVisitor`. `Wasm2.emptyVisitorLoop.body` drops the visitor from the loop body,
`Wasm2.emptyVisitorLoop.body_eq` relates it to the extracted body, and `code.bodyCore` is the
visitor-free body validator.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca

/-- One iteration of the extracted loop body with the visitor argument kept only as a pass-through
value, so semantic proofs do not track the empty visitor. -/
def Wasm2.emptyVisitorLoop.body
  (data : Slice U8) (env : metadata.Env) (type_index : U32)
  (locals : alloc.vec.Vec wasm_types.ValueType)
  (results : alloc.vec.Vec wasm_types.ValueType)
  (st : code.BodyState)
  (visitor : code.EmptyOpVisitor) :
  Result (ControlFlow (code.BodyState ×
    code.EmptyOpVisitor) (core.result.Result Unit
    error.OpError))
  := do
  let b ← alloc.vec.Vec.is_empty Global st.blocks
  if b
  then
    let i2 := Slice.len data
    if st.core.pos != i2
    then ok (done (core.result.Result.Err error.OpError.TrailingBytes))
    else ok (done (core.result.Result.Ok ()))
  else
    let r ← reader.read_byte data st.core.pos
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue (op, «end») =>
      match op with
      | 2#uscalar =>
        let (r1, st1) ←
          code.enter { st with core := { st.core with pos := «end» } }
            data
            env code.LabelKind.Block
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 3#uscalar =>
        let (r1, st1) ←
          code.enter { st with core := { st.core with pos := «end» } }
            data
            env code.LabelKind.Loop
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 4#uscalar =>
        let (r1, st1) ←
          code.enter { st with core := { st.core with pos := «end» } }
            data
            env code.LabelKind.Then
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 5#uscalar =>
        let (r1, st1) ←
          code.end_frame
            { st with core := { st.core with pos := «end» } }
            env true
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 11#uscalar =>
        let (r1, st1) ←
          code.end_frame
            { st with core := { st.core with pos := «end» } }
            env false
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 12#uscalar =>
        let (r1, st1) ←
          code.branch
            { st with core := { st.core with pos := «end» } } data
            env false
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 13#uscalar =>
        let (r1, st1) ←
          code.branch
            { st with core := { st.core with pos := «end» } } data
            env true
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 14#uscalar =>
        let (r1, st1) ←
          code.branch_table
            { st with core := { st.core with pos := «end» } } data
            env
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 15#uscalar =>
        let (r1, ois) ←
          code.pop_results { st.core with pos := «end» }
            env (signature.ResultType.Type type_index signature.TypePart.Results)
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let ois1 ← code.mark_unreachable ois
          ok (cont ({ st with core := ois1 }, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 16#uscalar =>
        let (r1, st1) ←
          code.call { st with core := { st.core with pos := «end» } }
            data
            env false
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 17#uscalar =>
        let (r1, st1) ←
          code.call { st with core := { st.core with pos := «end» } }
            data
            env true
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | _ =>
        let i2 := alloc.vec.Vec.len st.core.vals
        if i2 = core.num.Usize.MAX
        then ok (done (core.result.Result.Err error.OpError.StackTooLarge))
        else
          let (r1, ois, visitor1) ←
            code.step_wasm2 code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
              { st.core with pos := «end» } data
              env { locals, results } op visitor
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            ok (cont ({ st with core := ois }, visitor1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame error.OpError)
                residual
            ok (done r2)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.OpError) residual
      ok (done r1)

/-- The extracted loop `code.body_loop_loop` run with the empty visitor, returning only the
validation result. -/
def Wasm2.emptyVisitorLoop
  (data : Slice U8) (env : metadata.Env) (type_index : U32)
  (st : code.BodyState)
  (locals : alloc.vec.Vec wasm_types.ValueType)
  (results : alloc.vec.Vec wasm_types.ValueType)
  (visitor : code.EmptyOpVisitor) :
  Result (core.result.Result Unit error.OpError)
  := do
  let (r, _) ← code.body_loop_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env
    ⟨locals, results⟩ type_index visitor st
  .ok r

/-- Only the placement of the empty visitor changes between the semantic
adapter and the extracted visiting loop. -/
theorem Wasm2.emptyVisitorLoop.body_eq (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (st : code.BodyState) :
    code.body_loop_loop.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx index () st = (do
      let r ← Wasm2.emptyVisitorLoop.body data env index ctx.locals ctx.results st ()
      .ok (match r with | .cont (s, _) => .cont ((), s) | .done result => .done (result, ()))) := by
  unfold code.body_loop_loop.body code.step_profile Wasm2.emptyVisitorLoop.body
  simp only [code.BodyState.blocks_is_empty, Std.bind_assoc]
  congr 1
  funext b
  split
  · split <;> simp
  · simp only [Std.bind_assoc]
    congr 1
    funext r
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨opcode, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry, Std.bind_assoc]
      split
      all_goals simp_all only [code.enter, code.end_frame,
        code.branch, code.branch_table, code.call, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
      all_goals first
        | (congr 1; funext pair; rcases pair with ⟨r, s⟩; cases r <;>
            simp [code.OpVisitor.on_block.default,
              code.OpVisitor.on_loop.default, code.OpVisitor.on_if.default,
              code.OpVisitor.on_else.default, code.OpVisitor.on_end.default,
              code.OpVisitor.on_br.default, code.OpVisitor.on_br_if.default,
              code.OpVisitor.on_call.default, code.OpVisitor.on_call_indirect.default,
              code.OpVisitor.on_return.default, code.visit, Std.bind_assoc,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])
        | skip
      all_goals try (rcases s with ⟨s, v⟩; cases v; simp)
      split
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp only [Std.bind_assoc]
        congr 1
        funext pair
        obtain ⟨r, s, v⟩ := pair
        cases v
        cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The visitor-free body validator with the loop replaced by `Wasm2.emptyVisitorLoop`. -/
def code.bodyCore
  (data : Slice U8) (env : metadata.Env)
  (locals results : alloc.vec.Vec wasm_types.ValueType) (type_index : U32)
   :
  Result (core.result.Result Unit error.OpError)
  := do
  let i := Slice.len data
  if i > limits.MAX_FUNCTION_BYTES
  then ok (core.result.Result.Err error.OpError.BodyTooLarge)
  else
    let i1 ← lift (UScalar.cast .Usize type_index)
    let i2 := alloc.vec.Vec.len env.types
    if i1 >= i2
    then ok (core.result.Result.Err error.OpError.UnknownType)
    else
      let ft ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          wasm_types.FuncType) env.types i1
      let r ← code.check_func_type ft
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let st ←
          code.push_frame
            {
              core :=
                {
                  vals := (alloc.vec.Vec.new code.StackType),
                  ctrls := (alloc.vec.Vec.new code.Ctrl),
                  pos := 0#usize
                }
            } code.LabelKind.Body (signature.BlockType.TypeIndex type_index)
        Wasm2.emptyVisitorLoop data env type_index st locals results ()
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.OpError) residual

end Itasca

end
