import Itasca.Body.SoundLoop
import Itasca.Body.Step.NonControlSound
import Itasca.Body.Control.BranchComplete
import Itasca.Body.Control.EnterSound
import Itasca.Body.Complete.Control

open WebAssembly

/-!
Proofs for Body.

This module collects Soundness, Completeness.
Each section documents its contracts and consumers.
-/

/-! ## Soundness -/

section

/-!
# Body soundness

`steps` joins scalar and structured-control cases into preservation of the body
invariant. `code.bodyCore.spec` and `.sound` compose that invariant through the
loop: accepted bytes have the independent instruction encoding, generated typing
and declared-reference evidence in `Body.Validated`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- Every opcode preserves semantic control and exact byte provenance on
success. Reserved opcodes and malformed immediates need no input premise. -/
theorem steps (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (ctx : code.Context) (index : U32)
    (hlocals : ctx.locals = locals) : Steps data env locals ctx index := by
  intro st p
  generalize hbyte : data.val[p.start.val]'p.inbounds = opcode
  by_cases hs : opcode.val ∉ controlOpcodes
  · exact p.scalar_step ctx hlocals opcode hs hbyte
  · have hm := Classical.not_not.mp hs
    obtain ⟨⟨n, hn⟩⟩ := opcode
    change n ∈ controlOpcodes at hm
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h <;> subst n
    · simpa [step, Frames.Form.kind] using p.enter_after .block (Or.inl rfl) hbyte
    · simpa [step, Frames.Form.kind] using p.enter_after .loop (Or.inr (Or.inl rfl)) hbyte
    · simpa [step, Frames.Form.kind] using p.enter_after .then_ (Or.inr (Or.inr rfl)) hbyte
    · simpa [step] using p.end_after true 0x05#u8 rfl hbyte
    · simpa [step] using p.end_after false 0x0B#u8 rfl hbyte
    · simpa [step] using p.branch hbyte
    · simpa [step] using p.branch_if hbyte
    · simpa [step] using p.branch_table hbyte
    · simpa [step] using p.return_ hbyte
    · simpa [step] using p.call hbyte
    · simpa [step] using p.call_indirect hbyte

end Itasca.Body

namespace Itasca

/-- `code.bodyCore` is sound for the unified validator, on arbitrary bytes and contexts. -/
theorem code.bodyCore.spec (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32) :
    code.bodyCore data env locals results index ⦃ r =>
      r = .Ok () → Body.Validated data env locals index ⦄ :=
  Body.public_spec_of_steps data env locals results index
    (Body.steps data env locals ⟨locals, results⟩ index rfl)

theorem code.bodyCore.sound (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32)
    (haccepted : code.bodyCore data env locals results index = .ok (.Ok ())) :
    Body.Validated data env locals index := by
  have hs := code.bodyCore.spec data env locals results index
  simpa [haccepted] using hs

end Itasca

end

/-! ## Completeness -/

section

/-!
# Wasm 2.0 body completeness

Completeness of the extracted body validator from independent premises. `code.bodyCore.complete`
accepts every `Body.Validated` body within the implementation limits. The
per-opcode contracts it builds on are in `Body/Complete/`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Completeness

/-- A body with independent encoding, typing and declared references is accepted, given a
`Program` contract for every token sequence. Typing starts the body with no operands, even when
its type has parameters, and the final `end` closes the selected result signature. -/
theorem body_execution_of_programs (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (hi : env.types.val[index.val]? = some ft)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hprograms : ∀ tokens ops, Emits tokens ops →
      Program data env ⟨locals, ft.results⟩ index tokens ops)
    (ops : List instr)
    (hencoding : ∃ tokens next, Body.Consumed data 0#usize tokens next ∧
      next.val = data.length ∧ BodyTokens tokens ops)
    (htyped : FunctionTyped env locals ft ops)
    (hdecl : Spec.DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops) :
    ∃ last, Execution data env ⟨locals, results⟩ index (initial index) last ∧
      last.blocks.val = [] ∧ last.core.pos.val = data.length := by
  obtain ⟨tokens, next, hbytes, hfinish, inner, heq, hemits⟩ := hencoding
  subst tokens
  obtain ⟨middle, hinner, hend⟩ := hbytes.split
  let st := initial index
  let f : Frame st :=
    ⟨⟨[], ⟨.Body, .TypeIndex index, 0#usize, false⟩, [], [], rfl, rfl, rfl⟩,
      [], .TypeIndex index, rfl, rfl⟩
  let C := Body.Control.labelContext (ft.results.val.map Translation.valueType) ++ bodyContext env locals ft
  have hmatch : Translation.Environment.Matches env ⟨locals, ft.results⟩ C :=
    (Translation.Environment.Matches.root env ⟨locals, ft.results⟩).enter _
  have hlabels : Labels env st C := by
    intro depth
    cases depth with
    | zero => simp [C, st, initial, Body.Control.label_context_labels, labelTypes, labelAt, target, outputs, resolve, hi]
    | succ depth => simp [C, st, initial, Body.Control.label_context_labels, bodyContext,
        Translation.Environment.context, labelTypes, labelAt]
  have hbounds : Bounds data st := by
    constructor <;> simp [st, initial, hsize]
  obtain ⟨s, hrun, hp, hout, _⟩ := hprograms inner ops hemits C st f middle []
    (ft.results.val.map Translation.valueType) hmatch hlabels hbounds hinner
      (Body.Stack.realizes_default false []) htyped hdecl
  obtain ⟨g, hgp, hgc, hcp, hco, hck, hcbase, hreal⟩ := hout.next
  obtain ⟨last, hclose, hp', _, hb', _⟩ := execute_end g data env ⟨locals, ft.results⟩
    index next ft.params.val ft.results.val (by simpa [hp] using hend.single)
    (by simp [hgc, f, inputs, resolve, hi]) (by simp [hgc, f, outputs, resolve, hi])
    (by simp [hck, f]) hreal (by simp [hco, f])
  refine ⟨last, (hrun.append hclose).change_context ⟨locals, results⟩ rfl, ?_, ?_⟩
  · simpa [hgp, f] using hb'
  · simpa [hp'] using hfinish

theorem body_of_programs (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (hi : env.types.val[index.val]? = some ft)
    (hparams : ft.params.val.length ≤ 1000) (hresults : ft.results.val.length ≤ 1000)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hprograms : ∀ tokens ops, Emits tokens ops →
      Program data env ⟨locals, ft.results⟩ index tokens ops)
    (ops : List instr)
    (hencoding : ∃ tokens next, Body.Consumed data 0#usize tokens next ∧
      next.val = data.length ∧ BodyTokens tokens ops)
    (htyped : FunctionTyped env locals ft ops)
    (hdecl : Spec.DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops) :
    code.bodyCore data env locals results index = .ok (.Ok ()) := by
  obtain ⟨last, run, closed, finished⟩ := body_execution_of_programs data env locals results
    index ft hi hsize hprograms ops hencoding htyped hdecl
  exact run.public hi hparams hresults hsize closed finished

end Itasca.Body.Completeness

open Aeneas Aeneas.Std

namespace Itasca.Body.Completeness

/-- Every token sequence emitted by a syntax tree has a `Program` contract for arbitrary
environments within limits. -/
theorem programs (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (henv : CodeEntry.EnvironmentWithinLimits env)
    (hret : resolve env (.Type index .Results) = some ctx.results.val)
    (tokens : List Token) (ops : List instr) (he : Emits tokens ops) :
    Program data env ctx index tokens ops := by
  apply program_of_atoms data env ctx index ?_ tokens ops he
  intro tokens op ha smaller
  change Emits tokens [op] at ha
  generalize eq : [op] = ops at ha
  cases ha <;> simp only [List.singleton_eq_append_iff, List.cons.injEq,
    List.cons_ne_nil, and_true, and_false, or_false] at eq
  all_goals obtain ⟨rfl, rfl⟩ := eq
  all_goals have prior := Emits.empty_iff.mp (by assumption)
  all_goals subst_vars
  case simple =>
    casesm WebAssembly.Binary.SimpleWith _ _
    exact atom_of_leaf data env ctx index (leaf_contract data env ctx index henv hret) _
  case block => exact atom_block henv _ (by assumption) smaller
  case loop => exact atom_loop henv _ (by assumption) smaller
  case ifElse => exact atom_if_else henv _ (by assumption) (by assumption) smaller
  case ifEnd => exact atom_if_end henv _ (by assumption) smaller

end Itasca.Body.Completeness

namespace Itasca

/-- Completeness of `code.bodyCore` from independent binary encoding,
generated Wasm 2.0 typing, and the independent function-reference declaration condition.
Implementation bounds constrain body bytes and signature sizes. -/
theorem code.bodyCore.complete (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32)
    (henv : CodeEntry.EnvironmentWithinLimits env)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Body.Validated data env locals index) :
    code.bodyCore data env locals results index = .ok (.Ok ()) := by
  obtain ⟨ft, ops, hi, hbytes, htyped, hdecl⟩ := hbody
  have hmem : ft ∈ env.types.val := List.mem_of_getElem? hi
  obtain ⟨hparams, hresults⟩ := (henv.types ft hmem).bounds
  exact Body.Completeness.body_of_programs data env locals results index ft hi hparams
    hresults hsize
    (Body.Completeness.programs data env ⟨locals, ft.results⟩ index henv
      (by simp [Body.resolve, hi])) ops hbytes htyped hdecl

end Itasca

end
