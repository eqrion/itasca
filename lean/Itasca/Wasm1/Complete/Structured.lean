import Itasca.Wasm1.Complete.Program
import Itasca.Wasm1.Complete.Control

/-!
# Wasm 1.0 structured instruction completeness

Executes `block`, `loop`, `if`, `else` and `end` through `code.step`, and builds `AtomProgram`
for `block`, `loop` and `if` with and without `else` (`atom_block`, `atom_loop`, `atom_ifEnd`,
`atom_ifElse`) from `Program` for their nested bodies. The signature lemmas recover block types
from the generated `Instr_ok` rule, and the profile lemmas restrict `Wasm1.Instruction` to the
nested instructions.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

theorem blocktype_signature {C : context} (bt : code.BlockType) {input output : List valtype}
    (h : Blocktype_ok C (Control.blockType bt) (.mk_functype (.mk_list input) (.mk_list output))) :
    input = [] ∧ output = Control.resultTypes bt := by
  cases bt <;> cases h <;> simp [Control.resultTypes, Control.results]

theorem block_signature {C : context} (bt : code.BlockType) (ops : List instr)
    {input output : List valtype}
    (h : Instr_ok C (.BLOCK (Control.blockType bt) ops)
      (.mk_functype (.mk_list input) (.mk_list output))) :
    input = [] ∧ output = Control.resultTypes bt ∧
      Instrs_ok (Control.labelContext (Control.resultTypes bt) ++ C) ops
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) := by
  cases h with
  | block C bt' ops input output hbt hbody hC hw hlabel =>
    obtain ⟨rfl, rfl⟩ := blocktype_signature bt hbt
    exact ⟨rfl, rfl, hbody⟩

theorem loop_signature {C : context} (bt : code.BlockType) (ops : List instr)
    {input output : List valtype}
    (h : Instr_ok C (.LOOP (Control.blockType bt) ops)
      (.mk_functype (.mk_list input) (.mk_list output))) :
    input = [] ∧ output = Control.resultTypes bt ∧
      Instrs_ok (Control.labelContext [] ++ C) ops
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) := by
  cases h with
  | loop C bt' ops input output hbt hbody hC hw hlabel =>
    obtain ⟨rfl, rfl⟩ := blocktype_signature bt hbt
    exact ⟨rfl, rfl, hbody⟩

theorem if_signature {C : context} (bt : code.BlockType) (yes no : List instr)
    {input output : List valtype}
    (h : Instr_ok C (.IFELSE (Control.blockType bt) yes no)
      (.mk_functype (.mk_list input) (.mk_list output))) :
    input = [.I32] ∧ output = Control.resultTypes bt ∧
      Instrs_ok (Control.labelContext (Control.resultTypes bt) ++ C) yes
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) ∧
      Instrs_ok (Control.labelContext (Control.resultTypes bt) ++ C) no
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) := by
  cases h with
  | «if» C bt' yes no input output hbt hy hn hC hw hlabel =>
    obtain ⟨rfl, rfl⟩ := blocktype_signature bt hbt
    exact ⟨rfl, rfl, hy, hn⟩

theorem blockType_injective : Function.Injective Control.blockType := by
  intro a b h
  cases a with
  | Empty => cases b <;> simp_all [Control.blockType]
  | Value a =>
    cases b with
    | Empty => simp [Control.blockType] at h
    | Value b =>
      have he : Translate.valueType a = Translate.valueType b := by simpa [Control.blockType] using h
      exact congrArg code.BlockType.Value (Translate.valueType_injective he)

theorem block_profile {C : context} (bt : code.BlockType) (ops : List instr)
    (h : Wasm1.Instruction C (.BLOCK (Control.blockType bt) ops)) :
    Wasm1.Instructions (Control.labelContext (Control.resultTypes bt) ++ C) ops := by
  generalize he : Control.blockType bt = b at h
  cases h with
  | leaf _ _ hf => exact hf.elim
  | block C bt' ops hp =>
    have hbt := blockType_injective he
    subst bt'
    exact hp

theorem loop_profile {C : context} (bt : code.BlockType) (ops : List instr)
    (h : Wasm1.Instruction C (.LOOP (Control.blockType bt) ops)) :
    Wasm1.Instructions (Control.labelContext [] ++ C) ops := by
  generalize he : Control.blockType bt = b at h
  cases h with
  | leaf _ _ hf => exact hf.elim
  | loop C bt' ops hp => exact hp

theorem if_profile {C : context} (bt : code.BlockType) (yes no : List instr)
    (h : Wasm1.Instruction C (.IFELSE (Control.blockType bt) yes no)) :
    Wasm1.Instructions (Control.labelContext (Control.resultTypes bt) ++ C) yes ∧
      Wasm1.Instructions (Control.labelContext (Control.resultTypes bt) ++ C) no := by
  generalize he : Control.blockType bt = b at h
  cases h with
  | leaf _ _ hf => exact hf.elim
  | ifElse C bt' yes no hy hn =>
    have hbt := blockType_injective he
    subst bt'
    exact ⟨hy, hn⟩

theorem bounds_after_token {data : Slice U8} {st s : code.OpIterState}
    {token : Wasm1.Token} {next : Usize} (h : Wasm1.Bounds data st)
    (hat : Wasm1.At data st.pos token next) (hp : s.pos = next)
    (hv : s.vals.val.length ≤ st.vals.val.length + 1)
    (hc : s.ctrls.val.length ≤ st.ctrls.val.length + 1) : Wasm1.Bounds data s := by
  have hs := hat.span
  have hvs := h.vals
  have hcs := h.ctrls
  refine ⟨h.size, by simpa [hp] using hs.2, ?_, ?_⟩ <;> rw [hp] <;> omega

/-- Executing the final `end` of a frame pops it, keeps the parent frames and pushes the declared
result operands. This also covers the end of the function body. -/
theorem execute_end {st : code.OpIterState} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (next : Usize)
    (hb : Wasm1.Bounds data st) (hat : Wasm1.At data st.pos .end_ next)
    (hthen : f.current.kind = .Then → f.current.block_type = .Empty)
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands
      (Control.resultTypes f.current.block_type)) :
    ∃ s, Wasm1.Execution data env ctx st s ∧ s.pos = next ∧
      s.ctrls.val = f.parents ∧
      s.vals.val = f.outer ++ (Control.results f.current.block_type).map code.StackType.Val ∧
      Wasm1.Bounds data s := by
  obtain ⟨opcode, pos, bytes, hread, hpos, himm, hspan⟩ := hat.read_op st rfl
  cases himm
  have hnext := hspan.empty
  have hcap : f.outer.length + (Control.results f.current.block_type).length ≤ Usize.max := by
    have hlen : (Control.results f.current.block_type).length ≤ 1 := by
      cases f.current.block_type <;> simp [Control.results]
    have hv := hb.vals
    have hp := hb.pos
    have hs := hb.size
    have hm := limits.MAX_FUNCTION_BYTES.room
    rw [f.vals, List.length_append] at hv
    omega
  obtain ⟨⟨_, s⟩, hr, rfl, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_end.complete {st with pos := pos} f.parents f.current f.outer f.operands
      f.ctrls f.vals f.base hthen hcap ht)
  dsimp only at hc hv hp
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      {st with pos := pos} data env ctx code.OP_END () = .ok (.Ok (), s, ()) := by
    simp [global_simps, hr, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
      code.OpVisitor.on_end.default]
  have hp' : s.pos = next := hp.trans hnext.symm
  refine ⟨s, .single f.nonempty hread (by simpa [global_simps] using hstep), hp', hc, hv, ?_⟩
  apply bounds_after_token hb hat hp'
  · have hlen : (Control.results f.current.block_type).length ≤ 1 := by
      cases f.current.block_type <;> simp [Control.results]
    simp only [hv, f.vals, List.length_append, List.length_map]
    omega
  · simp only [hc, f.ctrls, List.length_append, List.length_singleton]; omega

theorem execute_else {st : code.OpIterState} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (next : Usize)
    (hb : Wasm1.Bounds data st) (hat : Wasm1.At data st.pos .else_ next)
    (hthen : f.current.kind = .Then)
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands
      (Control.resultTypes f.current.block_type)) :
    ∃ s, Wasm1.Execution data env ctx st s ∧ s.pos = next ∧
      s.ctrls.val = f.parents ++ [{f.current with kind := .Else, polymorphic_base := false}] ∧
      s.vals.val = f.outer ∧ Wasm1.Bounds data s := by
  obtain ⟨opcode, pos, bytes, hread, hpos, himm, hspan⟩ := hat.read_op st rfl
  cases himm
  have hnext := hspan.empty
  obtain ⟨⟨_, s⟩, hr, rfl, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_else.complete {st with pos := pos} f.parents f.current f.outer f.operands
      f.ctrls f.vals f.base hthen ht)
  dsimp only at hc hv hp
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      {st with pos := pos} data env ctx code.OP_ELSE () = .ok (.Ok (), s, ()) := by
    simp [global_simps, hr, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
      code.OpVisitor.on_else.default]
  have hp' : s.pos = next := hp.trans hnext.symm
  refine ⟨s, .single f.nonempty hread (by simpa [global_simps] using hstep), hp', hc, hv, ?_⟩
  apply bounds_after_token hb hat hp'
  · simp only [hv, f.vals, List.length_append]; omega
  · simp only [hc, f.ctrls, List.length_append, List.length_singleton]; omega

theorem execute_block {st : code.OpIterState} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (bt : code.BlockType) (next : Usize)
    (hb : Wasm1.Bounds data st) (hat : Wasm1.At data st.pos (.block bt) next) :
    ∃ s, Wasm1.Execution data env ctx st s ∧ s.pos = next ∧ s.vals = st.vals ∧
      s.ctrls.val = st.ctrls.val ++ [Control.frame st .Block bt] ∧ Wasm1.Bounds data s := by
  obtain ⟨opcode, pos, bytes, hread, hpos, himm, hspan⟩ := hat.read_op st rfl
  cases himm
  have hcap : st.ctrls.val.length < Usize.max := by
    have hc := hb.ctrls; have hp := hb.pos; have hs := hb.size; have hm := limits.MAX_FUNCTION_BYTES.room
    omega
  obtain ⟨⟨_, s⟩, hr, rfl, hp, hv, hc⟩ := WP.spec_imp_exists
    (code.read_block.complete {st with pos := pos} data bt next hspan hcap (by assumption))
  dsimp only at hp hv hc
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      {st with pos := pos} data env ctx code.OP_BLOCK () = .ok (.Ok (), s, ()) := by
    simp [global_simps, hr, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
      code.OpVisitor.on_block.default]
  exact ⟨s, .single f.nonempty hread (by simpa [global_simps] using hstep), hp, hv, hc,
    bounds_after_token hb hat hp (by simp [hv]) (by simp [hc])⟩

theorem execute_loop {st : code.OpIterState} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (bt : code.BlockType) (next : Usize)
    (hb : Wasm1.Bounds data st) (hat : Wasm1.At data st.pos (.loop bt) next) :
    ∃ s, Wasm1.Execution data env ctx st s ∧ s.pos = next ∧ s.vals = st.vals ∧
      s.ctrls.val = st.ctrls.val ++ [Control.frame st .Loop bt] ∧ Wasm1.Bounds data s := by
  obtain ⟨opcode, pos, bytes, hread, hpos, himm, hspan⟩ := hat.read_op st rfl
  cases himm
  have hcap : st.ctrls.val.length < Usize.max := by
    have hc := hb.ctrls; have hp := hb.pos; have hs := hb.size; have hm := limits.MAX_FUNCTION_BYTES.room
    omega
  obtain ⟨⟨_, s⟩, hr, rfl, hp, hv, hc⟩ := WP.spec_imp_exists
    (code.read_loop.complete {st with pos := pos} data bt next hspan hcap (by assumption))
  dsimp only at hp hv hc
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      {st with pos := pos} data env ctx code.OP_LOOP () = .ok (.Ok (), s, ()) := by
    simp [global_simps, hr, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
      code.OpVisitor.on_loop.default]
  exact ⟨s, .single f.nonempty hread (by simpa [global_simps] using hstep), hp, hv, hc,
    bounds_after_token hb hat hp (by simp [hv]) (by simp [hc])⟩

theorem execute_if {st : code.OpIterState} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (bt : code.BlockType) (next : Usize)
    (front : List valtype)
    (hb : Wasm1.Bounds data st) (hat : Wasm1.At data st.pos (.if_ bt) next)
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ [.I32])) :
    ∃ s rest, Wasm1.Execution data env ctx st s ∧ s.pos = next ∧
      s.vals.val = f.outer ++ rest ∧
      s.ctrls.val = st.ctrls.val ++ [Control.frame s .Then bt] ∧
      Sequence.Realizes f.current.polymorphic_base rest front ∧ Wasm1.Bounds data s := by
  obtain ⟨opcode, pos, bytes, hread, hpos, himm, hspan⟩ := hat.read_op st rfl
  cases himm
  have hcap : st.ctrls.val.length < Usize.max := by
    have hc := hb.ctrls; have hp := hb.pos; have hs := hb.size; have hm := limits.MAX_FUNCTION_BYTES.room
    omega
  obtain ⟨⟨_, s⟩, hr, rfl, hp, rest, hv, hl, hc, ht'⟩ := WP.spec_imp_exists
    (code.read_if.complete {st with pos := pos} data bt next f.outer f.operands front
      hspan f.vals f.base_eq hcap (by simpa [Control.polymorphic, f.ctrls] using ht) (by assumption))
  dsimp only at hp hv hl hc ht'
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      {st with pos := pos} data env ctx code.OP_IF () = .ok (.Ok (), s, ()) := by
    simp [global_simps, hr, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
      code.OpVisitor.on_if.default]
  refine ⟨s, rest, .single f.nonempty hread (by simpa [global_simps] using hstep), hp, hv, hc, ?_, ?_⟩
  · simpa [Control.polymorphic, f.ctrls] using ht'
  · apply bounds_after_token hb hat hp
    · simp only [hv, f.vals, List.length_append]; omega
    · simp [hc]

/-- Runs a typed nested body and then its closing `end`. -/
theorem execute_body {data : Slice U8} {env : module.Env} {ctx : code.Context}
    {tokens : List Wasm1.Token} {ops : List instr}
    (program : Program data env ctx tokens ops) (C : context)
    (st : code.OpIterState) (f : Frame st) (next : Usize)
    (hm : EnvTranslation.Matches env ctx C) (hl : C.LABELS = Control.labels st.ctrls.val)
    (hb : Wasm1.Bounds data st) (hbytes : Wasm1.Consumed data st.pos (tokens ++ [Wasm1.Token.end_]) next)
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands [])
    (hbody : Instrs_ok C ops (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes f.current.block_type))))
    (hp : Wasm1.Instructions C ops)
    (hthen : f.current.kind = .Then → f.current.block_type = .Empty) :
    ∃ s, Wasm1.Execution data env ctx st s ∧ s.pos = next ∧
      s.ctrls.val = f.parents ∧
      s.vals.val = f.outer ++ (Control.results f.current.block_type).map code.StackType.Val ∧
      Wasm1.Bounds data s := by
  obtain ⟨middle, hinner, hend⟩ := hbytes.split
  obtain ⟨mid, hrun, hpos, hout, hbounds⟩ :=
    program C st f middle [] _ hm hl hb hinner ht hbody hp
  obtain ⟨poly, operands, hc, hv, hreal⟩ := hout
  let g : Frame mid := ⟨f.parents, {f.current with polymorphic_base := poly},
    f.outer, operands, hc, hv, f.base⟩
  obtain ⟨s, hclose, hpos', hc', hv', hb'⟩ :=
    execute_end g data env ctx next hbounds (by simpa [hpos] using hend.single) hthen hreal
  exact ⟨s, hrun.append hclose, hpos', hc', hv', hb'⟩

theorem atom_block {data : Slice U8} {env : module.Env} {ctx : code.Context}
    (bt : code.BlockType) {tokens : List Wasm1.Token} {ops : List instr}
    (he : Wasm1.Emits tokens ops)
    (smaller : SmallerPrograms data env ctx ([Wasm1.Token.block bt] ++ tokens ++ [Wasm1.Token.end_]).length) :
    AtomProgram data env ctx ([.block bt] ++ tokens ++ [Wasm1.Token.end_]) (.BLOCK (Control.blockType bt) ops) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hp
  obtain ⟨rfl, rfl, hbody⟩ := block_signature bt ops htyped
  have hprofile := block_profile bt ops hp
  have hreal : Sequence.Realizes f.current.polymorphic_base f.operands front := by simpa using ht
  obtain ⟨header, hhead, hrest⟩ := Wasm1.Consumed.cons_iff.mp (by simpa using hbytes)
  obtain ⟨entered, henter, hpos, hv, hc, hbounds⟩ := execute_block f data env ctx bt header hb hhead
  let child : Frame entered := ⟨st.ctrls.val, Control.frame st .Block bt, st.vals.val, [],
    hc, by simp [hv], rfl⟩
  have hlabels : (Control.labelContext (Control.resultTypes bt) ++ C).LABELS =
      Control.labels entered.ctrls.val := by
    simp [hc, Control.labels_push, Control.frame, Control.targetTypes,
      Control.targetBlockType, Control.resultTypes, hl]
  obtain ⟨s, hrun, hpos', hc', hv', hb'⟩ := execute_body
    (smaller tokens ops (by simp) he) _ entered child next (hm.enter _) hlabels hbounds
      (by simpa [hpos] using hrest) (by simp [child, Control.frame, Sequence.Realizes])
      hbody hprofile (by simp [child, Control.frame])
  refine ⟨s, henter.append hrun, hpos', ?_, hb'⟩
  apply f.output_of_same_ctrls (alloc.vec.Vec.ext _ _ hc')
    (operands := f.operands ++ (Control.results bt).map code.StackType.Val)
  · simpa [child, Control.frame, f.vals, List.append_assoc] using hv'
  · apply (Sequence.realizes_append_concrete _ _ _ _).mpr
    exact ⟨front, by simpa [f.poly_eq] using hreal, rfl⟩

theorem atom_loop {data : Slice U8} {env : module.Env} {ctx : code.Context}
    (bt : code.BlockType) {tokens : List Wasm1.Token} {ops : List instr}
    (he : Wasm1.Emits tokens ops)
    (smaller : SmallerPrograms data env ctx ([Wasm1.Token.loop bt] ++ tokens ++ [Wasm1.Token.end_]).length) :
    AtomProgram data env ctx ([.loop bt] ++ tokens ++ [Wasm1.Token.end_]) (.LOOP (Control.blockType bt) ops) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hp
  obtain ⟨rfl, rfl, hbody⟩ := loop_signature bt ops htyped
  have hprofile := loop_profile bt ops hp
  have hreal : Sequence.Realizes f.current.polymorphic_base f.operands front := by simpa using ht
  obtain ⟨header, hhead, hrest⟩ := Wasm1.Consumed.cons_iff.mp (by simpa using hbytes)
  obtain ⟨entered, henter, hpos, hv, hc, hbounds⟩ := execute_loop f data env ctx bt header hb hhead
  let child : Frame entered := ⟨st.ctrls.val, Control.frame st .Loop bt, st.vals.val, [],
    hc, by simp [hv], rfl⟩
  have hlabels : (Control.labelContext [] ++ C).LABELS =
      Control.labels entered.ctrls.val := by
    simp [hc, Control.labels_push, Control.frame, Control.targetTypes,
      Control.targetBlockType, Control.results, hl]
  obtain ⟨s, hrun, hpos', hc', hv', hb'⟩ := execute_body
    (smaller tokens ops (by simp) he) _ entered child next (hm.enter _) hlabels hbounds
      (by simpa [hpos] using hrest) (by simp [child, Control.frame, Sequence.Realizes])
      hbody hprofile (by simp [child, Control.frame])
  refine ⟨s, henter.append hrun, hpos', ?_, hb'⟩
  apply f.output_of_same_ctrls (alloc.vec.Vec.ext _ _ hc')
    (operands := f.operands ++ (Control.results bt).map code.StackType.Val)
  · simpa [child, Control.frame, f.vals, List.append_assoc] using hv'
  · apply (Sequence.realizes_append_concrete _ _ _ _).mpr
    exact ⟨front, by simpa [f.poly_eq] using hreal, rfl⟩

theorem empty_if_result {C : context} (bt : code.BlockType)
    (h : Instrs_ok C [] (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt)))) :
    bt = .Empty := by
  have hl := DeclarativeComplete.result_sub_length (DeclarativeComplete.empty_sub h)
  cases bt <;> simp_all [Control.resultTypes, Control.results]

theorem atom_ifEnd {data : Slice U8} {env : module.Env} {ctx : code.Context}
    (bt : code.BlockType) {tokens : List Wasm1.Token} {ops : List instr}
    (he : Wasm1.Emits tokens ops)
    (smaller : SmallerPrograms data env ctx ([Wasm1.Token.if_ bt] ++ tokens ++ [Wasm1.Token.end_]).length) :
    AtomProgram data env ctx ([.if_ bt] ++ tokens ++ [Wasm1.Token.end_])
      (.IFELSE (Control.blockType bt) ops []) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hp
  obtain ⟨rfl, rfl, hbody, hempty⟩ := if_signature bt ops [] htyped
  have hbt := empty_if_result bt hempty
  have hprofile := (if_profile bt ops [] hp).1
  obtain ⟨header, hhead, hrest⟩ := Wasm1.Consumed.cons_iff.mp (by simpa using hbytes)
  obtain ⟨entered, rest, henter, hpos, hv, hc, hreal, hbounds⟩ :=
    execute_if f data env ctx bt header front hb hhead ht
  let child : Frame entered := ⟨st.ctrls.val, Control.frame entered .Then bt, entered.vals.val, [],
    hc, by simp, rfl⟩
  have hlabels : (Control.labelContext (Control.resultTypes bt) ++ C).LABELS =
      Control.labels entered.ctrls.val := by
    simp [hc, Control.labels_push, Control.frame, Control.targetTypes,
      Control.targetBlockType, Control.resultTypes, hl]
  obtain ⟨s, hrun, hpos', hc', hv', hb'⟩ := execute_body
    (smaller tokens ops (by simp) he) _ entered child next (hm.enter _) hlabels hbounds
      (by simpa [hpos] using hrest) (by simp [child, Control.frame, Sequence.Realizes])
      hbody hprofile (by simpa [child, Control.frame] using hbt)
  refine ⟨s, henter.append hrun, hpos', ?_, hb'⟩
  apply f.output_of_same_ctrls (alloc.vec.Vec.ext _ _ hc')
    (operands := rest ++ (Control.results bt).map code.StackType.Val)
  · simpa [child, Control.frame, hv, List.append_assoc] using hv'
  · apply (Sequence.realizes_append_concrete _ _ _ _).mpr
    exact ⟨front, by simpa [f.poly_eq] using hreal, rfl⟩

theorem atom_ifElse {data : Slice U8} {env : module.Env} {ctx : code.Context}
    (bt : code.BlockType) {yesTokens noTokens : List Wasm1.Token} {yes no : List instr}
    (hyes : Wasm1.Emits yesTokens yes) (hno : Wasm1.Emits noTokens no)
    (smaller : SmallerPrograms data env ctx
      ([Wasm1.Token.if_ bt] ++ yesTokens ++ [Wasm1.Token.else_] ++ noTokens ++ [Wasm1.Token.end_]).length) :
    AtomProgram data env ctx ([.if_ bt] ++ yesTokens ++ [Wasm1.Token.else_] ++ noTokens ++ [Wasm1.Token.end_])
      (.IFELSE (Control.blockType bt) yes no) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hp
  obtain ⟨rfl, rfl, hyesBody, hnoBody⟩ := if_signature bt yes no htyped
  obtain ⟨hyesProfile, hnoProfile⟩ := if_profile bt yes no hp
  obtain ⟨header, hhead, hrest⟩ := Wasm1.Consumed.cons_iff.mp
    (show Wasm1.Consumed data st.pos (.if_ bt :: (yesTokens ++ [Wasm1.Token.else_] ++ noTokens ++ [Wasm1.Token.end_])) next by
      simpa using hbytes)
  obtain ⟨entered, rest, henter, hpos, hv, hc, hreal, hbounds⟩ :=
    execute_if f data env ctx bt header front hb hhead ht
  let child : Frame entered := ⟨st.ctrls.val, Control.frame entered .Then bt, entered.vals.val, [],
    hc, by simp, rfl⟩
  have hlabels : (Control.labelContext (Control.resultTypes bt) ++ C).LABELS =
      Control.labels entered.ctrls.val := by
    simp [hc, Control.labels_push, Control.frame, Control.targetTypes,
      Control.targetBlockType, Control.resultTypes, hl]
  obtain ⟨yesEnd, hybytes, hnbytes⟩ := Wasm1.Consumed.split
    (show Wasm1.Consumed data entered.pos (yesTokens ++ ([Wasm1.Token.else_] ++ noTokens ++ [Wasm1.Token.end_])) next by
      simpa [hpos, List.append_assoc] using hrest)
  have hprogramYes := smaller yesTokens yes (by simp) hyes
  obtain ⟨yesState, hyesRun, hyesPos, hyesOut, hyesBounds⟩ :=
    hprogramYes _ entered child yesEnd [] (Control.resultTypes bt) (hm.enter _) hlabels hbounds
      hybytes (by simp [child, Control.frame, Sequence.Realizes]) hyesBody hyesProfile
  obtain ⟨yesPoly, yesOperands, hyc, hyv, hyr⟩ := hyesOut
  let yesFrame : Frame yesState := ⟨child.parents, {child.current with polymorphic_base := yesPoly},
    child.outer, yesOperands, hyc, hyv, child.base⟩
  obtain ⟨elseStart, hatElse, hnoBytes⟩ := Wasm1.Consumed.cons_iff.mp
    (show Wasm1.Consumed data yesState.pos (.else_ :: (noTokens ++ [Wasm1.Token.end_])) next by
      simpa [hyesPos] using hnbytes)
  obtain ⟨elseState, helseRun, helsePos, hec, hev, heBounds⟩ :=
    execute_else yesFrame data env ctx elseStart hyesBounds hatElse rfl hyr
  let elseFrame : Frame elseState := ⟨yesFrame.parents,
    {yesFrame.current with kind := .Else, polymorphic_base := false}, yesFrame.outer, [],
    hec, by simp [hev], yesFrame.base⟩
  have hlabelsElse : (Control.labelContext (Control.resultTypes bt) ++ C).LABELS =
      Control.labels elseState.ctrls.val := by
    simp [hec, yesFrame, child, Control.labels_push, Control.frame, Control.targetTypes,
      Control.targetBlockType, Control.resultTypes, hl]
  obtain ⟨s, hnoRun, hpos', hc', hv', hb'⟩ := execute_body
    (smaller noTokens no (by simp; omega) hno) _ elseState elseFrame next
      (hm.enter _) hlabelsElse heBounds (by simpa [helsePos] using hnoBytes)
      (by simp [elseFrame, Sequence.Realizes]) hnoBody hnoProfile
      (by simp [elseFrame])
  refine ⟨s, ((henter.append hyesRun).append helseRun).append hnoRun, hpos', ?_, hb'⟩
  apply f.output_of_same_ctrls (alloc.vec.Vec.ext _ _ hc')
    (operands := rest ++ (Control.results bt).map code.StackType.Val)
  · simpa [elseFrame, yesFrame, child, Control.frame, hv, List.append_assoc] using hv'
  · apply (Sequence.realizes_append_concrete _ _ _ _).mpr
    exact ⟨front, by simpa [f.poly_eq] using hreal, rfl⟩

end Itasca.Wasm1.Completeness
