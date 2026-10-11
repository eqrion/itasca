import Itasca.MultiValue.CompletenessProgram
import Itasca.MultiValue.EnterStep
import Itasca.MultiValue.ControlStep

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Completeness

theorem blocktype_signature {env : module.Env} {ctx : code.Context} {C : context}
    (hm : EnvTranslation.Matches env ctx C) (bt : signature.BlockType) {input output : List valtype}
    (h : Blocktype_ok C (blockType bt) (.mk_functype (.mk_list input) (.mk_list output))) :
    ∃ ins outs, resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs ∧
      input = ins.map Translate.valueType ∧ output = outs.map Translate.valueType := by
  cases bt with
  | Empty => cases h; exact ⟨[], [], rfl, rfl, rfl, rfl⟩
  | Value t => cases h; exact ⟨[], [t], rfl, rfl, rfl, rfl⟩
  | TypeIndex index =>
    cases h with
    | typeidx _ _ _ hi he _ _ =>
      have hib : index.val < env.types.val.length := by simpa [hm.types, proj_uN_0] using hi
      have he' : EnvTranslation.funcType env.types.val[index.val] =
          .mk_functype (.mk_list input) (.mk_list output) := by
        simpa [hm.types, proj_uN_0, getElem!_pos, List.getElem_map, List.getElem?_eq_getElem hib] using he
      have hie : input = env.types.val[index.val].params.val.map Translate.valueType := by
        simpa [EnvTranslation.funcType] using congrArg (fun t => match t with | .mk_functype (.mk_list a) _ => a) he'.symm
      have hoe : output = env.types.val[index.val].results.val.map Translate.valueType := by
        simpa [EnvTranslation.funcType] using congrArg (fun t => match t with | .mk_functype _ (.mk_list a) => a) he'.symm
      exact ⟨_, _, by simp [resolve, inputs, hib], by simp [resolve, outputs, hib], hie, hoe⟩

theorem signature_limits {env : module.Env} (limits : EnvironmentWithinLimits env)
    (bt : signature.BlockType) (ins outs : List types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs) :
    ins.length ≤ 1000 ∧ outs.length ≤ 1000 := by
  cases bt with
  | Empty => simp [inputs, outputs, resolve] at hin hout; simp_all
  | Value t => simp [inputs, outputs, resolve] at hin hout; subst ins; subst outs; simp
  | TypeIndex index =>
    have hi : index.val < env.types.val.length := by
      by_contra he; simp [inputs, resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hin
    have h := limits.types _ (List.getElem_mem hi)
    simp [inputs, outputs, resolve, List.getElem?_eq_getElem hi] at hin hout
    simpa [← hin, ← hout] using h

theorem labels_push {env : module.Env} {C : context} {st s : multi_value.State}
    (hl : Labels env st C) (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (frame : code.Ctrl) (bt : signature.BlockType) (ts : List types.ValueType)
    (hc : s.core.ctrls.val = st.core.ctrls.val ++ [frame])
    (hb : s.blocks.val = st.blocks.val ++ [bt])
    (ht : resolve env (target frame.kind bt) = some ts) :
    Labels env s (Control.labelContext (ts.map Translate.valueType) ++ C) := by
  intro depth
  cases depth with
  | zero => simp [Control.labelContext_labels, labelTypes, labelAt, hc, hb, ha, ht]
  | succ depth =>
    rw [Control.labelContext_labels]
    simp only [List.getElem?_cons_succ, hl depth]
    unfold labelTypes labelAt
    by_cases hd : depth < st.blocks.val.length
    · have hs : depth + 1 < (st.blocks.val ++ [bt]).length := by simp; omega
      have he : (st.blocks.val ++ [bt]).length - 1 - (depth + 1) = st.blocks.val.length - 1 - depth := by simp; omega
      have hbnd : st.blocks.val.length - 1 - depth < st.blocks.val.length := by omega
      have he' : st.blocks.val.length - (depth + 1) = st.blocks.val.length - 1 - depth := by omega
      simp only [multi_value.State.blocks_length] at hd hs he hbnd he'
      simp [hb, hc, hd, he', hbnd, List.getElem?_append]
    · have hs : ¬ depth + 1 < (st.blocks.val ++ [bt]).length := by simp; omega
      simp only [multi_value.State.blocks_length] at hd
      simp [hb, hd]

/-- A delimiter execution, with exact effects and no post-delimiter capacity
estimate; callers derive bounds from the enclosing entry. -/
theorem execute_end {st : multi_value.State} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) (next : Usize)
    (ins outs : List types.ValueType)
    (hat : At data st.core.pos .end_ next)
    (hin : resolve env (inputs f.current) = some ins) (hout : resolve env (outputs f.current) = some outs)
    (hthen : f.core.current.kind = .Then → ins = outs)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (outs.map Translate.valueType))
    (hcap : f.core.outer.length + outs.length ≤ Usize.max) :
    ∃ s, Execution data env ctx index st s ∧ s.core.pos = next ∧
      s.core.ctrls.val = f.core.parents ∧ s.blocks.val = f.parents ∧
      s.core.vals.val = if f.parents = [] then f.core.outer else f.core.outer ++ outs.map code.StackType.Val := by
  have hs := hat.span
  have hinbounds : st.core.pos.val < data.length := by omega
  obtain ⟨_, hread, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hinbounds)
  obtain ⟨opcode, bytes, himm, ⟨_, hbyte⟩, hspan⟩ := hat.immediate pos hpos
  cases himm
  have hnext := hspan.empty
  obtain ⟨⟨r, s⟩, hr, hok, hp, hc, hb, hv⟩ := WP.spec_imp_exists
    (multi_value.end_frame.complete { st with core := { st.core with pos := pos } } env false
      f.core.parents f.parents f.core.current f.current ins outs f.core.outer f.core.operands
      f.core.ctrls f.blocks f.aligned f.core.vals f.core.base hin hout ht hthen hcap)
  dsimp only at hok
  subst r
  have hstep : step { st with core := { st.core with pos := pos } } data env ctx index 0x0B#u8 =
      .ok (.Ok (), s) := by simpa [step] using hr
  exact ⟨s, .single f.nonempty (by simpa [hbyte] using hread) hstep,
    hp.trans hnext.symm, hc, hb, hv⟩

theorem execute_else {st : multi_value.State} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) (next : Usize)
    (ins outs : List types.ValueType)
    (hat : At data st.core.pos .else_ next)
    (hin : resolve env (inputs f.current) = some ins) (hout : resolve env (outputs f.current) = some outs)
    (hthen : f.core.current.kind = .Then)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (outs.map Translate.valueType))
    (hcap : f.core.outer.length + ins.length ≤ Usize.max) :
    ∃ s, Execution data env ctx index st s ∧ s.core.pos = next ∧
      s.core.ctrls.val = f.core.parents ++ [{ f.core.current with kind := .Else, polymorphic_base := false }] ∧
      s.blocks = st.blocks ∧ s.core.vals.val = f.core.outer ++ ins.map code.StackType.Val := by
  have hs := hat.span
  have hinbounds : st.core.pos.val < data.length := by omega
  obtain ⟨_, hread, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hinbounds)
  obtain ⟨opcode, bytes, himm, ⟨_, hbyte⟩, hspan⟩ := hat.immediate pos hpos
  cases himm
  have hnext := hspan.empty
  obtain ⟨⟨r, s⟩, hr, hok, hp, hc, hb, hv⟩ := WP.spec_imp_exists
    (multi_value.end_frame.complete { st with core := { st.core with pos := pos } } env true
      f.core.parents f.parents f.core.current f.current ins outs f.core.outer f.core.operands
      f.core.ctrls f.blocks f.aligned f.core.vals f.core.base hin hout ht hthen hcap)
  dsimp only at hok
  subst r
  have hstep : step { st with core := { st.core with pos := pos } } data env ctx index 0x05#u8 =
      .ok (.Ok (), s) := by simpa [step] using hr
  exact ⟨s, .single f.nonempty (by simpa [hbyte] using hread) hstep,
    hp.trans hnext.symm, hc, hb, hv⟩

theorem execute_enter {st : multi_value.State} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (index : U32) (next : Usize)
    (form : Frames.Form) (initial : form.Initial) (bt : signature.BlockType)
    (ins outs : List types.ValueType) (front : List valtype)
    (limits : EnvironmentWithinLimits env) (hb : Bounds data st)
    (hat : At data st.core.pos (form.token bt) next)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ form.args ins)) :
    ∃ s, Execution data env ctx index st s ∧ s.core.pos = next ∧
      EnterForward st s form bt ins outs f.core.outer f.core.operands front ∧ Bounds data s := by
  have hs := hat.span
  have hinbounds : st.core.pos.val < data.length := by omega
  obtain ⟨_, hread, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hinbounds)
  obtain ⟨opcode, bytes, himm, ⟨_, hbyte⟩, hspan⟩ := hat.immediate pos hpos
  have hop : opcode = form.opcode ∧ BlockEncoding bt bytes := by
    rcases initial with rfl | rfl | rfl <;> cases himm <;> exact ⟨rfl, by assumption⟩
  have hd : BlockDecoded data pos bt next := blockDecoded_iff.mpr ⟨bytes, hop.2, hspan⟩
  obtain ⟨hins, houts⟩ := signature_limits limits bt ins outs hin hout
  obtain ⟨⟨r, s⟩, hr, hok, hp, heffect⟩ := WP.spec_imp_exists
    (multi_value.enter.complete { st with core := { st.core with pos := pos } } data env form initial
      bt next ins outs f.core.outer f.core.operands front hd hin hout hins houts f.core.vals
      f.core.base_eq (by simp [f.blocks, f.core.ctrls, f.aligned]) hb.ctrl_capacity
      (by change st.core.vals.val.length + ins.length ≤ Usize.max; have := hb.val_capacity; omega) (by simpa [Control.polymorphic, f.core.ctrls] using ht))
  dsimp only at hok
  subst r
  have hstep : step { st with core := { st.core with pos := pos } } data env ctx index opcode =
      .ok (.Ok (), s) := by
    rw [hop.1]
    rcases initial with rfl | rfl | rfl <;> simpa [step, Frames.Form.opcode, Frames.Form.kind] using hr
  refine ⟨s, .single f.nonempty (by simpa [hbyte] using hread) hstep, hp, heffect, ?_⟩
  obtain ⟨remaining, base, hlen, hbase, hreal, hctrls, hblocks, hvals⟩ := heffect
  apply bounds_after hb hat hp
  · have htwo := hd.span.1
    have hstart : st.core.pos.val + 2 ≤ next.val := by omega
    simp only [hvals, f.core.vals, List.length_append, List.length_map]
    omega
  · simp [hblocks]

private theorem restore_bounds {data : Slice U8} {st s : multi_value.State}
    (hb : Bounds data st) (hp : st.core.pos.val ≤ s.core.pos.val) (hpos : s.core.pos.val ≤ data.length)
    (hv : s.core.vals.val.length ≤ st.core.vals.val.length)
    (hc : s.blocks.val.length ≤ st.blocks.val.length) : Bounds data s := by
  have := hb.vals; have := hb.ctrls
  exact ⟨hb.size, hpos, by omega, by omega⟩

/-- Execute a child list and its end, preserving the original suspended
parent stack and result descriptor. -/
theorem execute_body {data : Slice U8} {env : module.Env} {ctx : code.Context} {index : U32}
    {tokens : List Token} {ops : List instr}
    (program : Program data env ctx index tokens ops) (C : context)
    (st : multi_value.State) (f : Frame st) (next : Usize)
    (ins outs : List types.ValueType)
    (hm : EnvTranslation.Matches env ctx C) (hl : Labels env st C)
    (hb : Bounds data st) (hbytes : Consumed data st.core.pos (tokens ++ [Token.end_]) next)
    (hin : resolve env (inputs f.current) = some ins) (hout : resolve env (outputs f.current) = some outs)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (ins.map Translate.valueType))
    (hbody : Instrs_ok C ops (.mk_functype (.mk_list (ins.map Translate.valueType))
      (.mk_list (outs.map Translate.valueType))))
    (hthen : f.core.current.kind = .Then → ins = outs)
    (hcap : f.core.outer.length + outs.length ≤ Usize.max) :
    ∃ s, Execution data env ctx index st s ∧ s.core.pos = next ∧
      s.core.ctrls.val = f.core.parents ∧ s.blocks.val = f.parents ∧
      s.core.vals.val = if f.parents = [] then f.core.outer else f.core.outer ++ outs.map code.StackType.Val := by
  obtain ⟨middle, hinner, hend⟩ := hbytes.split
  obtain ⟨mid, hrun, hpos, hout', hbounds⟩ := program C st f middle _ _ hm hl hb hinner ht hbody
  obtain ⟨g, hgp, hgc, hp, ho, hk, hcb, hbase, hreal⟩ := hout'.next
  obtain ⟨s, hclose, hp', hc', hb', hv'⟩ := execute_end g data env ctx index next ins outs
    (by simpa [hpos] using hend.single) (by simpa [hgc] using hin) (by simpa [hgc] using hout)
    (by simpa [hk] using hthen) hreal (by simpa [ho] using hcap)
  exact ⟨s, hrun.append hclose, hp', by simpa [hp] using hc', by simpa [hgp] using hb',
    by simpa [hgp, ho] using hv'⟩

private theorem concrete_realizes (ts : List types.ValueType) :
    Sequence.Realizes false (ts.map code.StackType.Val) (ts.map Translate.valueType) := by
  apply (WasmFrames.realizes_append_concrete false [] ts _).mpr
  exact ⟨[], by simp [Sequence.Realizes], rfl⟩

private theorem resume_parent {st s : multi_value.State} (f : Frame st)
    (remaining : List code.StackType) (front : List valtype) (outs : List types.ValueType)
    (hreal : Sequence.Realizes f.core.current.polymorphic_base remaining front)
    (hc : s.core.ctrls.val = st.core.ctrls.val) (hb : s.blocks.val = st.blocks.val)
    (hv : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val) :
    f.Output (front ++ outs.map Translate.valueType) s := by
  constructor
  · apply f.core.output_of_same_ctrls (alloc.vec.Vec.ext _ _ hc)
      (operands := remaining ++ outs.map code.StackType.Val) (by simpa [List.append_assoc] using hv)
    apply (WasmFrames.realizes_append_concrete _ _ _ _).mpr
    exact ⟨front, by simpa [f.core.poly_eq] using hreal, rfl⟩
  · exact alloc.vec.Vec.ext _ _ hb

private theorem closed_bounds {data : Slice U8} {st s : multi_value.State}
    (f : Frame st) (hb : Bounds data st) (next : Usize)
    (remaining : List code.StackType) (outs : List types.ValueType)
    (hp : s.core.pos = next) (hend : next.val ≤ data.length)
    (hlen : st.core.pos.val + 2 ≤ next.val) (hrem : remaining.length ≤ f.core.operands.length)
    (houts : outs.length ≤ 1000) (hblocks : s.blocks.val = st.blocks.val)
    (hvals : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val) :
    Bounds data s := by
  have hv := hb.vals; have hc := hb.ctrls
  rw [f.core.vals, List.length_append] at hv
  refine ⟨hb.size, by simpa [hp] using hend, ?_, ?_⟩
  · rw [hp, hvals, List.length_append, List.length_append, List.length_map]
    omega
  · simp only [hp, hblocks]; omega

/-- Common structured execution for blocks, loops, and omitted-else ifs. -/
theorem run_closed_child {data : Slice U8} {env : module.Env} {ctx : code.Context} {index : U32}
    (limits : EnvironmentWithinLimits env) (form : Frames.Form) (initial : form.Initial)
    (bt : signature.BlockType) (tokens : List Token) (ops : List instr)
    (program : Program data env ctx index tokens ops)
    (C : context) (st : multi_value.State) (f : Frame st) (next : Usize)
    (front : List valtype) (ins outs : List types.ValueType)
    (hm : EnvTranslation.Matches env ctx C) (hl : Labels env st C) (hb : Bounds data st)
    (hbytes : Consumed data st.core.pos ([form.token bt] ++ tokens ++ [Token.end_]) next)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ form.args ins))
    (hbody : Instrs_ok (Frames.enter C form ins outs) ops
      (.mk_functype (.mk_list (ins.map Translate.valueType)) (.mk_list (outs.map Translate.valueType))))
    (hthen : form = .then_ → ins = outs) :
    ∃ s, Execution data env ctx index st s ∧ s.core.pos = next ∧
      f.Output (front ++ outs.map Translate.valueType) s ∧ Bounds data s := by
  obtain ⟨header, hhead, hrest⟩ := Consumed.cons_iff.mp (by simpa using hbytes)
  obtain ⟨entered, henter, hpos, heffect, hbounds⟩ :=
    execute_enter f data env ctx index header form initial bt ins outs front limits hb hhead hin hout ht
  obtain ⟨remaining, base, hlen, hbase, hreal, hc, hblocks, hv⟩ := heffect
  let child : Frame entered :=
    ⟨⟨st.core.ctrls.val, (Frames.Saved.fresh base form bt ins outs).ctrl,
      f.core.outer ++ remaining, ins.map code.StackType.Val, hc, hv, by
        simpa [Frames.Saved.fresh] using hbase⟩,
      st.blocks.val, bt, hblocks, by simp [f.blocks, f.core.ctrls, f.aligned]⟩
  have hlabel : Labels env entered (Frames.enter C form ins outs) := by
    rcases initial with rfl | rfl | rfl
    · exact labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        (Frames.Saved.fresh base .block bt ins outs).ctrl bt outs hc hblocks hout
    · exact labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        (Frames.Saved.fresh base .loop bt ins outs).ctrl bt ins hc hblocks hin
    · exact labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        (Frames.Saved.fresh base .then_ bt ins outs).ctrl bt outs hc hblocks hout
  have hcap : (f.core.outer ++ remaining).length + outs.length ≤ Usize.max := by
    have hlimits := signature_limits limits bt ins outs hin hout
    have hvCap := hb.val_capacity
    rw [f.core.vals, List.length_append] at hvCap
    simp only [List.length_append]
    omega
  obtain ⟨s, hrun, hp', hc', hb', hv'⟩ := execute_body program _ entered child next ins outs
    (hm.enter _) hlabel hbounds (by simpa [hpos] using hrest) hin hout
    (concrete_realizes ins) hbody (by
      intro he
      apply hthen
      rcases initial with rfl | rfl | rfl <;> simp_all [child, Frames.Saved.fresh, Frames.Form.kind]) hcap
  have hvals : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val := by
    have hne : st.core.ctrls.val ≠ [] := by simpa using f.nonempty
    simpa [child, hne] using hv'
  refine ⟨s, henter.append hrun, hp', resume_parent f remaining front outs
    (by simpa [f.core.poly_eq] using hreal) hc' hb' hvals, ?_⟩
  apply closed_bounds f hb next remaining outs hp' hbytes.span.2 _ hlen
    (signature_limits limits bt ins outs hin hout).2 hb' hvals
  have hfirst := hhead.span.1
  have hlast : header.val < next.val := by
    obtain ⟨middle, hi, he⟩ := hrest.split
    have hfinal := he.single.span.1
    have hmid := hi.span.1
    omega
  omega

theorem empty_identity {C : context} (ins outs : List types.ValueType)
    (h : Instrs_ok C [] (.mk_functype (.mk_list (ins.map Translate.valueType))
      (.mk_list (outs.map Translate.valueType)))) : ins = outs := by
  have hreal := DeclarativeComplete.empty_realizes (concrete_realizes ins) h
  obtain ⟨pre, hp, he⟩ := (WasmFrames.realizes_append_concrete false [] ins _).mp hreal
  have hp' := (Sequence.realizes_empty _).mp hp
  have hm : ins.map Translate.valueType = outs.map Translate.valueType := by simpa [hp'] using he.symm
  clear h hreal he hp hp' pre
  induction ins generalizing outs with
  | nil => cases outs <;> simp_all
  | cons i ins ih =>
    cases outs with
    | nil => simp at hm
    | cons o outs =>
      have hs := List.cons.inj hm
      have hio := Translate.valueType_injective hs.1
      simp [hio, ih outs hs.2]

theorem atom_block {data : Slice U8} {env : module.Env} {ctx : code.Context} {index : U32}
    (limits : EnvironmentWithinLimits env) (bt : signature.BlockType)
    {tokens : List Token} {ops : List instr} (he : Emits tokens ops)
    (smaller : SmallerPrograms data env ctx index ([Token.block bt] ++ tokens ++ [Token.end_]).length) :
    AtomProgram data env ctx index ([.block bt] ++ tokens ++ [Token.end_]) (.BLOCK (blockType bt) ops) := by
  intro C st f next front input output hm hl hb hbytes ht htyped
  cases htyped with
  | block _ _ _ input output hbt hbody _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    exact run_closed_child limits .block (Or.inl rfl) bt tokens ops (smaller tokens ops (by simp) he)
      C st f next front ins outs hm hl hb hbytes hin hout (by simpa [Frames.Form.args] using ht)
      hbody (by simp)

theorem atom_loop {data : Slice U8} {env : module.Env} {ctx : code.Context} {index : U32}
    (limits : EnvironmentWithinLimits env) (bt : signature.BlockType)
    {tokens : List Token} {ops : List instr} (he : Emits tokens ops)
    (smaller : SmallerPrograms data env ctx index ([Token.loop bt] ++ tokens ++ [Token.end_]).length) :
    AtomProgram data env ctx index ([.loop bt] ++ tokens ++ [Token.end_]) (.LOOP (blockType bt) ops) := by
  intro C st f next front input output hm hl hb hbytes ht htyped
  cases htyped with
  | loop _ _ _ input output hbt hbody _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    exact run_closed_child limits .loop (Or.inr (Or.inl rfl)) bt tokens ops (smaller tokens ops (by simp) he)
      C st f next front ins outs hm hl hb hbytes hin hout (by simpa [Frames.Form.args] using ht)
      hbody (by simp)

theorem atom_ifEnd {data : Slice U8} {env : module.Env} {ctx : code.Context} {index : U32}
    (limits : EnvironmentWithinLimits env) (bt : signature.BlockType)
    {tokens : List Token} {ops : List instr} (he : Emits tokens ops)
    (smaller : SmallerPrograms data env ctx index ([Token.if_ bt] ++ tokens ++ [Token.end_]).length) :
    AtomProgram data env ctx index ([.if_ bt] ++ tokens ++ [Token.end_]) (.IFELSE (blockType bt) ops []) := by
  intro C st f next front input output hm hl hb hbytes ht htyped
  cases htyped with
  | «if» _ _ _ _ input output hbt hbody hempty _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    exact run_closed_child limits .then_ (Or.inr (Or.inr rfl)) bt tokens ops (smaller tokens ops (by simp) he)
      C st f next front ins outs hm hl hb hbytes hin hout ht hbody (fun _ => empty_identity ins outs hempty)

theorem atom_ifElse {data : Slice U8} {env : module.Env} {ctx : code.Context} {index : U32}
    (limits : EnvironmentWithinLimits env) (bt : signature.BlockType)
    {yesTokens noTokens : List Token} {yes no : List instr}
    (hyes : Emits yesTokens yes) (hno : Emits noTokens no)
    (smaller : SmallerPrograms data env ctx index
      ([Token.if_ bt] ++ yesTokens ++ [Token.else_] ++ noTokens ++ [Token.end_]).length) :
    AtomProgram data env ctx index ([.if_ bt] ++ yesTokens ++ [.else_] ++ noTokens ++ [.end_])
      (.IFELSE (blockType bt) yes no) := by
  intro C st f next front input output hm hl hb hbytes ht htyped
  cases htyped with
  | «if» _ _ _ _ input output hbt hyesBody hnoBody _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    obtain ⟨header, hhead, hrest⟩ := Consumed.cons_iff.mp
      (show Consumed data st.core.pos (.if_ bt :: (yesTokens ++ [.else_] ++ noTokens ++ [.end_])) next by
        simpa using hbytes)
    obtain ⟨entered, henter, hpos, heffect, hbounds⟩ :=
      execute_enter f data env ctx index header .then_ (Or.inr (Or.inr rfl)) bt ins outs front
        limits hb hhead hin hout ht
    obtain ⟨remaining, base, hlen, hbase, hreal, hc, hblocks, hv⟩ := heffect
    let child : Frame entered :=
      ⟨⟨st.core.ctrls.val, (Frames.Saved.fresh base .then_ bt ins outs).ctrl,
        f.core.outer ++ remaining, ins.map code.StackType.Val, hc, hv, by
          simpa [Frames.Saved.fresh] using hbase⟩,
        st.blocks.val, bt, hblocks, by simp [f.blocks, f.core.ctrls, f.aligned]⟩
    have hlabel : Labels env entered (Frames.enter C .then_ ins outs) :=
      labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        child.core.current bt outs hc hblocks hout
    obtain ⟨yesEnd, hybytes, hnbytes⟩ := Consumed.split
      (show Consumed data entered.core.pos (yesTokens ++ ([.else_] ++ noTokens ++ [.end_])) next by
        simpa [hpos, List.append_assoc] using hrest)
    obtain ⟨yesState, hyesRun, hyesPos, hyesOut, hyesBounds⟩ :=
      smaller yesTokens yes (by simp) hyes _ entered child yesEnd
        (ins.map Translate.valueType) (outs.map Translate.valueType) (hm.enter _) hlabel hbounds
        hybytes (concrete_realizes ins) hyesBody
    obtain ⟨yesPoly, yesOperands, hyc, hyv, hyr⟩ := hyesOut.1
    let yesFrame : Frame yesState :=
      ⟨⟨child.core.parents, {child.core.current with polymorphic_base := yesPoly},
        child.core.outer, yesOperands, hyc, hyv, child.core.base⟩,
        child.parents, child.current, by rw [hyesOut.2]; exact child.blocks, child.aligned⟩
    obtain ⟨elseStart, hatElse, hnoBytes⟩ := Consumed.cons_iff.mp
      (show Consumed data yesState.core.pos (.else_ :: (noTokens ++ [.end_])) next by
        simpa [hyesPos] using hnbytes)
    have hcapIns : (f.core.outer ++ remaining).length + ins.length ≤ Usize.max := by
      have hvc := entered.core.vals.property
      simpa [hv, List.length_append, List.length_map, Nat.add_assoc] using hvc
    have hcapOuts : (f.core.outer ++ remaining).length + outs.length ≤ Usize.max := by
      have hlimits := signature_limits limits bt ins outs hin hout
      have hvc := hb.val_capacity
      rw [f.core.vals, List.length_append] at hvc
      simp only [List.length_append]; omega
    obtain ⟨elseState, helseRun, helsePos, hec, heb, hev⟩ :=
      execute_else yesFrame data env ctx index elseStart ins outs hatElse hin hout rfl hyr hcapIns
    let elseFrame : Frame elseState :=
      ⟨⟨yesFrame.core.parents, {yesFrame.core.current with kind := .Else, polymorphic_base := false},
        yesFrame.core.outer, ins.map code.StackType.Val, hec, hev, yesFrame.core.base⟩,
        yesFrame.parents, yesFrame.current, by rw [heb]; exact yesFrame.blocks, yesFrame.aligned⟩
    have hlabelElse : Labels env elseState (Frames.enter C .then_ ins outs) := by
      apply labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        elseFrame.core.current bt outs hec _ hout
      rw [heb, hyesOut.2]
      exact hblocks
    have heBounds : Bounds data elseState := by
      refine restore_bounds hbounds ?_ (by rw [helsePos]; exact hatElse.span.2) ?_ ?_
      · have hh := hybytes.span.1
        have he := hatElse.span.1
        rw [helsePos]
        rw [hyesPos] at he
        omega
      · simp [hev, yesFrame, child, hv]
      · simp [heb, hyesOut.2]
    obtain ⟨s, hnoRun, hp', hc', hb', hv'⟩ := execute_body
      (smaller noTokens no (by simp; omega) hno) _ elseState elseFrame next ins outs
      (hm.enter _) hlabelElse heBounds (by simpa [helsePos] using hnoBytes) hin hout
      (concrete_realizes ins) hnoBody (by simp [elseFrame]) hcapOuts
    have hvals : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val := by
      have hne : st.core.ctrls.val ≠ [] := by simpa using f.nonempty
      simpa [elseFrame, yesFrame, child, hne] using hv'
    refine ⟨s, ((henter.append hyesRun).append helseRun).append hnoRun, hp',
      resume_parent f remaining front outs (by simpa [f.core.poly_eq] using hreal) hc' hb' hvals, ?_⟩
    apply closed_bounds f hb next remaining outs hp' hbytes.span.2 _ hlen
      (signature_limits limits bt ins outs hin hout).2 hb' hvals
    have hf := hhead.span.1
    have hrest' := hnbytes.span.2
    have hy := hybytes.span.1
    have hel := hatElse.span.1
    rw [hyesPos] at hel
    have hn := hnoBytes.span.1
    rw [hpos] at hy
    omega

end Itasca.MultiValue.Completeness
