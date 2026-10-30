import Itasca.Wasm2.Complete.Program
import Itasca.Wasm2.Control.EnterStep
import Itasca.Wasm2.Control.EndStep

/-!
# Completeness of structured control

Executes `block`, `loop` and `if` (with and without `else`) from independent encodings and
generated typing. `execute_enter`, `execute_else` and `execute_end` run the delimiters,
`execute_body` and `run_closed_child` run nested bodies with the parent frame suspended, and
`atom_block`, `atom_loop`, `atom_ifEnd` and `atom_ifElse` yield an `AtomProgram` for each form.
`blocktype_signature` and `labels_push` connect block descriptors to the SpecTec label context.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

theorem blocktype_signature {env : metadata.Env} {ctx : code.Context} {C : context}
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

theorem signature_limits {env : metadata.Env} (limits : Profile.EnvironmentWithinLimits env)
    (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs) :
    ins.length ≤ 1000 ∧ outs.length ≤ 1000 := by
  cases bt with
  | Empty => simp [inputs, outputs, resolve] at hin hout; simp_all
  | Value t => simp [inputs, outputs, resolve] at hin hout; subst ins; subst outs; simp
  | TypeIndex index =>
    have hi : index.val < env.types.val.length := by
      by_contra he; simp [inputs, resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hin
    have h := (limits.types _ (List.getElem_mem hi)).bounds
    simp [inputs, outputs, resolve, List.getElem?_eq_getElem hi] at hin hout
    simpa [← hin, ← hout] using h

theorem labels_push {env : metadata.Env} {C : context} {st s : code.BodyState}
    (hl : Labels env st C) (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (frame : code.Ctrl) (bt : signature.BlockType) (ts : List wasm_types.ValueType)
    (hc : s.core.ctrls.val = st.core.ctrls.val ++ [frame])
    (hb : s.blocks.val = st.blocks.val ++ [bt])
    (ht : resolve env (target frame.kind bt) = some ts) :
    Labels env s (Control.labelContext (ts.map Translate.valueType) ++ C) := by
  intro depth
  cases depth with
  | zero => simp [Control.labelContext_labels, labelTypes, labelAt, hc, hb, ht]
  | succ depth =>
    rw [Control.labelContext_labels]
    simp only [List.getElem?_cons_succ, hl depth]
    unfold labelTypes labelAt
    by_cases hd : depth < st.blocks.val.length
    · have hs : depth + 1 < (st.blocks.val ++ [bt]).length := by simp; omega
      have he : (st.blocks.val ++ [bt]).length - 1 - (depth + 1) = st.blocks.val.length - 1 - depth := by simp; omega
      have hbnd : st.blocks.val.length - 1 - depth < st.blocks.val.length := by omega
      have he' : st.blocks.val.length - (depth + 1) = st.blocks.val.length - 1 - depth := by omega
      simp only [code.BodyState.blocks_length] at hd hs he hbnd he'
      simp [hb, hc, hd, he', hbnd, List.getElem?_append]
    · have hs : ¬ depth + 1 < (st.blocks.val ++ [bt]).length := by simp; omega
      simp only [code.BodyState.blocks_length] at hd
      simp [hb, hd]

/-- A delimiter execution, with exact effects and no post-delimiter capacity
estimate; callers derive bounds from the enclosing entry. -/
theorem execute_end {st : code.BodyState} (f : Frame st) (data : Slice U8)
    (env : metadata.Env) (profile : ValidationProfile) (ctx : code.Context) (index : U32) (next : Usize)
    (ins outs : List wasm_types.ValueType)
    (hat : At data st.core.pos .end_ next)
    (hin : resolve env (inputs f.current) = some ins) (hout : resolve env (outputs f.current) = some outs)
    (hthen : f.core.current.kind = .Then → ins = outs)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (outs.map Translate.valueType))
    (hcap : f.core.outer.length + outs.length ≤ Usize.max) :
    ∃ s, Execution data env profile ctx index st s ∧ s.core.pos = next ∧
      s.core.ctrls.val = f.core.parents ∧ s.blocks.val = f.parents ∧
      s.core.vals.val = if f.parents = [] then f.core.outer else f.core.outer ++ outs.map code.StackType.Val := by
  have hs := hat.span
  have hinbounds : st.core.pos.val < data.length := by omega
  obtain ⟨_, hread, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hinbounds)
  obtain ⟨opcode, bytes, himm, ⟨_, hbyte⟩, hspan⟩ := hat.immediate pos hpos
  cases himm
  have hnext := hspan.empty
  obtain ⟨⟨r, s⟩, hr, hok, hp, hc, hb, hv⟩ := WP.spec_imp_exists
    (code.end_frame.complete { st with core := { st.core with pos := pos } } env false
      f.core.parents f.parents f.core.current f.current ins outs f.core.outer f.core.operands
      f.core.ctrls f.blocks f.aligned f.core.vals f.core.base hin hout ht hthen hcap)
  dsimp only at hok
  subst r
  have hstep : step { st with core := { st.core with pos := pos } } data env profile ctx index 0x0B#u8 =
      .ok (.Ok (), s) := by simpa [step] using hr
  exact ⟨s, .single f.nonempty (by simpa [hbyte] using hread)
    (code.check_opcode.complete profile _ (by decide)) hstep,
    hp.trans hnext.symm, hc, hb, hv⟩

theorem execute_else {st : code.BodyState} (f : Frame st) (data : Slice U8)
    (env : metadata.Env) (profile : ValidationProfile) (ctx : code.Context) (index : U32) (next : Usize)
    (ins outs : List wasm_types.ValueType)
    (hat : At data st.core.pos .else_ next)
    (hin : resolve env (inputs f.current) = some ins) (hout : resolve env (outputs f.current) = some outs)
    (hthen : f.core.current.kind = .Then)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (outs.map Translate.valueType))
    (hcap : f.core.outer.length + ins.length ≤ Usize.max) :
    ∃ s, Execution data env profile ctx index st s ∧ s.core.pos = next ∧
      s.core.ctrls.val = f.core.parents ++ [{ f.core.current with kind := .Else, polymorphic_base := false }] ∧
      s.blocks = st.blocks ∧ s.core.vals.val = f.core.outer ++ ins.map code.StackType.Val := by
  have hs := hat.span
  have hinbounds : st.core.pos.val < data.length := by omega
  obtain ⟨_, hread, pos, rfl, hpos⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hinbounds)
  obtain ⟨opcode, bytes, himm, ⟨_, hbyte⟩, hspan⟩ := hat.immediate pos hpos
  cases himm
  have hnext := hspan.empty
  obtain ⟨⟨r, s⟩, hr, hok, hp, hc, hb, hv⟩ := WP.spec_imp_exists
    (code.end_frame.complete { st with core := { st.core with pos := pos } } env true
      f.core.parents f.parents f.core.current f.current ins outs f.core.outer f.core.operands
      f.core.ctrls f.blocks f.aligned f.core.vals f.core.base hin hout ht hthen hcap)
  dsimp only at hok
  subst r
  have hstep : step { st with core := { st.core with pos := pos } } data env profile ctx index 0x05#u8 =
      .ok (.Ok (), s) := by simpa [step] using hr
  exact ⟨s, .single f.nonempty (by simpa [hbyte] using hread)
    (code.check_opcode.complete profile _ (by decide)) hstep,
    hp.trans hnext.symm, hc, hb, hv⟩

theorem execute_enter {st : code.BodyState} (f : Frame st) (data : Slice U8)
    (env : metadata.Env) (profile : ValidationProfile) (ctx : code.Context) (index : U32) (next : Usize)
    (form : Frames.Form) (initial : form.Initial) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (front : List valtype)
    (limits : Profile.EnvironmentWithinLimits env) (hb : Bounds data st)
    (hat : At data st.core.pos (form.token bt) next)
    (hscalar : profile = .Wasm1 → ∃ b, Wasm1.ScalarBlockByte bt b)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ form.args ins)) :
    ∃ s, Execution data env profile ctx index st s ∧ s.core.pos = next ∧
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
    (code.enter.complete { st with core := { st.core with pos := pos } } data env profile form initial
      bt next ins outs f.core.outer f.core.operands front hd hscalar hin hout hins houts f.core.vals
      f.core.base_eq hb.ctrl_capacity
      (by change st.core.vals.val.length + ins.length ≤ Usize.max; have := hb.val_capacity; omega) (by simpa [Control.polymorphic, f.core.ctrls] using ht))
  dsimp only at hok
  subst r
  have hstep : step { st with core := { st.core with pos := pos } } data env profile ctx index opcode =
      .ok (.Ok (), s) := by
    rw [hop.1]
    rcases initial with rfl | rfl | rfl <;> simpa [step, Frames.Form.opcode, Frames.Form.kind] using hr
  have hcheck : code.check_opcode profile opcode = .ok (.Ok ()) := by
    rw [hop.1]
    rcases initial with rfl | rfl | rfl <;> exact code.check_opcode.complete profile _ (by decide)
  refine ⟨s, .single f.nonempty (by simpa [hbyte] using hread) hcheck hstep, hp, heffect, ?_⟩
  obtain ⟨remaining, base, hlen, hbase, hreal, hctrls, hblocks, hvals⟩ := heffect
  apply bounds_after hb hat hp
  · have htwo := hd.span.1
    have hstart : st.core.pos.val + 2 ≤ next.val := by omega
    simp only [hvals, f.core.vals, List.length_append, List.length_map]
    omega
  · simp [hblocks]

private theorem restore_bounds {data : Slice U8} {st s : code.BodyState}
    (hb : Bounds data st) (hp : st.core.pos.val ≤ s.core.pos.val) (hpos : s.core.pos.val ≤ data.length)
    (hv : s.core.vals.val.length ≤ st.core.vals.val.length)
    (hc : s.blocks.val.length ≤ st.blocks.val.length) : Bounds data s := by
  have := hb.vals; have := hb.ctrls
  exact ⟨hb.size, hpos, by omega, by omega⟩

/-- Execute a child list and its end, preserving the original suspended
parent stack and result descriptor. -/
theorem execute_body {data : Slice U8} {env : metadata.Env} {profile : ValidationProfile}
    {ctx : code.Context} {index : U32} {tokens : List Token} {ops : List instr}
    (program : Program data env profile ctx index tokens ops) (C : context)
    (st : code.BodyState) (f : Frame st) (next : Usize)
    (ins outs : List wasm_types.ValueType)
    (hm : EnvTranslation.Matches env ctx C) (hl : Labels env st C)
    (hb : Bounds data st)
    (hbytes : ProfileConsumed profile data st.core.pos (tokens ++ [Token.end_]) next)
    (hin : resolve env (inputs f.current) = some ins) (hout : resolve env (outputs f.current) = some outs)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (ins.map Translate.valueType))
    (hbody : Instrs_ok C ops (.mk_functype (.mk_list (ins.map Translate.valueType))
      (.mk_list (outs.map Translate.valueType))))
    (hthen : f.core.current.kind = .Then → ins = outs)
    (hcap : f.core.outer.length + outs.length ≤ Usize.max)
    (hdecl : DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops)
    (hprofile : profile = .Wasm1 → Wasm1.Instructions C ops) :
    ∃ s, Execution data env profile ctx index st s ∧ s.core.pos = next ∧
      s.core.ctrls.val = f.core.parents ∧ s.blocks.val = f.parents ∧
      s.core.vals.val = if f.parents = [] then f.core.outer else f.core.outer ++ outs.map code.StackType.Val := by
  obtain ⟨middle, hinner, hend⟩ := hbytes.split
  obtain ⟨mid, hrun, hpos, hout', hbounds⟩ :=
    program C st f middle _ _ hm hl hb hinner ht hbody hdecl hprofile
  obtain ⟨g, hgp, hgc, hp, ho, hk, hbase, hreal⟩ := hout'.next
  obtain ⟨s, hclose, hp', hc', hb', hv'⟩ := execute_end g data env profile ctx index next ins outs
    (by simpa [hpos] using hend.single.1) (by simpa [hgc] using hin) (by simpa [hgc] using hout)
    (by simpa [hk] using hthen) hreal (by simpa [ho] using hcap)
  exact ⟨s, hrun.append hclose, hp', by simpa [hp] using hc', by simpa [hgp] using hb',
    by simpa [hgp, ho] using hv'⟩

private theorem concrete_realizes (ts : List wasm_types.ValueType) :
    Sequence.Realizes false (ts.map code.StackType.Val) (ts.map Translate.valueType) := by
  apply (Sequence.realizes_append_concrete false [] ts _).mpr
  exact ⟨[], by simp [Sequence.Realizes], rfl⟩

private theorem resume_parent {st s : code.BodyState} (f : Frame st)
    (remaining : List code.StackType) (front : List valtype) (outs : List wasm_types.ValueType)
    (hreal : Sequence.Realizes f.core.current.polymorphic_base remaining front)
    (hc : s.core.ctrls.val = st.core.ctrls.val) (hb : s.blocks.val = st.blocks.val)
    (hv : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val) :
    f.Output (front ++ outs.map Translate.valueType) s := by
  constructor
  · apply f.core.output_of_same_ctrls (alloc.vec.Vec.ext _ _ hc)
      (operands := remaining ++ outs.map code.StackType.Val) (by simpa [List.append_assoc] using hv)
    apply (Sequence.realizes_append_concrete _ _ _ _).mpr
    exact ⟨front, by simpa [f.core.poly_eq] using hreal, rfl⟩
  · exact alloc.vec.Vec.ext _ _ hb

private theorem closed_bounds {data : Slice U8} {st s : code.BodyState}
    (f : Frame st) (hb : Bounds data st) (next : Usize)
    (remaining : List code.StackType) (outs : List wasm_types.ValueType)
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
theorem run_closed_child {data : Slice U8} {env : metadata.Env} {profile : ValidationProfile}
    {ctx : code.Context} {index : U32}
    (limits : Profile.EnvironmentWithinLimits env) (form : Frames.Form) (initial : form.Initial)
    (bt : signature.BlockType) (tokens : List Token) (ops : List instr)
    (program : Program data env profile ctx index tokens ops)
    (C : context) (st : code.BodyState) (f : Frame st) (next : Usize)
    (front : List valtype) (ins outs : List wasm_types.ValueType)
    (hm : EnvTranslation.Matches env ctx C) (hl : Labels env st C) (hb : Bounds data st)
    (hbytes : ProfileConsumed profile data st.core.pos ([form.token bt] ++ tokens ++ [Token.end_]) next)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (ht : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ form.args ins))
    (hbody : Instrs_ok (Frames.enter C form ins outs) ops
      (.mk_functype (.mk_list (ins.map Translate.valueType)) (.mk_list (outs.map Translate.valueType))))
    (hthen : form = .then_ → ins = outs)
    (hdecl : DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops)
    (hprofile : profile = .Wasm1 → Wasm1.Instructions (Frames.enter C form ins outs) ops) :
    ∃ s, Execution data env profile ctx index st s ∧ s.core.pos = next ∧
      f.Output (front ++ outs.map Translate.valueType) s ∧ Bounds data s := by
  obtain ⟨header, hheadc, hrest⟩ :=
    (show ProfileConsumed profile data st.core.pos ([form.token bt] ++ (tokens ++ [Token.end_])) next by
      simpa [List.append_assoc] using hbytes).split
  obtain ⟨hhead, hhead1⟩ := hheadc.single
  have hscalar : profile = .Wasm1 → ∃ b, Wasm1.ScalarBlockByte bt b := by
    intro hp
    have hok := (hhead1 hp).blockTokenOk
    rcases initial with rfl | rfl | rfl <;> exact hok
  obtain ⟨entered, henter, hpos, heffect, hbounds⟩ :=
    execute_enter f data env profile ctx index header form initial bt ins outs front limits hb hhead
      hscalar hin hout ht
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
      rcases initial with rfl | rfl | rfl <;> simp_all [child, Frames.Saved.fresh, Frames.Form.kind]) hcap hdecl
      hprofile
  have hvals : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val := by
    have hne : st.core.ctrls.val ≠ [] := by simpa using f.nonempty
    simpa [child, hne] using hv'
  refine ⟨s, henter.append hrun, hp', resume_parent f remaining front outs
    (by simpa [f.core.poly_eq] using hreal) hc' hb' hvals, ?_⟩
  apply closed_bounds f hb next remaining outs hp' hbytes.to_wasm2.span.2 _ hlen
    (signature_limits limits bt ins outs hin hout).2 hb' hvals
  have hfirst := hhead.span.1
  have hlast : header.val < next.val := by
    obtain ⟨middle, hi, he⟩ := hrest.split
    have hfinal := he.single.1.span.1
    have hmid := hi.to_wasm2.span.1
    omega
  omega

theorem empty_identity {C : context} (ins outs : List wasm_types.ValueType)
    (h : Instrs_ok C [] (.mk_functype (.mk_list (ins.map Translate.valueType))
      (.mk_list (outs.map Translate.valueType)))) : ins = outs := by
  have hreal := DeclarativeComplete.empty_realizes (concrete_realizes ins) h
  obtain ⟨pre, hp, he⟩ := (Sequence.realizes_append_concrete false [] ins _).mp hreal
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

/-- A Wasm 1.0 block type has no parameters and its result list is the label of its body. -/
theorem result_types {env : metadata.Env} {bt : signature.BlockType} {result : Option valtype}
    {ins outs : List wasm_types.ValueType} (hbt : blockType bt = ._RESULT result)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs) :
    ins = [] ∧ outs.map Translate.valueType = result.toList := by
  cases bt with
  | Empty =>
    simp only [blockType, blocktype._RESULT.injEq] at hbt
    subst hbt
    simp_all [inputs, outputs, resolve]
  | Value t =>
    simp only [blockType, blocktype._RESULT.injEq] at hbt
    subst hbt
    simp only [inputs, outputs, resolve, Option.some.injEq] at hin hout
    subst hin hout
    simp
  | TypeIndex i => simp [blockType] at hbt

theorem atom_block {data : Slice U8} {env : metadata.Env} {profile : ValidationProfile}
    {ctx : code.Context} {index : U32}
    (limits : Profile.EnvironmentWithinLimits env) (bt : signature.BlockType)
    {tokens : List Token} {ops : List instr} (he : Emits tokens ops)
    (smaller : SmallerPrograms data env profile ctx index
      ([Token.block bt] ++ tokens ++ [Token.end_]).length) :
    AtomProgram data env profile ctx index ([.block bt] ++ tokens ++ [Token.end_])
      (.BLOCK (blockType bt) ops) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hdecl hprofile
  cases htyped with
  | block _ _ _ input output hbt hbody _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    exact run_closed_child limits .block (Or.inl rfl) bt tokens ops (smaller tokens ops (by simp) he)
      C st f next front ins outs hm hl hb hbytes hin hout (by simpa [Frames.Form.args] using ht)
      hbody (by simp) hdecl (fun hp => by
        obtain ⟨result, hr, hops⟩ := (hprofile hp).block_inv
        have hres := result_types hr hin hout
        exact hops.congr_labels _ (by simp [Frames.enter, Frames.Form.label, hres.2]))

theorem atom_loop {data : Slice U8} {env : metadata.Env} {profile : ValidationProfile}
    {ctx : code.Context} {index : U32}
    (limits : Profile.EnvironmentWithinLimits env) (bt : signature.BlockType)
    {tokens : List Token} {ops : List instr} (he : Emits tokens ops)
    (smaller : SmallerPrograms data env profile ctx index
      ([Token.loop bt] ++ tokens ++ [Token.end_]).length) :
    AtomProgram data env profile ctx index ([.loop bt] ++ tokens ++ [Token.end_])
      (.LOOP (blockType bt) ops) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hdecl hprofile
  cases htyped with
  | loop _ _ _ input output hbt hbody _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    exact run_closed_child limits .loop (Or.inr (Or.inl rfl)) bt tokens ops (smaller tokens ops (by simp) he)
      C st f next front ins outs hm hl hb hbytes hin hout (by simpa [Frames.Form.args] using ht)
      hbody (by simp) hdecl (fun hp => by
        obtain ⟨result, hr, hops⟩ := (hprofile hp).loop_inv
        have hres := result_types hr hin hout
        exact hops.congr_labels _ (by simp [Frames.enter, Frames.Form.label, hres.1]))

theorem atom_ifEnd {data : Slice U8} {env : metadata.Env} {profile : ValidationProfile}
    {ctx : code.Context} {index : U32}
    (limits : Profile.EnvironmentWithinLimits env) (bt : signature.BlockType)
    {tokens : List Token} {ops : List instr} (he : Emits tokens ops)
    (smaller : SmallerPrograms data env profile ctx index
      ([Token.if_ bt] ++ tokens ++ [Token.end_]).length) :
    AtomProgram data env profile ctx index ([.if_ bt] ++ tokens ++ [Token.end_])
      (.IFELSE (blockType bt) ops []) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hdecl hprofile
  cases htyped with
  | «if» _ _ _ _ input output hbt hbody hempty _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    exact run_closed_child limits .then_ (Or.inr (Or.inr rfl)) bt tokens ops (smaller tokens ops (by simp) he)
      C st f next front ins outs hm hl hb hbytes hin hout ht hbody (fun _ => empty_identity ins outs hempty)
      (DeclaredReferences.Instruction.ifElse_iff.mp hdecl).1 (fun hp => by
        obtain ⟨result, hr, hops, _⟩ := (hprofile hp).ifElse_inv
        have hres := result_types hr hin hout
        exact hops.congr_labels _ (by simp [Frames.enter, Frames.Form.label, hres.2]))

theorem atom_ifElse {data : Slice U8} {env : metadata.Env} {profile : ValidationProfile}
    {ctx : code.Context} {index : U32}
    (limits : Profile.EnvironmentWithinLimits env) (bt : signature.BlockType)
    {yesTokens noTokens : List Token} {yes no : List instr}
    (hyes : Emits yesTokens yes) (hno : Emits noTokens no)
    (smaller : SmallerPrograms data env profile ctx index
      ([Token.if_ bt] ++ yesTokens ++ [Token.else_] ++ noTokens ++ [Token.end_]).length) :
    AtomProgram data env profile ctx index ([.if_ bt] ++ yesTokens ++ [.else_] ++ noTokens ++ [.end_])
      (.IFELSE (blockType bt) yes no) := by
  intro C st f next front input output hm hl hb hbytes ht htyped hdecl hprofile
  cases htyped with
  | «if» _ _ _ _ input output hbt hyesBody hnoBody _ _ _ =>
    obtain ⟨ins, outs, hin, hout, rfl, rfl⟩ := blocktype_signature hm bt hbt
    have harms : profile = .Wasm1 →
        Wasm1.Instructions (Frames.enter C .then_ ins outs) yes ∧
        Wasm1.Instructions (Frames.enter C .then_ ins outs) no := by
      intro hp
      obtain ⟨result, hr, hy, hn⟩ := (hprofile hp).ifElse_inv
      have hres := result_types hr hin hout
      have hl' : (Control.labelContext result.toList ++ C).LABELS =
          (Frames.enter C .then_ ins outs).LABELS := by
        simp [Frames.enter, Frames.Form.label, hres.2]
      exact ⟨hy.congr_labels _ hl', hn.congr_labels _ hl'⟩
    obtain ⟨header, hheadc, hrest⟩ :=
      (show ProfileConsumed profile data st.core.pos
          ([.if_ bt] ++ (yesTokens ++ [.else_] ++ noTokens ++ [.end_])) next by
        simpa [List.append_assoc] using hbytes).split
    obtain ⟨hhead, hhead1⟩ := hheadc.single
    obtain ⟨entered, henter, hpos, heffect, hbounds⟩ :=
      execute_enter f data env profile ctx index header .then_ (Or.inr (Or.inr rfl)) bt ins outs front
        limits hb hhead (fun hp => (hhead1 hp).blockTokenOk) hin hout ht
    obtain ⟨remaining, base, hlen, hbase, hreal, hc, hblocks, hv⟩ := heffect
    let child : Frame entered :=
      ⟨⟨st.core.ctrls.val, (Frames.Saved.fresh base .then_ bt ins outs).ctrl,
        f.core.outer ++ remaining, ins.map code.StackType.Val, hc, hv, by
          simpa [Frames.Saved.fresh] using hbase⟩,
        st.blocks.val, bt, hblocks, by simp [f.blocks, f.core.ctrls, f.aligned]⟩
    have hlabel : Labels env entered (Frames.enter C .then_ ins outs) :=
      labels_push hl (by simp [f.blocks, f.core.ctrls, f.aligned])
        child.core.current bt outs hc hblocks hout
    obtain ⟨yesEnd, hybytes, hnbytes⟩ := ProfileConsumed.split
      (show ProfileConsumed profile data entered.core.pos
          (yesTokens ++ ([.else_] ++ noTokens ++ [.end_])) next by
        simpa [hpos, List.append_assoc] using hrest)
    obtain ⟨yesState, hyesRun, hyesPos, hyesOut, hyesBounds⟩ :=
      smaller yesTokens yes (by simp) hyes _ entered child yesEnd
        (ins.map Translate.valueType) (outs.map Translate.valueType) (hm.enter _) hlabel hbounds
        hybytes (concrete_realizes ins) hyesBody (DeclaredReferences.Instruction.ifElse_iff.mp hdecl).1
        (fun hp => (harms hp).1)
    obtain ⟨yesPoly, yesOperands, hyc, hyv, hyr⟩ := hyesOut.1
    let yesFrame : Frame yesState :=
      ⟨⟨child.core.parents, {child.core.current with polymorphic_base := yesPoly},
        child.core.outer, yesOperands, hyc, hyv, child.core.base⟩,
        child.parents, child.current, by rw [hyesOut.2]; exact child.blocks, child.aligned⟩
    obtain ⟨elseStart, hatElsec, hnoBytes⟩ := ProfileConsumed.split
      (show ProfileConsumed profile data yesState.core.pos ([.else_] ++ (noTokens ++ [.end_])) next by
        simpa [hyesPos, List.append_assoc] using hnbytes)
    have hatElse := hatElsec.single.1
    have hcapIns : (f.core.outer ++ remaining).length + ins.length ≤ Usize.max := by
      have hvc := entered.core.vals.property
      simpa [hv, List.length_append, List.length_map, Nat.add_assoc] using hvc
    have hcapOuts : (f.core.outer ++ remaining).length + outs.length ≤ Usize.max := by
      have hlimits := signature_limits limits bt ins outs hin hout
      have hvc := hb.val_capacity
      rw [f.core.vals, List.length_append] at hvc
      simp only [List.length_append]; omega
    obtain ⟨elseState, helseRun, helsePos, hec, heb, hev⟩ :=
      execute_else yesFrame data env profile ctx index elseStart ins outs hatElse hin hout rfl hyr hcapIns
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
      · have hh := hybytes.to_wasm2.span.1
        have he := hatElse.span.1
        rw [helsePos]
        rw [hyesPos] at he
        omega
      · simp [hev, yesFrame, child, hv]
      · simp [heb, hyesOut.2]
    obtain ⟨s, hnoRun, hp', hc', hb', hv'⟩ := execute_body
      (smaller noTokens no (by simp; omega) hno) _ elseState elseFrame next ins outs
      (hm.enter _) hlabelElse heBounds (by simpa [helsePos] using hnoBytes) hin hout
      (concrete_realizes ins) hnoBody (by simp [elseFrame]) hcapOuts (DeclaredReferences.Instruction.ifElse_iff.mp hdecl).2
      (fun hp => (harms hp).2)
    have hvals : s.core.vals.val = f.core.outer ++ remaining ++ outs.map code.StackType.Val := by
      have hne : st.core.ctrls.val ≠ [] := by simpa using f.nonempty
      simpa [elseFrame, yesFrame, child, hne] using hv'
    refine ⟨s, ((henter.append hyesRun).append helseRun).append hnoRun, hp',
      resume_parent f remaining front outs (by simpa [f.core.poly_eq] using hreal) hc' hb' hvals, ?_⟩
    apply closed_bounds f hb next remaining outs hp' hbytes.to_wasm2.span.2 _ hlen
      (signature_limits limits bt ins outs hin hout).2 hb' hvals
    have hf := hhead.span.1
    have hrest' := hnbytes.to_wasm2.span.2
    have hy := hybytes.to_wasm2.span.1
    have hel := hatElse.span.1
    rw [hyesPos] at hel
    have hn := hnoBytes.to_wasm2.span.1
    rw [hpos] at hy
    omega

end Itasca.Wasm2.Completeness
