import Itasca.Support.Result
import Itasca.Module.ModuleReaders

open Aeneas Aeneas.Std

namespace Itasca.StreamSource

/-- Successful source calls expose fixed logical regions. Read errors are
permitted; neither availability nor a canonical module split is assumed. -/
structure Coherent {S : Type} (source : stream.Source S) (state : S)
    (environment code tail : List U8) : Prop where
  environment_eq : ∀ bytes, source.environment state = .ok (.Ok bytes) →
    bytes.val = environment
  code_len_eq : ∀ len, source.code_len state = .ok len → len.val = code.length
  code_eq : ∀ first last bytes, first.val ≤ last.val → last.val ≤ code.length →
    source.code state first last = .ok (.Ok bytes) →
    bytes.val = code.slice first.val last.val
  tail_eq : ∀ bytes, source.tail state = .ok (.Ok bytes) → bytes.val = tail

/-- Availability is a completeness premise. It prescribes successful reads
without identifying the regions with a valid module or requiring canonical splitting. -/
structure Available {S : Type} (source : stream.Source S) (state : S)
    (environment code tail : List U8) : Prop where
  environment_read : ∃ bytes, source.environment state = .ok (.Ok bytes) ∧
    bytes.val = environment
  code_len_read : ∃ len, source.code_len state = .ok len ∧ len.val = code.length
  code_read : ∀ first last, first.val ≤ last.val → last.val ≤ code.length →
    ∃ bytes, source.code state first last = .ok (.Ok bytes) ∧
      bytes.val = code.slice first.val last.val
  tail_read : ∃ bytes, source.tail state = .ok (.Ok bytes) ∧ bytes.val = tail

/-- Source callbacks return ordinary modeled results. Unlike availability,
this allows Rust errors, and unlike coherence it imposes no byte equality. -/
structure CallbacksTotal {S : Type} (source : stream.Source S) (state : S) : Prop where
  environment_returns : ∃ r, source.environment state = .ok r
  code_len_returns : ∃ len, source.code_len state = .ok len
  code_returns : ∀ first last, ∃ r, source.code state first last = .ok r
  tail_returns : ∃ r, source.tail state = .ok r

/-- Unsigned length decoding retains its U32 binary encoding after conversion
into the host-size integer used by the streaming driver. -/
def LenPost (data : Slice U8) (start : Usize) :
    core.result.Result (Usize × Usize) error.Error → Prop
  | .Ok (len, next) => ∃ value : U32, len.val = value.val ∧
      Leb128.Decoded data start value next
  | .Err _ => True

end Itasca.StreamSource

namespace Itasca

/-- Offset arithmetic is total on arbitrary operands and checks the module cap
before addition, so no machine overflow is possible. -/
@[step]
theorem limits.add_offset.spec (a b : Usize) :
    limits.add_offset a b ⦃ r => match r with
      | .Ok total => total.val = a.val + b.val ∧ total.val ≤ limits.MAX_MODULE_BYTES.val
      | .Err e => e = .ModuleTooLarge ∧ limits.MAX_MODULE_BYTES.val < a.val + b.val ⦄ := by
  unfold limits.add_offset
  step*

theorem limits.add_offset.total (a b : Usize) :
    ∃ r, limits.add_offset a b = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (limits.add_offset.spec a b)
  exact ⟨r, hr⟩

theorem limits.add_offset.complete (a b : Usize)
    (hbound : a.val + b.val ≤ limits.MAX_MODULE_BYTES.val) :
    ∃ total, limits.add_offset a b = .ok (.Ok total) ∧ total.val = a.val + b.val := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (limits.add_offset.spec a b)
  cases r with
  | Ok total => exact ⟨total, hr, hp.1⟩
  | Err e => omega

@[step]
theorem stream.read_len.spec (data : Slice U8) (start : Usize) :
    stream.read_len data start ⦃ StreamSource.LenPost data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e => cases e <;> simp [stream.read_len, hr, StreamSource.LenPost]
  | Ok pair =>
    obtain ⟨value, next⟩ := pair
    simp only [stream.read_len, hr, bind_ok]
    step
    exact ⟨value, by scalar_tac, hp⟩

theorem stream.read_len.total (data : Slice U8) (start : Usize) :
    ∃ r, stream.read_len data start = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (stream.read_len.spec data start)
  exact ⟨r, hr⟩

theorem stream.read_len.sound (data : Slice U8) (start len next : Usize)
    (h : stream.read_len data start = .ok (.Ok (len, next))) :
    ∃ value : U32, len.val = value.val ∧ Leb128.Decoded data start value next := by
  have hs := stream.read_len.spec data start
  simpa [h, StreamSource.LenPost] using hs

theorem stream.read_len.success_span (data : Slice U8) (start len next : Usize)
    (h : stream.read_len data start = .ok (.Ok (len, next))) :
    start.val < next.val ∧ next.val ≤ start.val + 5 ∧ next.val ≤ data.length := by
  obtain ⟨value, _, hd⟩ := stream.read_len.sound data start len next h
  exact hd.span

theorem stream.read_len.complete (data : Slice U8) (start next : Usize)
    (value : U32) (h : Leb128.Decoded data start value next) :
    ∃ len, stream.read_len data start = .ok (.Ok (len, next)) ∧ len.val = value.val := by
  have hr := reader.read_u32_leb.complete data start value next h
  have hs : stream.read_len data start ⦃ r =>
      ∃ len, r = .Ok (len, next) ∧ len.val = value.val ⦄ := by
    simp only [stream.read_len, hr, bind_ok]
    step
    exact ⟨_, rfl, by scalar_tac⟩
  obtain ⟨_, hr, len, rfl, hv⟩ := WP.spec_imp_exists hs
  exact ⟨len, hr, hv⟩

/-- Exact reads need only the reached code callback to return, and permit its
ordinary error result. The ordering premise prevents subtraction underflow. -/
@[step]
theorem stream.read_exact.spec {S : Type} (source : stream.Source S) (state : S)
    (first last : Usize) (horder : first.val ≤ last.val)
    (hreturn : ∃ r, source.code state first last = .ok r) :
    stream.read_exact source state first last ⦃ r => match r with
      | .Ok bytes => source.code state first last = .ok (.Ok bytes) ∧
          bytes.length = last.val - first.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr⟩ := hreturn
  cases r with
  | Err e => simp [stream.read_exact, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok bytes =>
    simp only [stream.read_exact, hr, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step
    split
    · simp
    · simp only [WP.spec_ok]
      exact ⟨trivial, by scalar_tac⟩

theorem stream.read_exact.total {S : Type} (source : stream.Source S) (state : S)
    (first last : Usize) (horder : first.val ≤ last.val)
    (hreturn : ∃ r, source.code state first last = .ok r) :
    ∃ r, stream.read_exact source state first last = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (stream.read_exact.spec source state first last horder hreturn)
  exact ⟨r, hr⟩


/-- Acceptance reveals the actual successful source call, without a callback
termination premise for this or any other read. -/
theorem stream.read_exact.accepted {S : Type} (source : stream.Source S) (state : S)
    (first last : Usize) (bytes : Slice U8) (horder : first.val ≤ last.val)
    (h : stream.read_exact source state first last = .ok (.Ok bytes)) :
    source.code state first last = .ok (.Ok bytes) ∧ bytes.length = last.val - first.val := by
  have hex : ∃ r, source.code state first last = .ok r := by
    unfold stream.read_exact at h
    obtain ⟨r, hr, _⟩ := ResultFacts.bind_ok_inv _ _ _ h
    exact ⟨r, hr⟩
  have hs := stream.read_exact.spec source state first last horder hex
  simpa [h] using hs

theorem stream.read_exact.sound {S : Type} (source : stream.Source S) (state : S)
    (environment code tail : List U8) (hc : StreamSource.Coherent source state environment code tail)
    (first last : Usize) (bytes : Slice U8) (horder : first.val ≤ last.val)
    (hbound : last.val ≤ code.length)
    (h : stream.read_exact source state first last = .ok (.Ok bytes)) :
    bytes.val = code.slice first.val last.val ∧ bytes.length = last.val - first.val := by
  obtain ⟨hr, hn⟩ := stream.read_exact.accepted source state first last bytes horder h
  exact ⟨hc.code_eq first last bytes horder hbound hr, hn⟩

theorem stream.read_exact.complete {S : Type} (source : stream.Source S) (state : S)
    (first last : Usize) (bytes : Slice U8) (horder : first.val ≤ last.val)
    (hread : source.code state first last = .ok (.Ok bytes))
    (hlen : bytes.length = last.val - first.val) :
    stream.read_exact source state first last = .ok (.Ok bytes) := by
  have hs : stream.read_exact source state first last ⦃ r => r = .Ok bytes ⦄ := by
    simp only [stream.read_exact, hread, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step*
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- The concrete slice source returns exact bounded views and rejects other
ranges with an ordinary host error. -/
@[step]
theorem stream.SliceSource.code_spec (state : stream.SliceSource) (first last : Usize) :
    stream.SliceSource.Insts.ItascaStreamSource.code state first last ⦃ r => match r with
      | .Ok bytes => first.val ≤ last.val ∧ last.val ≤ state.code.length ∧
          bytes.val = state.code.val.slice first.val last.val
      | .Err e => e = .Host ∧ (last.val < first.val ∨ state.code.length < last.val) ⦄ := by
  unfold stream.SliceSource.Insts.ItascaStreamSource.code
  step*

theorem stream.SliceSource.coherent (state : stream.SliceSource) :
    StreamSource.Coherent stream.SliceSource.Insts.ItascaStreamSource state
      state.env.val state.code.val state.tail.val := by
  constructor
  · intro bytes h
    have he : state.env = bytes := by
      simpa [stream.SliceSource.Insts.ItascaStreamSource,
        stream.SliceSource.Insts.ItascaStreamSource.environment] using h
    exact congrArg Slice.val he.symm
  · intro len h
    have he : Slice.len state.code = len := by
      simpa [stream.SliceSource.Insts.ItascaStreamSource,
        stream.SliceSource.Insts.ItascaStreamSource.code_len] using h
    simp [← he]
  · intro first last bytes _ _ h
    have hs := stream.SliceSource.code_spec state first last
    change stream.SliceSource.Insts.ItascaStreamSource.code state first last = _ at h
    simp only [h, WP.spec_ok] at hs
    exact hs.2.2
  · intro bytes h
    have he : state.tail = bytes := by
      simpa [stream.SliceSource.Insts.ItascaStreamSource,
        stream.SliceSource.Insts.ItascaStreamSource.tail] using h
    exact congrArg Slice.val he.symm

theorem stream.SliceSource.available (state : stream.SliceSource) :
    StreamSource.Available stream.SliceSource.Insts.ItascaStreamSource state
      state.env.val state.code.val state.tail.val := by
  constructor
  · exact ⟨state.env, rfl, rfl⟩
  · exact ⟨Slice.len state.code, rfl, rfl⟩
  · intro first last horder hbound
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.SliceSource.code_spec state first last)
    cases r with
    | Ok bytes => exact ⟨bytes, hr, hp.2.2⟩
    | Err e => simp only [Slice.length] at hp; omega
  · exact ⟨state.tail, rfl, rfl⟩

theorem stream.SliceSource.callbacks_total (state : stream.SliceSource) :
    StreamSource.CallbacksTotal stream.SliceSource.Insts.ItascaStreamSource state := by
  constructor
  · exact ⟨.Ok state.env, rfl⟩
  · exact ⟨Slice.len state.code, rfl⟩
  · intro first last
    obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (stream.SliceSource.code_spec state first last)
    exact ⟨r, hr⟩
  · exact ⟨.Ok state.tail, rfl⟩

end Itasca

namespace Itasca.Wasm

/-- A coherent bounded view is an exact interval in its parent region. -/
theorem BytesAt.of_slice_view {data view : Slice U8} {first last : Usize}
    (horder : first.val ≤ last.val) (hbound : last.val ≤ data.length)
    (hview : view.val = data.val.slice first.val last.val) :
    BytesAt data first view.val last := by
  refine ⟨?_, ?_, hbound⟩
  · rw [hview, List.slice]
    have he : first.val + (last.val - first.val) = last.val := by omega
    simpa only [List.drop_drop, he] using
      (List.take_append_drop (last.val - first.val) (data.val.drop first.val)).symm
  · rw [hview, List.slice_length]
    simp only [Slice.length] at hbound
    omega

/-- Transport an independently encoded interval from a view into its parent
region. Offset equalities avoid imposing an executable arithmetic operation. -/
theorem BytesAt.transport {data view : Slice U8} {first last pos next pos' next' : Usize}
    {bytes : List U8} (hview : BytesAt data first view.val last)
    (hbytes : BytesAt view pos bytes next)
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val) :
    BytesAt data pos' bytes next' := by
  have hn : next.val ≤ view.val.length := hbytes.bound
  have hp : pos.val ≤ view.val.length := by have := hbytes.length; omega
  have shift (i : Nat) (hi : i ≤ view.val.length) :
      data.val.drop (first.val + i) = view.val.drop i ++ data.val.drop last.val := by
    rw [← List.drop_drop, hview.suffix, List.drop_append_of_le_length hi]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpos, hnext, shift pos.val hp, shift next.val hn, hbytes.suffix, List.append_assoc]
  · have := hbytes.length
    omega
  · have := hview.length
    have := hview.bound
    omega

end Itasca.Wasm

namespace Itasca.Leb128

/-- Length-prefix decoding transports across coherent bounded views, retaining
nonminimal encodings and exact consumed bytes. -/
theorem Decoded.of_slice_view {data view : Slice U8} {first last pos next pos' next' : Usize}
    {value : U32} (horder : first.val ≤ last.val) (hbound : last.val ≤ data.length)
    (hview : view.val = data.val.slice first.val last.val)
    (hd : Decoded view pos value next)
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val) :
    Decoded data pos' value next' := by
  obtain ⟨bytes, hs, hn, hb, he⟩ := hd
  have hspan := (Wasm.BytesAt.of_slice_view horder hbound hview).transport
    (⟨hs, hn, hb⟩ : Wasm.BytesAt view pos bytes next) hpos hnext
  exact ⟨bytes, hspan.suffix, hspan.length, hspan.bound, he⟩

end Itasca.Leb128

namespace Itasca.Wasm

/-- Restrict an encoded interval to a coherent view that contains its end.
Only the bytes of that view need to be available to the reader. -/
theorem BytesAt.restrict {data view : Slice U8} {first last pos next pos' next' : Usize}
    {bytes : List U8} (hview : BytesAt data first view.val last)
    (hbytes : BytesAt data pos' bytes next')
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val)
    (hwithin : next'.val ≤ last.val) :
    BytesAt view pos bytes next := by
  have hn : next.val ≤ view.val.length := by have := hview.length; omega
  have hp : pos.val ≤ view.val.length := by have := hbytes.length; omega
  have shift (i : Nat) (hi : i ≤ view.val.length) :
      data.val.drop (first.val + i) = view.val.drop i ++ data.val.drop last.val := by
    rw [← List.drop_drop, hview.suffix, List.drop_append_of_le_length hi]
  refine ⟨?_, ?_, hn⟩
  · have he := hbytes.suffix
    rw [hpos, hnext, shift pos.val hp, shift next.val hn, ← List.append_assoc] at he
    exact List.append_cancel_right he
  · have := hbytes.length
    omega

end Itasca.Wasm

namespace Itasca.Leb128

/-- A complete LEB prefix inside a bounded view decodes using just that view;
this is the reverse transport needed for streaming completeness. -/
theorem Decoded.to_slice_view {data view : Slice U8} {first last pos next pos' next' : Usize}
    {value : U32} (horder : first.val ≤ last.val) (hbound : last.val ≤ data.length)
    (hview : view.val = data.val.slice first.val last.val)
    (hd : Decoded data pos' value next')
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val)
    (hwithin : next'.val ≤ last.val) :
    Decoded view pos value next := by
  obtain ⟨bytes, hs, hn, hb, he⟩ := hd
  have hspan := (Wasm.BytesAt.of_slice_view horder hbound hview).restrict
    (⟨hs, hn, hb⟩ : Wasm.BytesAt data pos' bytes next') hpos hnext hwithin
  exact ⟨bytes, hspan.suffix, hspan.length, hspan.bound, he⟩

end Itasca.Leb128
