import Itasca.Support.Result
import Itasca.Module.Readers.Basic
import Itasca.Contracts

/-!
# Streaming sources

Lemmas for the helpers that read from a `stream.Source`. The source premises
`StreamSource.Coherent`, `StreamSource.Available` and `StreamSource.CallbacksTotal` are defined in
`Itasca/Contracts`, and `stream.SliceSource` satisfies all three. The file also covers `limits.add_offset`, `stream.read_len` and `stream.read_exact`, and
the transport of encoded intervals between a bounded view and its parent region.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamSource

/-- Postcondition of `stream.read_len`: a returned length is a `U32` LEB128 value decoded from
`data` at `start`, converted to `Usize`. Errors are unconstrained. -/
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

/-- Any LEB128 decoding of a `U32` at `start` is returned by `stream.read_len`. -/
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

/-- Over a coherent source, a successful exact read returns the requested slice of the code
region. -/
theorem stream.read_exact.sound {S : Type} (source : stream.Source S) (state : S)
    (environment code tail : List U8) (hc : StreamSource.Coherent source state environment code tail)
    (first last : Usize) (bytes : Slice U8) (horder : first.val ≤ last.val)
    (hbound : last.val ≤ code.length)
    (h : stream.read_exact source state first last = .ok (.Ok bytes)) :
    bytes.val = code.slice first.val last.val ∧ bytes.length = last.val - first.val := by
  obtain ⟨hr, hn⟩ := stream.read_exact.accepted source state first last bytes horder h
  exact ⟨hc.code_eq first last bytes horder hbound hr, hn⟩

/-- A successful code read of the right length is returned by `stream.read_exact`. -/
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

/-- `stream.SliceSource` is coherent with its own environment, code and tail slices. -/
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

/-- `stream.SliceSource` makes every in-range read available. -/
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

/-- Every `stream.SliceSource` callback returns. -/
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

namespace Itasca.Wasm1

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

/-- An encoded interval in a view is an encoded interval in the parent region at offsets shifted
by the view start. The offsets are given as equalities rather than executable additions. -/
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

end Itasca.Wasm1

namespace Itasca.Leb128

/-- A LEB128 decoding inside a bounded view is a decoding of the parent region at shifted
offsets. Nonminimal encodings and the consumed bytes are preserved. -/
theorem Decoded.of_slice_view {data view : Slice U8} {first last pos next pos' next' : Usize}
    {value : U32} (horder : first.val ≤ last.val) (hbound : last.val ≤ data.length)
    (hview : view.val = data.val.slice first.val last.val)
    (hd : Decoded view pos value next)
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val) :
    Decoded data pos' value next' := by
  obtain ⟨bytes, hs, hn, hb, he⟩ := hd
  have hspan := (Wasm1.BytesAt.of_slice_view horder hbound hview).transport
    (⟨hs, hn, hb⟩ : Wasm1.BytesAt view pos bytes next) hpos hnext
  exact ⟨bytes, hspan.suffix, hspan.length, hspan.bound, he⟩

end Itasca.Leb128

namespace Itasca.Wasm1

/-- An encoded interval of the parent region that ends inside a view is an encoded interval of
that view at offsets shifted by the view start. -/
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

end Itasca.Wasm1

namespace Itasca.Leb128

/-- A LEB128 decoding of the parent region that ends inside a bounded view is a decoding of that
view alone. Completeness uses this direction. -/
theorem Decoded.to_slice_view {data view : Slice U8} {first last pos next pos' next' : Usize}
    {value : U32} (horder : first.val ≤ last.val) (hbound : last.val ≤ data.length)
    (hview : view.val = data.val.slice first.val last.val)
    (hd : Decoded data pos' value next')
    (hpos : pos'.val = first.val + pos.val)
    (hnext : next'.val = first.val + next.val)
    (hwithin : next'.val ≤ last.val) :
    Decoded view pos value next := by
  obtain ⟨bytes, hs, hn, hb, he⟩ := hd
  have hspan := (Wasm1.BytesAt.of_slice_view horder hbound hview).restrict
    (⟨hs, hn, hb⟩ : Wasm1.BytesAt data pos' bytes next') hpos hnext hwithin
  exact ⟨bytes, hspan.suffix, hspan.length, hspan.bound, he⟩

end Itasca.Leb128
