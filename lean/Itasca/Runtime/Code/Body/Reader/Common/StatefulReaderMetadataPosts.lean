import Itasca.Runtime.Code.Body.Reader.Common.StatefulReaderPost
import Itasca.Runtime.Code.Body.Reader.Common.ReaderStatefulMetadata
import Itasca.Runtime.Code.Body.Reader.Common.ReaderStatefulBulk
import Itasca.Runtime.Code.Body.Reader.Memory.ReaderMemoryMetadata
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem reader_table_get_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 37#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_get st.core data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableGet value.val) := by
  apply (reader_table_get_wasm2 p hbyte hsize value out accepted).stateful_post (.tableGet value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_table_set_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 38#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_set st.core data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableSet value.val) := by
  apply (reader_table_set_wasm2 p hbyte hsize value out accepted).stateful_post (.tableSet value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_ref_null_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 208#u8)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : types.ElemType) (out : code.OpIterState)
    (accepted : code.read_ref_null st.core data = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.refNull (Translate.referenceType value)) := by
  apply (reader_ref_null_wasm2 p hbyte hsize value out accepted).stateful_post (.refNull (Translate.referenceType value)) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_table_grow_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 15#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_grow {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableGrow value.val) := by
  apply (reader_table_grow_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableGrow value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_table_size_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 16#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_size {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableSize value.val) := by
  apply (reader_table_size_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableSize value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_table_fill_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 17#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_table_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableFill value.val) := by
  apply (reader_table_fill_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableFill value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_data_drop_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 9#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.take_data_index {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.dataDrop value.val) := by
  apply (reader_data_drop_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.dataDrop value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_elem_drop_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 13#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × types.ValueType) (out : code.OpIterState)
    (accepted : code.take_element {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.elemDrop value.1.val) := by
  apply (reader_elem_drop_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.elemDrop value.1.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_memory_fill_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 11#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_fill {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out .memoryFill := by
  apply (reader_memory_fill_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post .memoryFill ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_memory_copy_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 10#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : Unit) (out : code.OpIterState)
    (accepted : code.read_memory_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out .memoryCopy := by
  apply (reader_memory_copy_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post .memoryCopy ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_memory_init_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 8#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32) (out : code.OpIterState)
    (accepted : code.read_memory_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.memoryInit value.val) := by
  apply (reader_memory_init_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.memoryInit value.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_table_init_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 12#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_init {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableInit value.2.val value.1.val) := by
  apply (reader_table_init_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableInit value.2.val value.1.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_table_copy_post_wasm2 {data env locals index st} (p : Pending data env .Wasm2 locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 14#u32 next)
    (hsize : st.core.vals.val.length < Usize.max)
    (value : U32 × U32) (out : code.OpIterState)
    (accepted : code.read_table_copy {st.core with pos := next} data env = .ok (.Ok value,out)) :
    StatefulReaderPost p out (.tableCopy value.1.val value.2.val) := by
  apply (reader_table_copy_wasm2 p hbyte next hprefix hsize value out accepted).stateful_post (.tableCopy value.1.val value.2.val) ?_ hsize
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_memory_size_post_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 63#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_size st.core data env = .ok (.Ok (),out)) :
    StatefulReaderPost p out .memorySize := by
  apply (reader_memory_size_wasm2 p byte size out accepted).stateful_post .memorySize ?_ size
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_memory_grow_post_wasm2 {data env locals index st}
    (p : Pending data env .Wasm2 locals index st)
    (byte : data.val[p.start.val]'p.inbounds = 64#u8)
    (size : st.core.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_grow st.core data env = .ok (.Ok (),out)) :
    StatefulReaderPost p out .memoryGrow := by
  apply (reader_memory_grow_wasm2 p byte size out accepted).stateful_post .memoryGrow ?_ size
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

end Itasca.Runtime.Code
