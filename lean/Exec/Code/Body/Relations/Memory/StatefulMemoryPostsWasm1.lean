import Exec.Code.Body.Reader.Common.StatefulReaderPostWasm1
import Exec.Code.Body.Reader.Memory.ReaderMemoryMetadataWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm1
theorem reader_memory_size_post_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st)
    (byte : data.val[p.start.val]'p.inbounds = 63#u8)
    (size : st.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_size st data env = .ok (.Ok (),out)) :
    StatefulReaderPostWasm1 p out .memorySize := by
  apply (reader_memory_size_wasm1 p byte size out accepted).stateful_post .memorySize ?_ size
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

theorem reader_memory_grow_post_wasm1 {data env ctx bt st}
    (p : Pending data env ctx bt st)
    (byte : data.val[p.start.val]'p.inbounds = 64#u8)
    (size : st.vals.val.length < Usize.max) (out : code.OpIterState)
    (accepted : code.read_memory_grow st data env = .ok (.Ok (),out)) :
    StatefulReaderPostWasm1 p out .memoryGrow := by
  apply (reader_memory_grow_wasm1 p byte size out accepted).stateful_post .memoryGrow ?_ size
  intro a equality
  try dsimp only [id] at equality
  simp only [Abs.Stateful.Instruction.source,equality]

end Exec.Code
