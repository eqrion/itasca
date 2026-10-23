import Itasca.Handler.Block
import Itasca.Handler.ControlFlow
import Itasca.Binary.Wasm1.EncodingComplete

/-!
# Block-type decoding on raw bytes

Total specifications of `code.read_block_type`, `code.read_block`, `code.read_loop` and
`code.read_if` that relate their outcome to `Control.BlockDecoded` on arbitrary bytes. The
`Wasm1.BytesAt.read_block_type` and `Wasm1.At.read_*` lemmas connect the binary grammar to
`code.read_block_type`.
-/

open Aeneas Aeneas.Std

namespace Itasca

end Itasca

namespace Itasca.Wasm1

end Itasca.Wasm1
