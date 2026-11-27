import WebAssembly

namespace WebAssembly.Binary

mutual
  /-- Data indices in instruction syntax trigger the binary data-count requirement. -/
  def instructionUsesData : instr → Bool
    | .MEMORY_INIT _ | .DATA_DROP _ => true
    | .BLOCK _ body | .LOOP _ body => instructionsUseData body
    | .IFELSE _ yes no => instructionsUseData yes || instructionsUseData no
    | _ => false

  /-- Whether any instruction in the list uses a data index. -/
  def instructionsUseData : List instr → Bool
    | [] => false
    | op :: ops => instructionUsesData op || instructionsUseData ops
end

end WebAssembly.Binary
