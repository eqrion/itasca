import Exec.Interp.Simd.Common.SimdPureRelation
import Exec.Interp.Simd.Float.SimdFloatUnarySound
import Exec.Interp.Simd.Float.SimdFloatBinarySound
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_103 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 103#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure103 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .CEIL offset laneIndex bits x y z memory

theorem pure_entry_104 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 104#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure104 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .FLOOR offset laneIndex bits x y z memory

theorem pure_entry_105 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 105#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure105 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .TRUNC offset laneIndex bits x y z memory

theorem pure_entry_106 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 106#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure106 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .NEAREST offset laneIndex bits x y z memory

theorem pure_entry_116 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 116#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure116 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .CEIL offset laneIndex bits x y z memory

theorem pure_entry_117 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 117#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure117 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .FLOOR offset laneIndex bits x y z memory

theorem pure_entry_122 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 122#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure122 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .TRUNC offset laneIndex bits x y z memory

theorem pure_entry_148 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 148#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure148 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .NEAREST offset laneIndex bits x y z memory

theorem pure_entry_224 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 224#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure224 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .ABS offset laneIndex bits x y z memory

theorem pure_entry_225 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 225#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure225 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .NEG offset laneIndex bits x y z memory

theorem pure_entry_227 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 227#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure227 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F32 .SQRT offset laneIndex bits x y z memory

theorem pure_entry_228 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 228#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure228 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .ADD offset laneIndex bits x y z memory

theorem pure_entry_229 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 229#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure229 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .SUB offset laneIndex bits x y z memory

theorem pure_entry_230 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 230#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure230 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .MUL offset laneIndex bits x y z memory

theorem pure_entry_231 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 231#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure231 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .DIV offset laneIndex bits x y z memory

theorem pure_entry_232 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 232#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure232 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .MIN offset laneIndex bits x y z memory

theorem pure_entry_233 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 233#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure233 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .MAX offset laneIndex bits x y z memory

theorem pure_entry_234 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 234#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure234 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .PMIN offset laneIndex bits x y z memory

theorem pure_entry_235 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 235#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure235 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F32 .PMAX offset laneIndex bits x y z memory

theorem pure_entry_236 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 236#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure236 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .ABS offset laneIndex bits x y z memory

theorem pure_entry_237 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 237#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure237 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .NEG offset laneIndex bits x y z memory

theorem pure_entry_239 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 239#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure239 = some op at meaning
  cases meaning
  with_unfolding_all exact float_unary_simd_sound floats laws .F64 .SQRT offset laneIndex bits x y z memory

theorem pure_entry_240 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 240#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure240 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .ADD offset laneIndex bits x y z memory

theorem pure_entry_241 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 241#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure241 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .SUB offset laneIndex bits x y z memory

theorem pure_entry_242 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 242#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure242 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .MUL offset laneIndex bits x y z memory

theorem pure_entry_243 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 243#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure243 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .DIV offset laneIndex bits x y z memory

theorem pure_entry_244 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 244#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure244 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .MIN offset laneIndex bits x y z memory

theorem pure_entry_245 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 245#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure245 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .MAX offset laneIndex bits x y z memory

theorem pure_entry_246 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 246#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure246 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .PMIN offset laneIndex bits x y z memory

theorem pure_entry_247 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 247#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure247 = some op at meaning
  cases meaning
  with_unfolding_all exact float_binary_simd_sound floats laws .F64 .PMAX offset laneIndex bits x y z memory

end Exec.Interp.Simd
