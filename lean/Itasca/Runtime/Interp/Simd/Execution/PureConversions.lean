import Itasca.Runtime.Interp.Simd.Relations.PureRelation
import Itasca.Runtime.Interp.Simd.Integer.WidenSound
import Itasca.Runtime.Interp.Simd.Integer.Pairwise
import Itasca.Runtime.Interp.Simd.Integer.Narrow
import Itasca.Runtime.Interp.Simd.Integer.Dot
import Itasca.Runtime.Interp.Simd.Float.TruncSat
import Itasca.Runtime.Interp.Simd.Integer.ConvertInteger
import Itasca.Runtime.Interp.Simd.Float.Resize

/-!
Source correspondence of pure conversion opcode entries.

Main declarations: `pure_entry_94` and `pure_entry_255`. A direct consumer is `Interp.Simd.Execution.PureSound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem pure_entry_94 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 94#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure94 = some op at meaning
  cases meaning
  with_unfolding_all exact float_resize_simd_sound floats laws .demote offset laneIndex bits x y z memory

theorem pure_entry_95 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 95#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure95 = some op at meaning
  cases meaning
  with_unfolding_all exact float_resize_simd_sound floats laws .promote offset laneIndex bits x y z memory

theorem pure_entry_101 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 101#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure101 = some op at meaning
  cases meaning
  with_unfolding_all exact narrow_simd_sound floats .i8 true offset laneIndex bits x y z memory

theorem pure_entry_102 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 102#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure102 = some op at meaning
  cases meaning
  with_unfolding_all exact narrow_simd_sound floats .i8 false offset laneIndex bits x y z memory

theorem pure_entry_124 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 124#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure124 = some op at meaning
  cases meaning
  with_unfolding_all exact pairwise_simd_sound floats .i8 true offset laneIndex bits x y z memory

theorem pure_entry_125 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 125#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure125 = some op at meaning
  cases meaning
  with_unfolding_all exact pairwise_simd_sound floats .i8 false offset laneIndex bits x y z memory

theorem pure_entry_126 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 126#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure126 = some op at meaning
  cases meaning
  with_unfolding_all exact pairwise_simd_sound floats .i16 true offset laneIndex bits x y z memory

theorem pure_entry_127 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 127#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure127 = some op at meaning
  cases meaning
  with_unfolding_all exact pairwise_simd_sound floats .i16 false offset laneIndex bits x y z memory

theorem pure_entry_133 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 133#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure133 = some op at meaning
  cases meaning
  with_unfolding_all exact narrow_simd_sound floats .i16 true offset laneIndex bits x y z memory

theorem pure_entry_134 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 134#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure134 = some op at meaning
  cases meaning
  with_unfolding_all exact narrow_simd_sound floats .i16 false offset laneIndex bits x y z memory

theorem pure_entry_135 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 135#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure135 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 false false true offset laneIndex bits x y z memory

theorem pure_entry_136 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 136#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure136 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 false true true offset laneIndex bits x y z memory

theorem pure_entry_137 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 137#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure137 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 false false false offset laneIndex bits x y z memory

theorem pure_entry_138 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 138#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure138 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 false true false offset laneIndex bits x y z memory

theorem pure_entry_156 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 156#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure156 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 true false true offset laneIndex bits x y z memory

theorem pure_entry_157 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 157#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure157 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 true true true offset laneIndex bits x y z memory

theorem pure_entry_158 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 158#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure158 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 true false false offset laneIndex bits x y z memory

theorem pure_entry_159 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 159#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure159 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i8 true true false offset laneIndex bits x y z memory

theorem pure_entry_167 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 167#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure167 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 false false true offset laneIndex bits x y z memory

theorem pure_entry_168 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 168#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure168 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 false true true offset laneIndex bits x y z memory

theorem pure_entry_169 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 169#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure169 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 false false false offset laneIndex bits x y z memory

theorem pure_entry_170 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 170#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure170 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 false true false offset laneIndex bits x y z memory

theorem pure_entry_186 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 186#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure186 = some op at meaning
  cases meaning
  with_unfolding_all exact dot_simd_sound floats  offset laneIndex bits x y z memory

theorem pure_entry_188 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 188#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure188 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 true false true offset laneIndex bits x y z memory

theorem pure_entry_189 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 189#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure189 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 true true true offset laneIndex bits x y z memory

theorem pure_entry_190 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 190#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure190 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 true false false offset laneIndex bits x y z memory

theorem pure_entry_191 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 191#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure191 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i16 true true false offset laneIndex bits x y z memory

theorem pure_entry_199 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 199#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure199 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 false false true offset laneIndex bits x y z memory

theorem pure_entry_200 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 200#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure200 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 false true true offset laneIndex bits x y z memory

theorem pure_entry_201 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 201#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure201 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 false false false offset laneIndex bits x y z memory

theorem pure_entry_202 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 202#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure202 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 false true false offset laneIndex bits x y z memory

theorem pure_entry_220 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 220#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure220 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 true false true offset laneIndex bits x y z memory

theorem pure_entry_221 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 221#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure221 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 true true true offset laneIndex bits x y z memory

theorem pure_entry_222 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 222#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure222 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 true false false offset laneIndex bits x y z memory

theorem pure_entry_223 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 223#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure223 = some op at meaning
  cases meaning
  with_unfolding_all exact widen_simd_sound floats .i32 true true false offset laneIndex bits x y z memory

theorem pure_entry_248 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 248#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure248 = some op at meaning
  cases meaning
  with_unfolding_all exact trunc_sat_simd_sound floats .F32 true offset laneIndex bits x y z memory

theorem pure_entry_249 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 249#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure249 = some op at meaning
  cases meaning
  with_unfolding_all exact trunc_sat_simd_sound floats .F32 false offset laneIndex bits x y z memory

theorem pure_entry_250 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 250#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure250 = some op at meaning
  cases meaning
  with_unfolding_all exact convert_integer_simd_sound floats laws .F32 true offset laneIndex bits x y z memory

theorem pure_entry_251 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 251#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure251 = some op at meaning
  cases meaning
  with_unfolding_all exact convert_integer_simd_sound floats laws .F32 false offset laneIndex bits x y z memory

theorem pure_entry_252 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 252#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure252 = some op at meaning
  cases meaning
  with_unfolding_all exact trunc_sat_simd_sound floats .F64 true offset laneIndex bits x y z memory

theorem pure_entry_253 {F : Type} (floats : runtime.platform.FloatOps F) :
    PureEntrySound floats 253#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure253 = some op at meaning
  cases meaning
  with_unfolding_all exact trunc_sat_simd_sound floats .F64 false offset laneIndex bits x y z memory

theorem pure_entry_254 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 254#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure254 = some op at meaning
  cases meaning
  with_unfolding_all exact convert_integer_simd_sound floats laws .F64 true offset laneIndex bits x y z memory

theorem pure_entry_255 {F : Type} (floats : runtime.platform.FloatOps F) (laws : Platform.FloatOpsCorrect floats) :
    PureEntrySound floats 255#u32 := by
  intro op meaning offset laneIndex bits x y z memory
  change some Itasca.Wasm2.Simd.pure255 = some op at meaning
  cases meaning
  with_unfolding_all exact convert_integer_simd_sound floats laws .F64 false offset laneIndex bits x y z memory

end Itasca.Runtime.Interp.Simd
