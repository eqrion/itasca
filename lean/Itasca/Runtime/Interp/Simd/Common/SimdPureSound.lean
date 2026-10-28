import Itasca.Runtime.Interp.Simd.Common.SimdPureRelation
import Itasca.Runtime.Interp.Simd.Common.SimdPureCompare
import Itasca.Runtime.Interp.Simd.Float.SimdPureFloat
import Itasca.Runtime.Interp.Simd.Integer.SimdPureInteger
import Itasca.Runtime.Interp.Simd.Common.SimdPureConversions
import Itasca.Runtime.Interp.Simd.Common.SimdPureUnary
import Mathlib.Tactic.IntervalCases
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Every source-table pure SIMD operation refines its generated source rule. -/
theorem pure_entries {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : Platform.FloatOpsCorrect floats) (opcode : U32) (bounded : opcode.val < 256) :
    PureEntrySound floats opcode := by
  rcases opcode with ⟨⟨n,hn⟩⟩
  change n < 256 at bounded
  interval_cases n
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_14 floats
  · exact pure_entry_15 floats
  · exact pure_entry_16 floats
  · exact pure_entry_17 floats
  · exact pure_entry_18 floats
  · exact pure_entry_19 floats
  · exact pure_entry_20 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_35 floats
  · exact pure_entry_36 floats
  · exact pure_entry_37 floats
  · exact pure_entry_38 floats
  · exact pure_entry_39 floats
  · exact pure_entry_40 floats
  · exact pure_entry_41 floats
  · exact pure_entry_42 floats
  · exact pure_entry_43 floats
  · exact pure_entry_44 floats
  · exact pure_entry_45 floats
  · exact pure_entry_46 floats
  · exact pure_entry_47 floats
  · exact pure_entry_48 floats
  · exact pure_entry_49 floats
  · exact pure_entry_50 floats
  · exact pure_entry_51 floats
  · exact pure_entry_52 floats
  · exact pure_entry_53 floats
  · exact pure_entry_54 floats
  · exact pure_entry_55 floats
  · exact pure_entry_56 floats
  · exact pure_entry_57 floats
  · exact pure_entry_58 floats
  · exact pure_entry_59 floats
  · exact pure_entry_60 floats
  · exact pure_entry_61 floats
  · exact pure_entry_62 floats
  · exact pure_entry_63 floats
  · exact pure_entry_64 floats
  · exact pure_entry_65 floats
  · exact pure_entry_66 floats
  · exact pure_entry_67 floats
  · exact pure_entry_68 floats
  · exact pure_entry_69 floats
  · exact pure_entry_70 floats
  · exact pure_entry_71 floats
  · exact pure_entry_72 floats
  · exact pure_entry_73 floats
  · exact pure_entry_74 floats
  · exact pure_entry_75 floats
  · exact pure_entry_76 floats
  · exact pure_entry_77 floats
  · exact pure_entry_78 floats
  · exact pure_entry_79 floats
  · exact pure_entry_80 floats
  · exact pure_entry_81 floats
  · exact pure_entry_82 floats
  · exact pure_entry_83 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_94 floats laws
  · exact pure_entry_95 floats laws
  · exact pure_entry_96 floats
  · exact pure_entry_97 floats
  · exact pure_entry_98 floats
  · exact pure_entry_99 floats
  · exact pure_entry_100 floats
  · exact pure_entry_101 floats
  · exact pure_entry_102 floats
  · exact pure_entry_103 floats laws
  · exact pure_entry_104 floats laws
  · exact pure_entry_105 floats laws
  · exact pure_entry_106 floats laws
  · exact pure_entry_107 floats
  · exact pure_entry_108 floats
  · exact pure_entry_109 floats
  · exact pure_entry_110 floats
  · exact pure_entry_111 floats
  · exact pure_entry_112 floats
  · exact pure_entry_113 floats
  · exact pure_entry_114 floats
  · exact pure_entry_115 floats
  · exact pure_entry_116 floats laws
  · exact pure_entry_117 floats laws
  · exact pure_entry_118 floats
  · exact pure_entry_119 floats
  · exact pure_entry_120 floats
  · exact pure_entry_121 floats
  · exact pure_entry_122 floats laws
  · exact pure_entry_123 floats
  · exact pure_entry_124 floats
  · exact pure_entry_125 floats
  · exact pure_entry_126 floats
  · exact pure_entry_127 floats
  · exact pure_entry_128 floats
  · exact pure_entry_129 floats
  · exact pure_entry_130 floats
  · exact pure_entry_131 floats
  · exact pure_entry_132 floats
  · exact pure_entry_133 floats
  · exact pure_entry_134 floats
  · exact pure_entry_135 floats
  · exact pure_entry_136 floats
  · exact pure_entry_137 floats
  · exact pure_entry_138 floats
  · exact pure_entry_139 floats
  · exact pure_entry_140 floats
  · exact pure_entry_141 floats
  · exact pure_entry_142 floats
  · exact pure_entry_143 floats
  · exact pure_entry_144 floats
  · exact pure_entry_145 floats
  · exact pure_entry_146 floats
  · exact pure_entry_147 floats
  · exact pure_entry_148 floats laws
  · exact pure_entry_149 floats
  · exact pure_entry_150 floats
  · exact pure_entry_151 floats
  · exact pure_entry_152 floats
  · exact pure_entry_153 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_155 floats
  · exact pure_entry_156 floats
  · exact pure_entry_157 floats
  · exact pure_entry_158 floats
  · exact pure_entry_159 floats
  · exact pure_entry_160 floats
  · exact pure_entry_161 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_163 floats
  · exact pure_entry_164 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_167 floats
  · exact pure_entry_168 floats
  · exact pure_entry_169 floats
  · exact pure_entry_170 floats
  · exact pure_entry_171 floats
  · exact pure_entry_172 floats
  · exact pure_entry_173 floats
  · exact pure_entry_174 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_177 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_181 floats
  · exact pure_entry_182 floats
  · exact pure_entry_183 floats
  · exact pure_entry_184 floats
  · exact pure_entry_185 floats
  · exact pure_entry_186 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_188 floats
  · exact pure_entry_189 floats
  · exact pure_entry_190 floats
  · exact pure_entry_191 floats
  · exact pure_entry_192 floats
  · exact pure_entry_193 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_195 floats
  · exact pure_entry_196 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_199 floats
  · exact pure_entry_200 floats
  · exact pure_entry_201 floats
  · exact pure_entry_202 floats
  · exact pure_entry_203 floats
  · exact pure_entry_204 floats
  · exact pure_entry_205 floats
  · exact pure_entry_206 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_209 floats
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_213 floats
  · exact pure_entry_214 floats
  · exact pure_entry_215 floats
  · exact pure_entry_216 floats
  · exact pure_entry_217 floats
  · exact pure_entry_218 floats
  · exact pure_entry_219 floats
  · exact pure_entry_220 floats
  · exact pure_entry_221 floats
  · exact pure_entry_222 floats
  · exact pure_entry_223 floats
  · exact pure_entry_224 floats laws
  · exact pure_entry_225 floats laws
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_227 floats laws
  · exact pure_entry_228 floats laws
  · exact pure_entry_229 floats laws
  · exact pure_entry_230 floats laws
  · exact pure_entry_231 floats laws
  · exact pure_entry_232 floats laws
  · exact pure_entry_233 floats laws
  · exact pure_entry_234 floats laws
  · exact pure_entry_235 floats laws
  · exact pure_entry_236 floats laws
  · exact pure_entry_237 floats laws
  · intro op meaning
    change none = some op at meaning
    contradiction
  · exact pure_entry_239 floats laws
  · exact pure_entry_240 floats laws
  · exact pure_entry_241 floats laws
  · exact pure_entry_242 floats laws
  · exact pure_entry_243 floats laws
  · exact pure_entry_244 floats laws
  · exact pure_entry_245 floats laws
  · exact pure_entry_246 floats laws
  · exact pure_entry_247 floats laws
  · exact pure_entry_248 floats
  · exact pure_entry_249 floats
  · exact pure_entry_250 floats laws
  · exact pure_entry_251 floats laws
  · exact pure_entry_252 floats
  · exact pure_entry_253 floats
  · exact pure_entry_254 floats laws
  · exact pure_entry_255 floats laws

theorem pure_dispatch_source {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : Platform.FloatOpsCorrect floats) (opcode : U32) (op : Itasca.Wasm2.Simd.Operation)
    (meaning : Itasca.Wasm2.Simd.pureMeaning opcode.val = some op)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats opcode offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧ PureSourceEffect op x.bv y.bv z.bv value.bv ⦄ := by
  exact pure_entries floats laws opcode (Itasca.Wasm2.Simd.pure_bound meaning)
    op meaning offset laneIndex bits x y z memory
end Itasca.Runtime.Interp.Simd
