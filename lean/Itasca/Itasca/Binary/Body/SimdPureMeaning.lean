import Itasca.Binary.Definitions
import Itasca.Results.Definitions.Binary
import ItascaRust.Funs
import Mathlib.Tactic.IntervalCases
import Aeneas
import WebAssembly

open WebAssembly

/-!
Proofs for Binary / Body.

This module collects SimdOperations, SimdPureMeaning.
Each section documents its contracts and consumers.
-/

/-! ## SimdOperations -/

section

/-!
# Implementation classifications for pure SIMD

Implementation proofs classify pure SIMD instructions by stack shape. Public
grammar and compiler relations use SpecTec syntax and judgments directly. This
finite vocabulary supports case analysis and is connected to those relations by
checked correspondence and principal-signature theorems.
-/

namespace Itasca.Body.Simd

/-- The stack signature shapes of the SIMD instructions without immediates. -/
inductive Signature where
  | unary | binary | ternary | test | shift
  | splatI32 | splatI64 | splatF32 | splatF64

/-- The operand types of a signature. -/
def Signature.inputs : Signature → List valtype
  | .unary | .test => [.V128]
  | .binary => [.V128, .V128]
  | .ternary => [.V128, .V128, .V128]
  | .shift => [.V128, .I32]
  | .splatI32 => [.I32]
  | .splatI64 => [.I64]
  | .splatF32 => [.F32]
  | .splatF64 => [.F64]

/-- The result types of a signature. -/
def Signature.outputs : Signature → List valtype
  | .test => [.I32]
  | _ => [.V128]

inductive Operation where
  | pure14
  | pure15
  | pure16
  | pure17
  | pure18
  | pure19
  | pure20
  | pure35
  | pure36
  | pure37
  | pure38
  | pure39
  | pure40
  | pure41
  | pure42
  | pure43
  | pure44
  | pure45
  | pure46
  | pure47
  | pure48
  | pure49
  | pure50
  | pure51
  | pure52
  | pure53
  | pure54
  | pure55
  | pure56
  | pure57
  | pure58
  | pure59
  | pure60
  | pure61
  | pure62
  | pure63
  | pure64
  | pure65
  | pure66
  | pure67
  | pure68
  | pure69
  | pure70
  | pure71
  | pure72
  | pure73
  | pure74
  | pure75
  | pure76
  | pure77
  | pure78
  | pure79
  | pure80
  | pure81
  | pure82
  | pure83
  | pure94
  | pure95
  | pure96
  | pure97
  | pure98
  | pure99
  | pure100
  | pure101
  | pure102
  | pure103
  | pure104
  | pure105
  | pure106
  | pure107
  | pure108
  | pure109
  | pure110
  | pure111
  | pure112
  | pure113
  | pure114
  | pure115
  | pure116
  | pure117
  | pure118
  | pure119
  | pure120
  | pure121
  | pure122
  | pure123
  | pure124
  | pure125
  | pure126
  | pure127
  | pure128
  | pure129
  | pure130
  | pure131
  | pure132
  | pure133
  | pure134
  | pure135
  | pure136
  | pure137
  | pure138
  | pure139
  | pure140
  | pure141
  | pure142
  | pure143
  | pure144
  | pure145
  | pure146
  | pure147
  | pure148
  | pure149
  | pure150
  | pure151
  | pure152
  | pure153
  | pure155
  | pure156
  | pure157
  | pure158
  | pure159
  | pure160
  | pure161
  | pure163
  | pure164
  | pure167
  | pure168
  | pure169
  | pure170
  | pure171
  | pure172
  | pure173
  | pure174
  | pure177
  | pure181
  | pure182
  | pure183
  | pure184
  | pure185
  | pure186
  | pure188
  | pure189
  | pure190
  | pure191
  | pure192
  | pure193
  | pure195
  | pure196
  | pure199
  | pure200
  | pure201
  | pure202
  | pure203
  | pure204
  | pure205
  | pure206
  | pure209
  | pure213
  | pure214
  | pure215
  | pure216
  | pure217
  | pure218
  | pure219
  | pure220
  | pure221
  | pure222
  | pure223
  | pure224
  | pure225
  | pure227
  | pure228
  | pure229
  | pure230
  | pure231
  | pure232
  | pure233
  | pure234
  | pure235
  | pure236
  | pure237
  | pure239
  | pure240
  | pure241
  | pure242
  | pure243
  | pure244
  | pure245
  | pure246
  | pure247
  | pure248
  | pure249
  | pure250
  | pure251
  | pure252
  | pure253
  | pure254
  | pure255

/-- Binary subopcode of each compiler classification. -/
def Operation.opcode : Operation → Nat
  | .pure14 => 14
  | .pure15 => 15
  | .pure16 => 16
  | .pure17 => 17
  | .pure18 => 18
  | .pure19 => 19
  | .pure20 => 20
  | .pure35 => 35
  | .pure36 => 36
  | .pure37 => 37
  | .pure38 => 38
  | .pure39 => 39
  | .pure40 => 40
  | .pure41 => 41
  | .pure42 => 42
  | .pure43 => 43
  | .pure44 => 44
  | .pure45 => 45
  | .pure46 => 46
  | .pure47 => 47
  | .pure48 => 48
  | .pure49 => 49
  | .pure50 => 50
  | .pure51 => 51
  | .pure52 => 52
  | .pure53 => 53
  | .pure54 => 54
  | .pure55 => 55
  | .pure56 => 56
  | .pure57 => 57
  | .pure58 => 58
  | .pure59 => 59
  | .pure60 => 60
  | .pure61 => 61
  | .pure62 => 62
  | .pure63 => 63
  | .pure64 => 64
  | .pure65 => 65
  | .pure66 => 66
  | .pure67 => 67
  | .pure68 => 68
  | .pure69 => 69
  | .pure70 => 70
  | .pure71 => 71
  | .pure72 => 72
  | .pure73 => 73
  | .pure74 => 74
  | .pure75 => 75
  | .pure76 => 76
  | .pure77 => 77
  | .pure78 => 78
  | .pure79 => 79
  | .pure80 => 80
  | .pure81 => 81
  | .pure82 => 82
  | .pure83 => 83
  | .pure94 => 94
  | .pure95 => 95
  | .pure96 => 96
  | .pure97 => 97
  | .pure98 => 98
  | .pure99 => 99
  | .pure100 => 100
  | .pure101 => 101
  | .pure102 => 102
  | .pure103 => 103
  | .pure104 => 104
  | .pure105 => 105
  | .pure106 => 106
  | .pure107 => 107
  | .pure108 => 108
  | .pure109 => 109
  | .pure110 => 110
  | .pure111 => 111
  | .pure112 => 112
  | .pure113 => 113
  | .pure114 => 114
  | .pure115 => 115
  | .pure116 => 116
  | .pure117 => 117
  | .pure118 => 118
  | .pure119 => 119
  | .pure120 => 120
  | .pure121 => 121
  | .pure122 => 122
  | .pure123 => 123
  | .pure124 => 124
  | .pure125 => 125
  | .pure126 => 126
  | .pure127 => 127
  | .pure128 => 128
  | .pure129 => 129
  | .pure130 => 130
  | .pure131 => 131
  | .pure132 => 132
  | .pure133 => 133
  | .pure134 => 134
  | .pure135 => 135
  | .pure136 => 136
  | .pure137 => 137
  | .pure138 => 138
  | .pure139 => 139
  | .pure140 => 140
  | .pure141 => 141
  | .pure142 => 142
  | .pure143 => 143
  | .pure144 => 144
  | .pure145 => 145
  | .pure146 => 146
  | .pure147 => 147
  | .pure148 => 148
  | .pure149 => 149
  | .pure150 => 150
  | .pure151 => 151
  | .pure152 => 152
  | .pure153 => 153
  | .pure155 => 155
  | .pure156 => 156
  | .pure157 => 157
  | .pure158 => 158
  | .pure159 => 159
  | .pure160 => 160
  | .pure161 => 161
  | .pure163 => 163
  | .pure164 => 164
  | .pure167 => 167
  | .pure168 => 168
  | .pure169 => 169
  | .pure170 => 170
  | .pure171 => 171
  | .pure172 => 172
  | .pure173 => 173
  | .pure174 => 174
  | .pure177 => 177
  | .pure181 => 181
  | .pure182 => 182
  | .pure183 => 183
  | .pure184 => 184
  | .pure185 => 185
  | .pure186 => 186
  | .pure188 => 188
  | .pure189 => 189
  | .pure190 => 190
  | .pure191 => 191
  | .pure192 => 192
  | .pure193 => 193
  | .pure195 => 195
  | .pure196 => 196
  | .pure199 => 199
  | .pure200 => 200
  | .pure201 => 201
  | .pure202 => 202
  | .pure203 => 203
  | .pure204 => 204
  | .pure205 => 205
  | .pure206 => 206
  | .pure209 => 209
  | .pure213 => 213
  | .pure214 => 214
  | .pure215 => 215
  | .pure216 => 216
  | .pure217 => 217
  | .pure218 => 218
  | .pure219 => 219
  | .pure220 => 220
  | .pure221 => 221
  | .pure222 => 222
  | .pure223 => 223
  | .pure224 => 224
  | .pure225 => 225
  | .pure227 => 227
  | .pure228 => 228
  | .pure229 => 229
  | .pure230 => 230
  | .pure231 => 231
  | .pure232 => 232
  | .pure233 => 233
  | .pure234 => 234
  | .pure235 => 235
  | .pure236 => 236
  | .pure237 => 237
  | .pure239 => 239
  | .pure240 => 240
  | .pure241 => 241
  | .pure242 => 242
  | .pure243 => 243
  | .pure244 => 244
  | .pure245 => 245
  | .pure246 => 246
  | .pure247 => 247
  | .pure248 => 248
  | .pure249 => 249
  | .pure250 => 250
  | .pure251 => 251
  | .pure252 => 252
  | .pure253 => 253
  | .pure254 => 254
  | .pure255 => 255

/-- Reuse the binary table rather than maintain a second AST mapping.
All constructors have a mapped opcode; Binary proves the associated properties.
The default makes the projection total and is unreachable for these constructors. -/
def Operation.instruction (op : Operation) : instr :=
  (pureInstruction op.opcode).getD .UNREACHABLE

def Operation.signature : Operation → Signature
  | .pure14 => .binary
  | .pure15 => .splatI32
  | .pure16 => .splatI32
  | .pure17 => .splatI32
  | .pure18 => .splatI64
  | .pure19 => .splatF32
  | .pure20 => .splatF64
  | .pure35 => .binary
  | .pure36 => .binary
  | .pure37 => .binary
  | .pure38 => .binary
  | .pure39 => .binary
  | .pure40 => .binary
  | .pure41 => .binary
  | .pure42 => .binary
  | .pure43 => .binary
  | .pure44 => .binary
  | .pure45 => .binary
  | .pure46 => .binary
  | .pure47 => .binary
  | .pure48 => .binary
  | .pure49 => .binary
  | .pure50 => .binary
  | .pure51 => .binary
  | .pure52 => .binary
  | .pure53 => .binary
  | .pure54 => .binary
  | .pure55 => .binary
  | .pure56 => .binary
  | .pure57 => .binary
  | .pure58 => .binary
  | .pure59 => .binary
  | .pure60 => .binary
  | .pure61 => .binary
  | .pure62 => .binary
  | .pure63 => .binary
  | .pure64 => .binary
  | .pure65 => .binary
  | .pure66 => .binary
  | .pure67 => .binary
  | .pure68 => .binary
  | .pure69 => .binary
  | .pure70 => .binary
  | .pure71 => .binary
  | .pure72 => .binary
  | .pure73 => .binary
  | .pure74 => .binary
  | .pure75 => .binary
  | .pure76 => .binary
  | .pure77 => .unary
  | .pure78 => .binary
  | .pure79 => .binary
  | .pure80 => .binary
  | .pure81 => .binary
  | .pure82 => .ternary
  | .pure83 => .test
  | .pure94 => .unary
  | .pure95 => .unary
  | .pure96 => .unary
  | .pure97 => .unary
  | .pure98 => .unary
  | .pure99 => .test
  | .pure100 => .test
  | .pure101 => .binary
  | .pure102 => .binary
  | .pure103 => .unary
  | .pure104 => .unary
  | .pure105 => .unary
  | .pure106 => .unary
  | .pure107 => .shift
  | .pure108 => .shift
  | .pure109 => .shift
  | .pure110 => .binary
  | .pure111 => .binary
  | .pure112 => .binary
  | .pure113 => .binary
  | .pure114 => .binary
  | .pure115 => .binary
  | .pure116 => .unary
  | .pure117 => .unary
  | .pure118 => .binary
  | .pure119 => .binary
  | .pure120 => .binary
  | .pure121 => .binary
  | .pure122 => .unary
  | .pure123 => .binary
  | .pure124 => .unary
  | .pure125 => .unary
  | .pure126 => .unary
  | .pure127 => .unary
  | .pure128 => .unary
  | .pure129 => .unary
  | .pure130 => .binary
  | .pure131 => .test
  | .pure132 => .test
  | .pure133 => .binary
  | .pure134 => .binary
  | .pure135 => .unary
  | .pure136 => .unary
  | .pure137 => .unary
  | .pure138 => .unary
  | .pure139 => .shift
  | .pure140 => .shift
  | .pure141 => .shift
  | .pure142 => .binary
  | .pure143 => .binary
  | .pure144 => .binary
  | .pure145 => .binary
  | .pure146 => .binary
  | .pure147 => .binary
  | .pure148 => .unary
  | .pure149 => .binary
  | .pure150 => .binary
  | .pure151 => .binary
  | .pure152 => .binary
  | .pure153 => .binary
  | .pure155 => .binary
  | .pure156 => .binary
  | .pure157 => .binary
  | .pure158 => .binary
  | .pure159 => .binary
  | .pure160 => .unary
  | .pure161 => .unary
  | .pure163 => .test
  | .pure164 => .test
  | .pure167 => .unary
  | .pure168 => .unary
  | .pure169 => .unary
  | .pure170 => .unary
  | .pure171 => .shift
  | .pure172 => .shift
  | .pure173 => .shift
  | .pure174 => .binary
  | .pure177 => .binary
  | .pure181 => .binary
  | .pure182 => .binary
  | .pure183 => .binary
  | .pure184 => .binary
  | .pure185 => .binary
  | .pure186 => .binary
  | .pure188 => .binary
  | .pure189 => .binary
  | .pure190 => .binary
  | .pure191 => .binary
  | .pure192 => .unary
  | .pure193 => .unary
  | .pure195 => .test
  | .pure196 => .test
  | .pure199 => .unary
  | .pure200 => .unary
  | .pure201 => .unary
  | .pure202 => .unary
  | .pure203 => .shift
  | .pure204 => .shift
  | .pure205 => .shift
  | .pure206 => .binary
  | .pure209 => .binary
  | .pure213 => .binary
  | .pure214 => .binary
  | .pure215 => .binary
  | .pure216 => .binary
  | .pure217 => .binary
  | .pure218 => .binary
  | .pure219 => .binary
  | .pure220 => .binary
  | .pure221 => .binary
  | .pure222 => .binary
  | .pure223 => .binary
  | .pure224 => .unary
  | .pure225 => .unary
  | .pure227 => .unary
  | .pure228 => .binary
  | .pure229 => .binary
  | .pure230 => .binary
  | .pure231 => .binary
  | .pure232 => .binary
  | .pure233 => .binary
  | .pure234 => .binary
  | .pure235 => .binary
  | .pure236 => .unary
  | .pure237 => .unary
  | .pure239 => .unary
  | .pure240 => .binary
  | .pure241 => .binary
  | .pure242 => .binary
  | .pure243 => .binary
  | .pure244 => .binary
  | .pure245 => .binary
  | .pure246 => .binary
  | .pure247 => .binary
  | .pure248 => .unary
  | .pure249 => .unary
  | .pure250 => .unary
  | .pure251 => .unary
  | .pure252 => .unary
  | .pure253 => .unary
  | .pure254 => .unary
  | .pure255 => .unary

def pureMeaning (subopcode : Nat) : Option Operation :=
  if subopcode ≥ 256 then none else match subopcode with
  | 14 => some .pure14
  | 15 => some .pure15
  | 16 => some .pure16
  | 17 => some .pure17
  | 18 => some .pure18
  | 19 => some .pure19
  | 20 => some .pure20
  | 35 => some .pure35
  | 36 => some .pure36
  | 37 => some .pure37
  | 38 => some .pure38
  | 39 => some .pure39
  | 40 => some .pure40
  | 41 => some .pure41
  | 42 => some .pure42
  | 43 => some .pure43
  | 44 => some .pure44
  | 45 => some .pure45
  | 46 => some .pure46
  | 47 => some .pure47
  | 48 => some .pure48
  | 49 => some .pure49
  | 50 => some .pure50
  | 51 => some .pure51
  | 52 => some .pure52
  | 53 => some .pure53
  | 54 => some .pure54
  | 55 => some .pure55
  | 56 => some .pure56
  | 57 => some .pure57
  | 58 => some .pure58
  | 59 => some .pure59
  | 60 => some .pure60
  | 61 => some .pure61
  | 62 => some .pure62
  | 63 => some .pure63
  | 64 => some .pure64
  | 65 => some .pure65
  | 66 => some .pure66
  | 67 => some .pure67
  | 68 => some .pure68
  | 69 => some .pure69
  | 70 => some .pure70
  | 71 => some .pure71
  | 72 => some .pure72
  | 73 => some .pure73
  | 74 => some .pure74
  | 75 => some .pure75
  | 76 => some .pure76
  | 77 => some .pure77
  | 78 => some .pure78
  | 79 => some .pure79
  | 80 => some .pure80
  | 81 => some .pure81
  | 82 => some .pure82
  | 83 => some .pure83
  | 94 => some .pure94
  | 95 => some .pure95
  | 96 => some .pure96
  | 97 => some .pure97
  | 98 => some .pure98
  | 99 => some .pure99
  | 100 => some .pure100
  | 101 => some .pure101
  | 102 => some .pure102
  | 103 => some .pure103
  | 104 => some .pure104
  | 105 => some .pure105
  | 106 => some .pure106
  | 107 => some .pure107
  | 108 => some .pure108
  | 109 => some .pure109
  | 110 => some .pure110
  | 111 => some .pure111
  | 112 => some .pure112
  | 113 => some .pure113
  | 114 => some .pure114
  | 115 => some .pure115
  | 116 => some .pure116
  | 117 => some .pure117
  | 118 => some .pure118
  | 119 => some .pure119
  | 120 => some .pure120
  | 121 => some .pure121
  | 122 => some .pure122
  | 123 => some .pure123
  | 124 => some .pure124
  | 125 => some .pure125
  | 126 => some .pure126
  | 127 => some .pure127
  | 128 => some .pure128
  | 129 => some .pure129
  | 130 => some .pure130
  | 131 => some .pure131
  | 132 => some .pure132
  | 133 => some .pure133
  | 134 => some .pure134
  | 135 => some .pure135
  | 136 => some .pure136
  | 137 => some .pure137
  | 138 => some .pure138
  | 139 => some .pure139
  | 140 => some .pure140
  | 141 => some .pure141
  | 142 => some .pure142
  | 143 => some .pure143
  | 144 => some .pure144
  | 145 => some .pure145
  | 146 => some .pure146
  | 147 => some .pure147
  | 148 => some .pure148
  | 149 => some .pure149
  | 150 => some .pure150
  | 151 => some .pure151
  | 152 => some .pure152
  | 153 => some .pure153
  | 155 => some .pure155
  | 156 => some .pure156
  | 157 => some .pure157
  | 158 => some .pure158
  | 159 => some .pure159
  | 160 => some .pure160
  | 161 => some .pure161
  | 163 => some .pure163
  | 164 => some .pure164
  | 167 => some .pure167
  | 168 => some .pure168
  | 169 => some .pure169
  | 170 => some .pure170
  | 171 => some .pure171
  | 172 => some .pure172
  | 173 => some .pure173
  | 174 => some .pure174
  | 177 => some .pure177
  | 181 => some .pure181
  | 182 => some .pure182
  | 183 => some .pure183
  | 184 => some .pure184
  | 185 => some .pure185
  | 186 => some .pure186
  | 188 => some .pure188
  | 189 => some .pure189
  | 190 => some .pure190
  | 191 => some .pure191
  | 192 => some .pure192
  | 193 => some .pure193
  | 195 => some .pure195
  | 196 => some .pure196
  | 199 => some .pure199
  | 200 => some .pure200
  | 201 => some .pure201
  | 202 => some .pure202
  | 203 => some .pure203
  | 204 => some .pure204
  | 205 => some .pure205
  | 206 => some .pure206
  | 209 => some .pure209
  | 213 => some .pure213
  | 214 => some .pure214
  | 215 => some .pure215
  | 216 => some .pure216
  | 217 => some .pure217
  | 218 => some .pure218
  | 219 => some .pure219
  | 220 => some .pure220
  | 221 => some .pure221
  | 222 => some .pure222
  | 223 => some .pure223
  | 224 => some .pure224
  | 225 => some .pure225
  | 227 => some .pure227
  | 228 => some .pure228
  | 229 => some .pure229
  | 230 => some .pure230
  | 231 => some .pure231
  | 232 => some .pure232
  | 233 => some .pure233
  | 234 => some .pure234
  | 235 => some .pure235
  | 236 => some .pure236
  | 237 => some .pure237
  | 239 => some .pure239
  | 240 => some .pure240
  | 241 => some .pure241
  | 242 => some .pure242
  | 243 => some .pure243
  | 244 => some .pure244
  | 245 => some .pure245
  | 246 => some .pure246
  | 247 => some .pure247
  | 248 => some .pure248
  | 249 => some .pure249
  | 250 => some .pure250
  | 251 => some .pure251
  | 252 => some .pure252
  | 253 => some .pure253
  | 254 => some .pure254
  | 255 => some .pure255
  | _ => none


end Itasca.Body.Simd

end

/-! ## SimdPureMeaning -/

section

/-!
# Correctness of pure SIMD classifications

The public grammar maps bytes to SpecTec instructions without carrying proofs.
This module proves that the compiler classifications agree with that mapping and
have the stated signatures. The private certificates are a construction device;
no public semantic definition depends on them.
-/

namespace Itasca.Body.Simd

private theorem integer8_wf : wf_ishape (.mk_ishape (.X .I8 (.mk_dim 16))) := by
  apply wf_ishape.ishape_case_0 .I8
  · repeat' first | decide | constructor
  · rfl

private theorem integer16_wf : wf_ishape (.mk_ishape (.X .I16 (.mk_dim 8))) := by
  apply wf_ishape.ishape_case_0 .I16
  · repeat' first | decide | constructor
  · rfl

private theorem integer32_wf : wf_ishape (.mk_ishape (.X .I32 (.mk_dim 4))) := by
  apply wf_ishape.ishape_case_0 .I32
  · repeat' first | decide | constructor
  · rfl

private theorem integer64_wf : wf_ishape (.mk_ishape (.X .I64 (.mk_dim 2))) := by
  apply wf_ishape.ishape_case_0 .I64
  · repeat' first | decide | constructor
  · rfl

-- Scoped names let literal operation tables reuse these private shape proofs.
scoped notation "integer8_wf" => integer8_wf
scoped notation "integer16_wf" => integer16_wf
scoped notation "integer32_wf" => integer32_wf
scoped notation "integer64_wf" => integer64_wf

end Itasca.Body.Simd

open Aeneas Aeneas.Std

-- The shape scope supplies kernel-checked well-formedness witnesses for literal SIMD shapes.
open scoped Itasca.Body.Simd

namespace Itasca.Body.Simd

/-- A SIMD instruction without immediates with its signature, and proofs that it is well formed,
typed with that signature, free of declared-reference obligations, and that the signature is the
only one the generated rules give it. -/
private structure Certificate (op : Operation) where
  instruction : instr
  signature : Signature
  wellFormed : wf_instr instruction
  typed : ∀ C, wf_context C → Instr_ok C instruction
    (.mk_functype (.mk_list signature.inputs) (.mk_list signature.outputs))
  declared : ∀ refs, Spec.DeclaredReferences.Instruction refs instruction
  principal : ∀ C ins outs, Instr_ok C instruction (.mk_functype (.mk_list ins) (.mk_list outs)) →
    ins = signature.inputs ∧ outs = signature.outputs
  source : instruction = op.instruction
  shape : signature = op.signature

/-!
## Shared certificate construction

Each private row supplies its instruction, signature and generated typing rule.
The macro only shares proof scaffolding. Lean checks well-formedness, typing,
declared references and principal signatures for every row. The projection
lemmas connect these witnesses to the public data classifications; the final
correspondence theorem connects the classification table to binary decoding.
-/
macro "simdOperation%(" instruction:term ", " signature:term
    ", " rule:term ")" : term =>
  `(let instruction : instr := $instruction
    let hwf : wf_instr instruction := by
      dsimp only [instruction]
      repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
    { instruction := instruction, signature := $signature, wellFormed := hwf,
      typed := fun C hC => by exact $rule C hC hwf,
      declared := fun _ => by simp [instruction, Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices],
      principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩,
      source := rfl, shape := rfl : Certificate _ })

private def cert14 : Certificate .pure14 :=
  simdOperation%((.VSWIZZLE (.mk_ishape (.X .I8 (.mk_dim 16)))), .binary,
    (fun C => Instr_ok.vswizzle C _))

private def cert15 : Certificate .pure15 :=
  simdOperation%((.VSPLAT (.X .I8 (.mk_dim 16))), .splatI32,
    (fun C => Instr_ok.vsplat C _))

private def cert16 : Certificate .pure16 :=
  simdOperation%((.VSPLAT (.X .I16 (.mk_dim 8))), .splatI32,
    (fun C => Instr_ok.vsplat C _))

private def cert17 : Certificate .pure17 :=
  simdOperation%((.VSPLAT (.X .I32 (.mk_dim 4))), .splatI32,
    (fun C => Instr_ok.vsplat C _))

private def cert18 : Certificate .pure18 :=
  simdOperation%((.VSPLAT (.X .I64 (.mk_dim 2))), .splatI64,
    (fun C => Instr_ok.vsplat C _))

private def cert19 : Certificate .pure19 :=
  simdOperation%((.VSPLAT (.X .F32 (.mk_dim 4))), .splatF32,
    (fun C => Instr_ok.vsplat C _))

private def cert20 : Certificate .pure20 :=
  simdOperation%((.VSPLAT (.X .F64 (.mk_dim 2))), .splatF64,
    (fun C => Instr_ok.vsplat C _))

private def cert35 : Certificate .pure35 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 .EQ)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert36 : Certificate .pure36 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 .NE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert37 : Certificate .pure37 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LT .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert38 : Certificate .pure38 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LT .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert39 : Certificate .pure39 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GT .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert40 : Certificate .pure40 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GT .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert41 : Certificate .pure41 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LE .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert42 : Certificate .pure42 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LE .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert43 : Certificate .pure43 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GE .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert44 : Certificate .pure44 :=
  simdOperation%((.VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GE .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert45 : Certificate .pure45 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 .EQ)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert46 : Certificate .pure46 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 .NE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert47 : Certificate .pure47 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LT .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert48 : Certificate .pure48 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LT .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert49 : Certificate .pure49 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GT .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert50 : Certificate .pure50 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GT .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert51 : Certificate .pure51 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LE .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert52 : Certificate .pure52 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LE .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert53 : Certificate .pure53 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GE .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert54 : Certificate .pure54 :=
  simdOperation%((.VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GE .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert55 : Certificate .pure55 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 .EQ)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert56 : Certificate .pure56 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 .NE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert57 : Certificate .pure57 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LT .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert58 : Certificate .pure58 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LT .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert59 : Certificate .pure59 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GT .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert60 : Certificate .pure60 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GT .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert61 : Certificate .pure61 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LE .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert62 : Certificate .pure62 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LE .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert63 : Certificate .pure63 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GE .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert64 : Certificate .pure64 :=
  simdOperation%((.VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GE .U))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert65 : Certificate .pure65 :=
  simdOperation%((.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .EQ)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert66 : Certificate .pure66 :=
  simdOperation%((.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .NE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert67 : Certificate .pure67 :=
  simdOperation%((.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .LT)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert68 : Certificate .pure68 :=
  simdOperation%((.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .GT)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert69 : Certificate .pure69 :=
  simdOperation%((.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .LE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert70 : Certificate .pure70 :=
  simdOperation%((.VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .GE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert71 : Certificate .pure71 :=
  simdOperation%((.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .EQ)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert72 : Certificate .pure72 :=
  simdOperation%((.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .NE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert73 : Certificate .pure73 :=
  simdOperation%((.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .LT)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert74 : Certificate .pure74 :=
  simdOperation%((.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .GT)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert75 : Certificate .pure75 :=
  simdOperation%((.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .LE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert76 : Certificate .pure76 :=
  simdOperation%((.VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .GE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert77 : Certificate .pure77 :=
  simdOperation%((.VVUNOP .V128 .NOT), .unary,
    (fun C => Instr_ok.vvunop C _))

private def cert78 : Certificate .pure78 :=
  simdOperation%((.VVBINOP .V128 .AND), .binary,
    (fun C => Instr_ok.vvbinop C _))

private def cert79 : Certificate .pure79 :=
  simdOperation%((.VVBINOP .V128 .ANDNOT), .binary,
    (fun C => Instr_ok.vvbinop C _))

private def cert80 : Certificate .pure80 :=
  simdOperation%((.VVBINOP .V128 .OR), .binary,
    (fun C => Instr_ok.vvbinop C _))

private def cert81 : Certificate .pure81 :=
  simdOperation%((.VVBINOP .V128 .XOR), .binary,
    (fun C => Instr_ok.vvbinop C _))

private def cert82 : Certificate .pure82 :=
  simdOperation%((.VVTERNOP .V128 .BITSELECT), .ternary,
    (fun C => Instr_ok.vvternop C _))

private def cert83 : Certificate .pure83 :=
  simdOperation%((.VVTESTOP .V128 .ANY_TRUE), .test,
    (fun C => Instr_ok.vvtestop C _))

private def cert94 : Certificate .pure94 :=
  simdOperation%((.VCVTOP (.X .F32 (.mk_dim 4)) (.X .F64 (.mk_dim 2)) (.mk_vcvtop___3 .F64 2 .F32 4 (.DEMOTE .ZERO))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert95 : Certificate .pure95 :=
  simdOperation%((.VCVTOP (.X .F64 (.mk_dim 2)) (.X .F32 (.mk_dim 4)) (.mk_vcvtop___3 .F32 4 .F64 2 .PROMOTELOW)), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert96 : Certificate .pure96 :=
  simdOperation%((.VUNOP (.X .I8 (.mk_dim 16)) (.mk_vunop__0 .I8 16 .ABS)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert97 : Certificate .pure97 :=
  simdOperation%((.VUNOP (.X .I8 (.mk_dim 16)) (.mk_vunop__0 .I8 16 .NEG)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert98 : Certificate .pure98 :=
  simdOperation%((.VUNOP (.X .I8 (.mk_dim 16)) (.mk_vunop__0 .I8 16 .POPCNT)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert99 : Certificate .pure99 :=
  simdOperation%((.VTESTOP (.X .I8 (.mk_dim 16)) (.mk_vtestop__0 .I8 16 .ALL_TRUE)), .test,
    (fun C => Instr_ok.vtestop C _ _))

private def cert100 : Certificate .pure100 :=
  simdOperation%((.VBITMASK (.mk_ishape (.X .I8 (.mk_dim 16)))), .test,
    (fun C => Instr_ok.vbitmask C _))

private def cert101 : Certificate .pure101 :=
  simdOperation%((.VNARROW (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_ishape (.X .I16 (.mk_dim 8))) .S), .binary,
    (fun C => Instr_ok.vnarrow C _ _ _))

private def cert102 : Certificate .pure102 :=
  simdOperation%((.VNARROW (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_ishape (.X .I16 (.mk_dim 8))) .U), .binary,
    (fun C => Instr_ok.vnarrow C _ _ _))

private def cert103 : Certificate .pure103 :=
  simdOperation%((.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .CEIL)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert104 : Certificate .pure104 :=
  simdOperation%((.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .FLOOR)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert105 : Certificate .pure105 :=
  simdOperation%((.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .TRUNC)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert106 : Certificate .pure106 :=
  simdOperation%((.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .NEAREST)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert107 : Certificate .pure107 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vshiftop__0 .I8 16 .SHL)), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert108 : Certificate .pure108 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vshiftop__0 .I8 16 (.SHR .S))), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert109 : Certificate .pure109 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vshiftop__0 .I8 16 (.SHR .U))), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert110 : Certificate .pure110 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 .ADD)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert111 : Certificate .pure111 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.ADD_SAT .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert112 : Certificate .pure112 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.ADD_SAT .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert113 : Certificate .pure113 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 .SUB)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert114 : Certificate .pure114 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.SUB_SAT .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert115 : Certificate .pure115 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.SUB_SAT .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert116 : Certificate .pure116 :=
  simdOperation%((.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .CEIL)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert117 : Certificate .pure117 :=
  simdOperation%((.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .FLOOR)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert118 : Certificate .pure118 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MIN .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert119 : Certificate .pure119 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MIN .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert120 : Certificate .pure120 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MAX .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert121 : Certificate .pure121 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MAX .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert122 : Certificate .pure122 :=
  simdOperation%((.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .TRUNC)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert123 : Certificate .pure123 :=
  simdOperation%((.VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 .AVGRU)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert124 : Certificate .pure124 :=
  simdOperation%((.VEXTUNOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextunop___0 .I8 16 .I16 8 (.EXTADD_PAIRWISE .S))), .unary,
    (fun C => Instr_ok.vextunop C _ _ _))

private def cert125 : Certificate .pure125 :=
  simdOperation%((.VEXTUNOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextunop___0 .I8 16 .I16 8 (.EXTADD_PAIRWISE .U))), .unary,
    (fun C => Instr_ok.vextunop C _ _ _))

private def cert126 : Certificate .pure126 :=
  simdOperation%((.VEXTUNOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextunop___0 .I16 8 .I32 4 (.EXTADD_PAIRWISE .S))), .unary,
    (fun C => Instr_ok.vextunop C _ _ _))

private def cert127 : Certificate .pure127 :=
  simdOperation%((.VEXTUNOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextunop___0 .I16 8 .I32 4 (.EXTADD_PAIRWISE .U))), .unary,
    (fun C => Instr_ok.vextunop C _ _ _))

private def cert128 : Certificate .pure128 :=
  simdOperation%((.VUNOP (.X .I16 (.mk_dim 8)) (.mk_vunop__0 .I16 8 .ABS)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert129 : Certificate .pure129 :=
  simdOperation%((.VUNOP (.X .I16 (.mk_dim 8)) (.mk_vunop__0 .I16 8 .NEG)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert130 : Certificate .pure130 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .Q15MULR_SATS)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert131 : Certificate .pure131 :=
  simdOperation%((.VTESTOP (.X .I16 (.mk_dim 8)) (.mk_vtestop__0 .I16 8 .ALL_TRUE)), .test,
    (fun C => Instr_ok.vtestop C _ _))

private def cert132 : Certificate .pure132 :=
  simdOperation%((.VBITMASK (.mk_ishape (.X .I16 (.mk_dim 8)))), .test,
    (fun C => Instr_ok.vbitmask C _))

private def cert133 : Certificate .pure133 :=
  simdOperation%((.VNARROW (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I32 (.mk_dim 4))) .S), .binary,
    (fun C => Instr_ok.vnarrow C _ _ _))

private def cert134 : Certificate .pure134 :=
  simdOperation%((.VNARROW (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I32 (.mk_dim 4))) .U), .binary,
    (fun C => Instr_ok.vnarrow C _ _ _))

private def cert135 : Certificate .pure135 :=
  simdOperation%((.VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .LOW .S))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert136 : Certificate .pure136 :=
  simdOperation%((.VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .HIGH .S))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert137 : Certificate .pure137 :=
  simdOperation%((.VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .LOW .U))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert138 : Certificate .pure138 :=
  simdOperation%((.VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .HIGH .U))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert139 : Certificate .pure139 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vshiftop__0 .I16 8 .SHL)), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert140 : Certificate .pure140 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vshiftop__0 .I16 8 (.SHR .S))), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert141 : Certificate .pure141 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vshiftop__0 .I16 8 (.SHR .U))), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert142 : Certificate .pure142 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .ADD)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert143 : Certificate .pure143 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.ADD_SAT .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert144 : Certificate .pure144 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.ADD_SAT .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert145 : Certificate .pure145 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .SUB)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert146 : Certificate .pure146 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.SUB_SAT .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert147 : Certificate .pure147 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.SUB_SAT .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert148 : Certificate .pure148 :=
  simdOperation%((.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .NEAREST)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert149 : Certificate .pure149 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .MUL)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert150 : Certificate .pure150 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MIN .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert151 : Certificate .pure151 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MIN .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert152 : Certificate .pure152 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MAX .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert153 : Certificate .pure153 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MAX .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert155 : Certificate .pure155 :=
  simdOperation%((.VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .AVGRU)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert156 : Certificate .pure156 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .LOW .S))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert157 : Certificate .pure157 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .HIGH .S))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert158 : Certificate .pure158 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .LOW .U))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert159 : Certificate .pure159 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .HIGH .U))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert160 : Certificate .pure160 :=
  simdOperation%((.VUNOP (.X .I32 (.mk_dim 4)) (.mk_vunop__0 .I32 4 .ABS)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert161 : Certificate .pure161 :=
  simdOperation%((.VUNOP (.X .I32 (.mk_dim 4)) (.mk_vunop__0 .I32 4 .NEG)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert163 : Certificate .pure163 :=
  simdOperation%((.VTESTOP (.X .I32 (.mk_dim 4)) (.mk_vtestop__0 .I32 4 .ALL_TRUE)), .test,
    (fun C => Instr_ok.vtestop C _ _))

private def cert164 : Certificate .pure164 :=
  simdOperation%((.VBITMASK (.mk_ishape (.X .I32 (.mk_dim 4)))), .test,
    (fun C => Instr_ok.vbitmask C _))

private def cert167 : Certificate .pure167 :=
  simdOperation%((.VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .LOW .S))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert168 : Certificate .pure168 :=
  simdOperation%((.VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .HIGH .S))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert169 : Certificate .pure169 :=
  simdOperation%((.VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .LOW .U))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert170 : Certificate .pure170 :=
  simdOperation%((.VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .HIGH .U))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert171 : Certificate .pure171 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vshiftop__0 .I32 4 .SHL)), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert172 : Certificate .pure172 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vshiftop__0 .I32 4 (.SHR .S))), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert173 : Certificate .pure173 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vshiftop__0 .I32 4 (.SHR .U))), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert174 : Certificate .pure174 :=
  simdOperation%((.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 .ADD)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert177 : Certificate .pure177 :=
  simdOperation%((.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 .SUB)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert181 : Certificate .pure181 :=
  simdOperation%((.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 .MUL)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert182 : Certificate .pure182 :=
  simdOperation%((.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MIN .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert183 : Certificate .pure183 :=
  simdOperation%((.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MIN .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert184 : Certificate .pure184 :=
  simdOperation%((.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MAX .S))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert185 : Certificate .pure185 :=
  simdOperation%((.VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MAX .U))), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert186 : Certificate .pure186 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 .DOTS)), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert188 : Certificate .pure188 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .LOW .S))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert189 : Certificate .pure189 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .HIGH .S))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert190 : Certificate .pure190 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .LOW .U))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert191 : Certificate .pure191 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .HIGH .U))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert192 : Certificate .pure192 :=
  simdOperation%((.VUNOP (.X .I64 (.mk_dim 2)) (.mk_vunop__0 .I64 2 .ABS)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert193 : Certificate .pure193 :=
  simdOperation%((.VUNOP (.X .I64 (.mk_dim 2)) (.mk_vunop__0 .I64 2 .NEG)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert195 : Certificate .pure195 :=
  simdOperation%((.VTESTOP (.X .I64 (.mk_dim 2)) (.mk_vtestop__0 .I64 2 .ALL_TRUE)), .test,
    (fun C => Instr_ok.vtestop C _ _))

private def cert196 : Certificate .pure196 :=
  simdOperation%((.VBITMASK (.mk_ishape (.X .I64 (.mk_dim 2)))), .test,
    (fun C => Instr_ok.vbitmask C _))

private def cert199 : Certificate .pure199 :=
  simdOperation%((.VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .LOW .S))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert200 : Certificate .pure200 :=
  simdOperation%((.VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .HIGH .S))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert201 : Certificate .pure201 :=
  simdOperation%((.VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .LOW .U))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert202 : Certificate .pure202 :=
  simdOperation%((.VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .HIGH .U))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert203 : Certificate .pure203 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_vshiftop__0 .I64 2 .SHL)), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert204 : Certificate .pure204 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_vshiftop__0 .I64 2 (.SHR .S))), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert205 : Certificate .pure205 :=
  simdOperation%((.VSHIFTOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_vshiftop__0 .I64 2 (.SHR .U))), .shift,
    (fun C => Instr_ok.vshiftop C _ _))

private def cert206 : Certificate .pure206 :=
  simdOperation%((.VBINOP (.X .I64 (.mk_dim 2)) (.mk_vbinop__0 .I64 2 .ADD)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert209 : Certificate .pure209 :=
  simdOperation%((.VBINOP (.X .I64 (.mk_dim 2)) (.mk_vbinop__0 .I64 2 .SUB)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert213 : Certificate .pure213 :=
  simdOperation%((.VBINOP (.X .I64 (.mk_dim 2)) (.mk_vbinop__0 .I64 2 .MUL)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert214 : Certificate .pure214 :=
  simdOperation%((.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 .EQ)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert215 : Certificate .pure215 :=
  simdOperation%((.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 .NE)), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert216 : Certificate .pure216 :=
  simdOperation%((.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.LT .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert217 : Certificate .pure217 :=
  simdOperation%((.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.GT .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert218 : Certificate .pure218 :=
  simdOperation%((.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.LE .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert219 : Certificate .pure219 :=
  simdOperation%((.VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.GE .S))), .binary,
    (fun C => Instr_ok.vrelop C _ _))

private def cert220 : Certificate .pure220 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .LOW .S))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert221 : Certificate .pure221 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .HIGH .S))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert222 : Certificate .pure222 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .LOW .U))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert223 : Certificate .pure223 :=
  simdOperation%((.VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .HIGH .U))), .binary,
    (fun C => Instr_ok.vextbinop C _ _ _))

private def cert224 : Certificate .pure224 :=
  simdOperation%((.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .ABS)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert225 : Certificate .pure225 :=
  simdOperation%((.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .NEG)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert227 : Certificate .pure227 :=
  simdOperation%((.VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .SQRT)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert228 : Certificate .pure228 :=
  simdOperation%((.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .ADD)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert229 : Certificate .pure229 :=
  simdOperation%((.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .SUB)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert230 : Certificate .pure230 :=
  simdOperation%((.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .MUL)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert231 : Certificate .pure231 :=
  simdOperation%((.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .DIV)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert232 : Certificate .pure232 :=
  simdOperation%((.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .MIN)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert233 : Certificate .pure233 :=
  simdOperation%((.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .MAX)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert234 : Certificate .pure234 :=
  simdOperation%((.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .PMIN)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert235 : Certificate .pure235 :=
  simdOperation%((.VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .PMAX)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert236 : Certificate .pure236 :=
  simdOperation%((.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .ABS)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert237 : Certificate .pure237 :=
  simdOperation%((.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .NEG)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert239 : Certificate .pure239 :=
  simdOperation%((.VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .SQRT)), .unary,
    (fun C => Instr_ok.vunop C _ _))

private def cert240 : Certificate .pure240 :=
  simdOperation%((.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .ADD)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert241 : Certificate .pure241 :=
  simdOperation%((.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .SUB)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert242 : Certificate .pure242 :=
  simdOperation%((.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .MUL)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert243 : Certificate .pure243 :=
  simdOperation%((.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .DIV)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert244 : Certificate .pure244 :=
  simdOperation%((.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .MIN)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert245 : Certificate .pure245 :=
  simdOperation%((.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .MAX)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert246 : Certificate .pure246 :=
  simdOperation%((.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .PMIN)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert247 : Certificate .pure247 :=
  simdOperation%((.VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .PMAX)), .binary,
    (fun C => Instr_ok.vbinop C _ _))

private def cert248 : Certificate .pure248 :=
  simdOperation%((.VCVTOP (.X .I32 (.mk_dim 4)) (.X .F32 (.mk_dim 4)) (.mk_vcvtop___2 .F32 4 .I32 4 (.TRUNC_SAT .S none))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert249 : Certificate .pure249 :=
  simdOperation%((.VCVTOP (.X .I32 (.mk_dim 4)) (.X .F32 (.mk_dim 4)) (.mk_vcvtop___2 .F32 4 .I32 4 (.TRUNC_SAT .U none))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert250 : Certificate .pure250 :=
  simdOperation%((.VCVTOP (.X .F32 (.mk_dim 4)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F32 4 (.CONVERT none .S))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert251 : Certificate .pure251 :=
  simdOperation%((.VCVTOP (.X .F32 (.mk_dim 4)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F32 4 (.CONVERT none .U))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert252 : Certificate .pure252 :=
  simdOperation%((.VCVTOP (.X .I32 (.mk_dim 4)) (.X .F64 (.mk_dim 2)) (.mk_vcvtop___2 .F64 2 .I32 4 (.TRUNC_SAT .S (some .ZERO)))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert253 : Certificate .pure253 :=
  simdOperation%((.VCVTOP (.X .I32 (.mk_dim 4)) (.X .F64 (.mk_dim 2)) (.mk_vcvtop___2 .F64 2 .I32 4 (.TRUNC_SAT .U (some .ZERO)))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert254 : Certificate .pure254 :=
  simdOperation%((.VCVTOP (.X .F64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F64 2 (.CONVERT (some .LOW) .S))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def cert255 : Certificate .pure255 :=
  simdOperation%((.VCVTOP (.X .F64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F64 2 (.CONVERT (some .LOW) .U))), .unary,
    (fun C => Instr_ok.vcvtop C _ _ _))

private def certificate : (op : Operation) → Certificate op
  | .pure14 => cert14
  | .pure15 => cert15
  | .pure16 => cert16
  | .pure17 => cert17
  | .pure18 => cert18
  | .pure19 => cert19
  | .pure20 => cert20
  | .pure35 => cert35
  | .pure36 => cert36
  | .pure37 => cert37
  | .pure38 => cert38
  | .pure39 => cert39
  | .pure40 => cert40
  | .pure41 => cert41
  | .pure42 => cert42
  | .pure43 => cert43
  | .pure44 => cert44
  | .pure45 => cert45
  | .pure46 => cert46
  | .pure47 => cert47
  | .pure48 => cert48
  | .pure49 => cert49
  | .pure50 => cert50
  | .pure51 => cert51
  | .pure52 => cert52
  | .pure53 => cert53
  | .pure54 => cert54
  | .pure55 => cert55
  | .pure56 => cert56
  | .pure57 => cert57
  | .pure58 => cert58
  | .pure59 => cert59
  | .pure60 => cert60
  | .pure61 => cert61
  | .pure62 => cert62
  | .pure63 => cert63
  | .pure64 => cert64
  | .pure65 => cert65
  | .pure66 => cert66
  | .pure67 => cert67
  | .pure68 => cert68
  | .pure69 => cert69
  | .pure70 => cert70
  | .pure71 => cert71
  | .pure72 => cert72
  | .pure73 => cert73
  | .pure74 => cert74
  | .pure75 => cert75
  | .pure76 => cert76
  | .pure77 => cert77
  | .pure78 => cert78
  | .pure79 => cert79
  | .pure80 => cert80
  | .pure81 => cert81
  | .pure82 => cert82
  | .pure83 => cert83
  | .pure94 => cert94
  | .pure95 => cert95
  | .pure96 => cert96
  | .pure97 => cert97
  | .pure98 => cert98
  | .pure99 => cert99
  | .pure100 => cert100
  | .pure101 => cert101
  | .pure102 => cert102
  | .pure103 => cert103
  | .pure104 => cert104
  | .pure105 => cert105
  | .pure106 => cert106
  | .pure107 => cert107
  | .pure108 => cert108
  | .pure109 => cert109
  | .pure110 => cert110
  | .pure111 => cert111
  | .pure112 => cert112
  | .pure113 => cert113
  | .pure114 => cert114
  | .pure115 => cert115
  | .pure116 => cert116
  | .pure117 => cert117
  | .pure118 => cert118
  | .pure119 => cert119
  | .pure120 => cert120
  | .pure121 => cert121
  | .pure122 => cert122
  | .pure123 => cert123
  | .pure124 => cert124
  | .pure125 => cert125
  | .pure126 => cert126
  | .pure127 => cert127
  | .pure128 => cert128
  | .pure129 => cert129
  | .pure130 => cert130
  | .pure131 => cert131
  | .pure132 => cert132
  | .pure133 => cert133
  | .pure134 => cert134
  | .pure135 => cert135
  | .pure136 => cert136
  | .pure137 => cert137
  | .pure138 => cert138
  | .pure139 => cert139
  | .pure140 => cert140
  | .pure141 => cert141
  | .pure142 => cert142
  | .pure143 => cert143
  | .pure144 => cert144
  | .pure145 => cert145
  | .pure146 => cert146
  | .pure147 => cert147
  | .pure148 => cert148
  | .pure149 => cert149
  | .pure150 => cert150
  | .pure151 => cert151
  | .pure152 => cert152
  | .pure153 => cert153
  | .pure155 => cert155
  | .pure156 => cert156
  | .pure157 => cert157
  | .pure158 => cert158
  | .pure159 => cert159
  | .pure160 => cert160
  | .pure161 => cert161
  | .pure163 => cert163
  | .pure164 => cert164
  | .pure167 => cert167
  | .pure168 => cert168
  | .pure169 => cert169
  | .pure170 => cert170
  | .pure171 => cert171
  | .pure172 => cert172
  | .pure173 => cert173
  | .pure174 => cert174
  | .pure177 => cert177
  | .pure181 => cert181
  | .pure182 => cert182
  | .pure183 => cert183
  | .pure184 => cert184
  | .pure185 => cert185
  | .pure186 => cert186
  | .pure188 => cert188
  | .pure189 => cert189
  | .pure190 => cert190
  | .pure191 => cert191
  | .pure192 => cert192
  | .pure193 => cert193
  | .pure195 => cert195
  | .pure196 => cert196
  | .pure199 => cert199
  | .pure200 => cert200
  | .pure201 => cert201
  | .pure202 => cert202
  | .pure203 => cert203
  | .pure204 => cert204
  | .pure205 => cert205
  | .pure206 => cert206
  | .pure209 => cert209
  | .pure213 => cert213
  | .pure214 => cert214
  | .pure215 => cert215
  | .pure216 => cert216
  | .pure217 => cert217
  | .pure218 => cert218
  | .pure219 => cert219
  | .pure220 => cert220
  | .pure221 => cert221
  | .pure222 => cert222
  | .pure223 => cert223
  | .pure224 => cert224
  | .pure225 => cert225
  | .pure227 => cert227
  | .pure228 => cert228
  | .pure229 => cert229
  | .pure230 => cert230
  | .pure231 => cert231
  | .pure232 => cert232
  | .pure233 => cert233
  | .pure234 => cert234
  | .pure235 => cert235
  | .pure236 => cert236
  | .pure237 => cert237
  | .pure239 => cert239
  | .pure240 => cert240
  | .pure241 => cert241
  | .pure242 => cert242
  | .pure243 => cert243
  | .pure244 => cert244
  | .pure245 => cert245
  | .pure246 => cert246
  | .pure247 => cert247
  | .pure248 => cert248
  | .pure249 => cert249
  | .pure250 => cert250
  | .pure251 => cert251
  | .pure252 => cert252
  | .pure253 => cert253
  | .pure254 => cert254
  | .pure255 => cert255

private theorem certificate_instruction (op : Operation) : (certificate op).instruction = op.instruction :=
  (certificate op).source

private theorem certificate_signature (op : Operation) : (certificate op).signature = op.signature :=
  (certificate op).shape

theorem Operation.wellFormed (op : Operation) : wf_instr op.instruction := by
  rw [← certificate_instruction]
  exact (certificate op).wellFormed

theorem Operation.typed (op : Operation) (C : context) (h : wf_context C) :
    Instr_ok C op.instruction (.mk_functype (.mk_list op.signature.inputs) (.mk_list op.signature.outputs)) := by
  rw [← certificate_instruction, ← certificate_signature]
  exact (certificate op).typed C h

theorem Operation.declared (op : Operation) (refs : List funcidx) :
    Spec.DeclaredReferences.Instruction refs op.instruction := by
  rw [← certificate_instruction]
  exact (certificate op).declared refs

theorem Operation.principal (op : Operation) (C : context) (ins outs : List valtype)
    (h : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.signature.inputs ∧ outs = op.signature.outputs := by
  rw [← certificate_instruction] at h
  rw [← certificate_signature]
  exact (certificate op).principal C ins outs h

private theorem pureInstruction_eq_0 (opcode : Nat) (lo : 0 ≤ opcode) (hi : opcode < 16) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_1 (opcode : Nat) (lo : 16 ≤ opcode) (hi : opcode < 32) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_2 (opcode : Nat) (lo : 32 ≤ opcode) (hi : opcode < 48) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_3 (opcode : Nat) (lo : 48 ≤ opcode) (hi : opcode < 64) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_4 (opcode : Nat) (lo : 64 ≤ opcode) (hi : opcode < 80) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_5 (opcode : Nat) (lo : 80 ≤ opcode) (hi : opcode < 96) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_6 (opcode : Nat) (lo : 96 ≤ opcode) (hi : opcode < 112) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_7 (opcode : Nat) (lo : 112 ≤ opcode) (hi : opcode < 128) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_8 (opcode : Nat) (lo : 128 ≤ opcode) (hi : opcode < 144) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_9 (opcode : Nat) (lo : 144 ≤ opcode) (hi : opcode < 160) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_10 (opcode : Nat) (lo : 160 ≤ opcode) (hi : opcode < 176) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_11 (opcode : Nat) (lo : 176 ≤ opcode) (hi : opcode < 192) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_12 (opcode : Nat) (lo : 192 ≤ opcode) (hi : opcode < 208) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_13 (opcode : Nat) (lo : 208 ≤ opcode) (hi : opcode < 224) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_14 (opcode : Nat) (lo : 224 ≤ opcode) (hi : opcode < 240) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

private theorem pureInstruction_eq_15 (opcode : Nat) (lo : 240 ≤ opcode) (hi : opcode < 256) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  interval_cases opcode <;> rfl

theorem pureInstruction_eq (opcode : Nat) :
    pureInstruction opcode = (pureMeaning opcode).map Operation.instruction := by
  by_cases high : 256 ≤ opcode
  · have left : pureInstruction opcode = none := if_pos high
    have right : pureMeaning opcode = none := if_pos high
    exact left.trans (congrArg (Option.map Operation.instruction) right).symm
  · have ranges : ( 0 ≤ opcode ∧ opcode < 16) ∨ ( 16 ≤ opcode ∧ opcode < 32) ∨ ( 32 ≤ opcode ∧ opcode < 48) ∨ ( 48 ≤ opcode ∧ opcode < 64) ∨ ( 64 ≤ opcode ∧ opcode < 80) ∨ ( 80 ≤ opcode ∧ opcode < 96) ∨ ( 96 ≤ opcode ∧ opcode < 112) ∨ ( 112 ≤ opcode ∧ opcode < 128) ∨ ( 128 ≤ opcode ∧ opcode < 144) ∨ ( 144 ≤ opcode ∧ opcode < 160) ∨ ( 160 ≤ opcode ∧ opcode < 176) ∨ ( 176 ≤ opcode ∧ opcode < 192) ∨ ( 192 ≤ opcode ∧ opcode < 208) ∨ ( 208 ≤ opcode ∧ opcode < 224) ∨ ( 224 ≤ opcode ∧ opcode < 240) ∨ ( 240 ≤ opcode ∧ opcode < 256) := by omega
    rcases ranges with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
    · exact pureInstruction_eq_0 opcode h0.1 h0.2
    · exact pureInstruction_eq_1 opcode h1.1 h1.2
    · exact pureInstruction_eq_2 opcode h2.1 h2.2
    · exact pureInstruction_eq_3 opcode h3.1 h3.2
    · exact pureInstruction_eq_4 opcode h4.1 h4.2
    · exact pureInstruction_eq_5 opcode h5.1 h5.2
    · exact pureInstruction_eq_6 opcode h6.1 h6.2
    · exact pureInstruction_eq_7 opcode h7.1 h7.2
    · exact pureInstruction_eq_8 opcode h8.1 h8.2
    · exact pureInstruction_eq_9 opcode h9.1 h9.2
    · exact pureInstruction_eq_10 opcode h10.1 h10.2
    · exact pureInstruction_eq_11 opcode h11.1 h11.2
    · exact pureInstruction_eq_12 opcode h12.1 h12.2
    · exact pureInstruction_eq_13 opcode h13.1 h13.2
    · exact pureInstruction_eq_14 opcode h14.1 h14.2
    · exact pureInstruction_eq_15 opcode h15.1 h15.2

end Itasca.Body.Simd

end
