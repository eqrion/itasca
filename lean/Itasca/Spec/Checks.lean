import «wasm2.0»

/-!
Sections, each formerly its own module: DeclaredReferences, Checks.
-/

/-! ## DeclaredReferences -/

section

/-!
# Declared function references

The pinned SpecTec model omits the `C.refs` condition of `ref.func`. This file supplies it
following Core 2.0 section 3.4.10: `declarations m` lists the function indices occurring in `m`
with its functions and start declaration removed, and `Module m` requires every `ref.func` in a
function body to be declared. Lists stand for sets, so order and duplicates do not matter.
Collection includes `call` as well as `ref.func`, since `funcidx` covers all syntactic function
index occurrences; the definitions do not assume the expressions are well typed.
-/

namespace Itasca.DeclaredReferences

mutual
  /-- Function-index occurrences in an instruction tree. With `calls = false`,
  collect only the occurrences whose typing requires a reference declaration. -/
  def instructionIndices (calls : Bool) : instr → List funcidx
    | .CALL x => if calls then [x] else []
    | .REF_FUNC x => [x]
    | .BLOCK _ body | .LOOP _ body => instructionsIndices calls body
    | .IFELSE _ yes no => instructionsIndices calls yes ++ instructionsIndices calls no
    | _ => []

  /-- Function-index occurrences in a sequence, including nested control bodies. -/
  def instructionsIndices (calls : Bool) : List instr → List funcidx
    | [] => []
    | op :: ops => instructionIndices calls op ++ instructionsIndices calls ops
end

@[simp] theorem instructionsIndices_nil (calls : Bool) :
    instructionsIndices calls [] = [] := rfl

@[simp] theorem instructionsIndices_cons (calls : Bool) (op : instr) (ops : List instr) :
    instructionsIndices calls (op :: ops) =
      instructionIndices calls op ++ instructionsIndices calls ops := rfl

@[simp] theorem instructionsIndices_append (calls : Bool) (xs ys : List instr) :
    instructionsIndices calls (xs ++ ys) =
      instructionsIndices calls xs ++ instructionsIndices calls ys := by
  induction xs with
  | nil => rfl
  | cons op ops ih => simp [ih, List.append_assoc]

/-- All `ref.func` occurrences in one instruction have declarations in `refs`. -/
def Instruction (refs : List funcidx) (op : instr) : Prop :=
  ∀ x ∈ instructionIndices false op, x ∈ refs

/-- All `ref.func` occurrences in a sequence have declarations in `refs`. -/
def Instructions (refs : List funcidx) (ops : List instr) : Prop :=
  ∀ x ∈ instructionsIndices false ops, x ∈ refs

@[simp] theorem Instruction.ref_func_iff {refs x} :
    Instruction refs (.REF_FUNC x) ↔ x ∈ refs := by
  simp [Instruction, instructionIndices]

@[simp] theorem Instruction.call (refs : List funcidx) (x : funcidx) :
    Instruction refs (.CALL x) := by
  simp [Instruction, instructionIndices]

@[simp] theorem Instruction.block_iff {refs bt ops} :
    Instruction refs (.BLOCK bt ops) ↔ Instructions refs ops := Iff.rfl

@[simp] theorem Instruction.loop_iff {refs bt ops} :
    Instruction refs (.LOOP bt ops) ↔ Instructions refs ops := Iff.rfl

@[simp] theorem Instruction.ifElse_iff {refs bt yes no} :
    Instruction refs (.IFELSE bt yes no) ↔ Instructions refs yes ∧ Instructions refs no := by
  simp only [Instruction, instructionIndices, List.mem_append, or_imp, forall_and,
    Instructions]

@[simp] theorem Instructions.nil (refs : List funcidx) : Instructions refs [] := by
  simp [Instructions]

@[simp] theorem Instructions.cons_iff {refs op ops} :
    Instructions refs (op :: ops) ↔ Instruction refs op ∧ Instructions refs ops := by
  simp only [Instructions, instructionsIndices_cons, List.mem_append, or_imp,
    forall_and, Instruction]

@[simp] theorem Instructions.append_iff {refs xs ys} :
    Instructions refs (xs ++ ys) ↔ Instructions refs xs ∧ Instructions refs ys := by
  simp only [Instructions, instructionsIndices_append, List.mem_append, or_imp, forall_and]

/-- Declared-reference conditions are monotone in `refs`. -/
theorem Instructions.mono {refs refs' ops}
    (hsub : ∀ x ∈ refs, x ∈ refs') (h : Instructions refs ops) : Instructions refs' ops :=
  fun x hx => hsub x (h x hx)

/-- Function indices occurring in a global initializer. -/
def globalIndices : global → List funcidx
  | .GLOBAL _ body => instructionsIndices true body

/-- Function indices occurring in an active element's offset expression. -/
def elementModeIndices : elemmode → List funcidx
  | .ACTIVE _ offset => instructionsIndices true offset
  | .PASSIVE | .DECLARE => []

/-- Function indices in an element segment's initializers and mode. -/
def elementIndices : elem → List funcidx
  | .ELEM _ initializers mode =>
    initializers.flatMap (instructionsIndices true) ++ elementModeIndices mode

/-- Function indices in an active data segment's offset expression. -/
def dataIndices : data → List funcidx
  | .DATA _ (.ACTIVE _ offset) => instructionsIndices true offset
  | .DATA _ .PASSIVE => []

/-- The function index of an exported function; other exports contribute none. -/
def exportIndices : «export» → List funcidx
  | .EXPORT _ (.FUNC x) => [x]
  | _ => []

/-- The declared references of a module: Core 2.0's `funcidx(module with funcs = [] with start =
none)`. Types, imports, tables and memories contain no function indices in Core 2.0. -/
def declarations : _root_.module → List funcidx
  | .MODULE _ _ _ globals _ _ elements datas _ exports =>
    globals.flatMap globalIndices ++ elements.flatMap elementIndices ++
      datas.flatMap dataIndices ++ exports.flatMap exportIndices

/-- The declared-reference obligation on one function's complete instruction tree. -/
def Function (refs : List funcidx) : func → Prop
  | .FUNC _ _ body => Instructions refs body

/-- The reference-declaration condition missing from the generated specification. Occurrences
outside function bodies already belong to `declarations`, so only function bodies need a
membership check. The start index is neither a declaration nor a use of `ref.func`. -/
def Module (m : _root_.module) : Prop :=
  match m with
  | .MODULE _ _ funcs _ _ _ _ _ _ _ =>
    ∀ f ∈ funcs, Function (declarations m) f

theorem Function.mono {refs refs' f}
    (hsub : ∀ x ∈ refs, x ∈ refs') (h : Function refs f) : Function refs' f := by
  cases f
  exact Instructions.mono hsub h

@[simp] theorem declarations_functions_start
    (ts is fs gs tables ms es ds start exports fs' start') :
    declarations (.MODULE ts is fs gs tables ms es ds start exports) =
      declarations (.MODULE ts is fs' gs tables ms es ds start' exports) := rfl

end Itasca.DeclaredReferences

end

/-! ## Checks -/

section

/-!
# Sanity checks of the generated specification

Small theorems that check the generated `wasm2.0.lean` is usable and covers the intended cases:
mutable and immutable globals, a nonempty `Instr_ok` instance, UTF-8 witnesses for four-byte
scalars, and import projections that must not drop an import of the projected kind.
-/

namespace Itasca.SpecChecks

/-- Mutable globals satisfy `Globaltype_ok`. -/
theorem mutable_global_supported (t : valtype) :
    Globaltype_ok (globaltype.mk_globaltype (some r_MUT.MUT) t) :=
  .mk_Globaltype_ok _ t

/-- Immutable globals satisfy `Globaltype_ok`. -/
theorem immutable_global_supported (t : valtype) :
    Globaltype_ok (globaltype.mk_globaltype none t) :=
  .mk_Globaltype_ok _ t

/-- `nop` is typed, so `Instr_ok` has inhabited instances. -/
theorem nop_typed (C : context) (hC : wf_context C) :
    Instr_ok C instr.NOP (functype.mk_functype (.mk_list []) (.mk_list [])) := by
  apply Instr_ok.nop C hC
  constructor

/-- The four-byte UTF-8 rule covers the first four-byte scalar value, U+10000. -/
theorem utf8_first_four_byte :
    fun_utf8 [.mk_char 0x10000]
      [.mk_byte 0xF0, .mk_byte 0x90, .mk_byte 0x80, .mk_byte 0x80] := by
  apply fun_utf8.fun_utf8_case_3
  · decide
  all_goals constructor; decide

/-- The four-byte UTF-8 rule covers U+1F600. -/
theorem utf8_emoji :
    fun_utf8 [.mk_char 0x1F600]
      [.mk_byte 0xF0, .mk_byte 0x9F, .mk_byte 0x98, .mk_byte 0x80] := by
  apply fun_utf8.fun_utf8_case_3
  · decide
  all_goals constructor; decide

/-- The four-byte UTF-8 rule covers the last scalar value, U+10FFFF. -/
theorem utf8_last_scalar :
    fun_utf8 [.mk_char 0x10FFFF]
      [.mk_byte 0xF4, .mk_byte 0x8F, .mk_byte 0xBF, .mk_byte 0xBF] := by
  apply fun_utf8.fun_utf8_case_3
  · decide
  all_goals constructor; decide

/-- A name containing a four-byte scalar value is well-formed. -/
theorem emoji_name_well_formed : wf_name (.mk_name [.mk_char 0x1F600]) := by
  apply wf_name.name_case_0 _ _ utf8_emoji
  · intro c hc
    have : c = .mk_char 0x1F600 := List.mem_singleton.mp hc
    subst c
    constructor
    decide
  · decide

/-- The `funcs` import projection does not discard a function import. -/
theorem function_import_not_discarded (ft : functype) :
    ¬ fun_funcsxt [.FUNC ft] [] := by
  intro h
  cases h

/-- The `globals` import projection does not discard a global import. -/
theorem global_import_not_discarded (gt : globaltype) :
    ¬ fun_globalsxt [.GLOBAL gt] [] := by
  intro h
  cases h

/-- The `tables` import projection does not discard a table import. -/
theorem table_import_not_discarded (tt : tabletype) :
    ¬ fun_tablesxt [.TABLE tt] [] := by
  intro h
  cases h

/-- The `mems` import projection does not discard a memory import. -/
theorem memory_import_not_discarded (mt : memtype) :
    ¬ fun_memsxt [.MEM mt] [] := by
  intro h
  cases h

#print axioms mutable_global_supported
#print axioms immutable_global_supported
#print axioms nop_typed

end Itasca.SpecChecks

end
