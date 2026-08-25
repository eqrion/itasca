(** [itasca]: external functions.

    Hand-written, unlike its Itasca_ siblings. Aeneas emits
    Itasca_FunsExternal_Template.v naming the axioms it needs; this file
    supplies them, plus the definitions Aeneas expects to already exist
    (the [loop] combinator, [core_convert_From], the primitive [PartialEq]
    instances). Run [just externals-check] after re-extracting to see whether
    the two have drifted. Every axiom here is a trust item; see TRUST.md.
*)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Itasca_Types.
Include Itasca_Types.
Module Itasca_FunsExternal.

(** Trait declaration: [core::convert::From] *)
Record core_convert_From (Self T : Type) := mkcore_convert_From {
  from_ : T -> result Self;
}.
Arguments mkcore_convert_From { _ } { _ }.
Arguments from_ { _ } { _ } _.

(** [alloc::alloc::Global] *)
Axiom alloc_alloc_Global : Type.

(** [alloc::vec::Vec::with_capacity]: capacity is not observable in the
    logical list model, so this is the same empty vector as [Vec::new]. *)
Definition alloc_vec_Vec_with_capacity (T : Type) (_ : usize) : alloc_vec_Vec T :=
  alloc_vec_Vec_new T.

(** [alloc::vec::Vec::deref]: convert Vec to slice. *)
Axiom alloc_vec_Vec_deref : forall {T : Type}, alloc_vec_Vec T -> slice T.

(** Loop combinator for binary reader functions. *)
Inductive LoopControl (A B : Type) :=
  | Cont : A -> LoopControl A B
  | Done : B -> LoopControl A B.
Arguments Cont {_ _}.
Arguments Done {_ _}.
Axiom loop : forall {A B : Type},
  (A -> result (LoopControl A B)) -> A -> result B.

(** PartialEq instances for primitive types (not in Primitives.v). *)
Definition core_cmp_PartialEqU8 : core_cmp_PartialEq_t u8 u8 := {|
  core_cmp_PartialEq_t_eq := fun x y => Ok (x s= y);
  core_cmp_PartialEq_t_ne := fun x y => Ok (negb (x s= y));
|}.

Definition core_cmp_PartialEqU32 : core_cmp_PartialEq_t u32 u32 := {|
  core_cmp_PartialEq_t_eq := fun x y => Ok (x s= y);
  core_cmp_PartialEq_t_ne := fun x y => Ok (negb (x s= y));
|}.


(** [core::cmp::PartialEq::ne]:
    Source: '/rustc/library/core/src/cmp.rs', lines 264:4-264:37
    Name pattern: [core::cmp::PartialEq::ne] *)
Axiom core_cmp_PartialEq_ne_default :
  forall{Self : Type} {Rhs : Type} (partialEqInst : core_cmp_PartialEq_t Self
        Rhs),
        Self -> Rhs -> result bool
.

(** [core::cmp::impls::{core::cmp::PartialEq<&0 (B)> for &1 (A)}::eq]:
    Source: '/rustc/library/core/src/cmp.rs', lines 2089:8-2089:40
    Name pattern: [core::cmp::impls::{core::cmp::PartialEq<&'1 @A, &'0 @B>}::eq] *)
Axiom Shared1A_Insts_CoreCmpPartialEqShared0B_eq :
  forall{A : Type} {B : Type} (partialEqInst : core_cmp_PartialEq_t A B),
        A -> B -> result bool
.

(** [core::convert::{core::convert::From<T> for T}::from]:
    Source: '/rustc/library/core/src/convert/mod.rs', lines 788:4-788:22
    Name pattern: [core::convert::{core::convert::From<@T, @T>}::from] *)
Axiom core_convert_From_Blanket_from : forall{T : Type}, T -> result T.

(** [core::result::{core::ops::try_trait::Try<T, core::result::Result<core::convert::Infallible, E>> for core::result::Result<T, E>}::branch]:
    Source: '/rustc/library/core/src/result.rs', lines 2172:4-2172:64
    Name pattern: [core::result::{core::ops::try_trait::Try<core::result::Result<@T, @E>, @T, core::result::Result<core::convert::Infallible, @E>>}::branch] *)
Axiom core_result_Result_Insts_CoreOpsTry_traitTryTResultInfallibleE_branch :
  forall{T : Type} {E : Type},
        core_result_Result_t T E -> result (core_ops_control_flow_ControlFlow_t
          (core_result_Result_t core_convert_Infallible_t E) T)
.

(** [core::result::{core::ops::try_trait::FromResidual<core::result::Result<core::convert::Infallible, E>> for core::result::Result<T, F>}::from_residual]:
    Source: '/rustc/library/core/src/result.rs', lines 2187:4-2187:70
    Name pattern: [core::result::{core::ops::try_trait::FromResidual<core::result::Result<@T, @F>, core::result::Result<core::convert::Infallible, @E>>}::from_residual] *)
Axiom
  core_result_Result_Insts_CoreOpsTry_traitFromResidualResultInfallibleE_from_residual
  :
  forall(T : Type) {E : Type} {F : Type} (convertFromInst : core_convert_From F
        E),
        core_result_Result_t core_convert_Infallible_t E -> result
          (core_result_Result_t T F)
.

(** [alloc::vec::{alloc::vec::Vec<T>}::pop]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2651:4-2651:38
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::pop] *)
Axiom alloc_vec_Vec_pop :
  forall{T : Type} (A : Type),
        alloc_vec_Vec T -> result ((option T) * (alloc_vec_Vec T))
.

(** [alloc::vec::{alloc::vec::Vec<T>}::is_empty]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2878:4-2878:40
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::is_empty] *)
Axiom alloc_vec_Vec_is_empty :
  forall{T : Type} (A : Type), alloc_vec_Vec T -> result bool
.

(** [itasca::types::{core::cmp::PartialEq<itasca::types::ValueType> for itasca::types::ValueType}::ne]:
    Source: 'src/types.rs' *)
Axiom types_ValueType_Insts_CoreCmpPartialEqValueType_ne
  : types_ValueType_t -> types_ValueType_t -> result bool
.

(** [itasca::code::{core::cmp::PartialEq<itasca::code::BlockType> for itasca::code::BlockType}::ne]:
    Source: 'src/code.rs' *)
Axiom code_BlockType_Insts_CoreCmpPartialEqBlockType_ne
  : code_BlockType_t -> code_BlockType_t -> result bool
.

(** [itasca::types::{core::cmp::PartialEq<itasca::types::Mut> for itasca::types::Mut}::ne]:
    Source: 'src/types.rs' *)
Axiom types_Mut_Insts_CoreCmpPartialEqMut_ne
  : types_Mut_t -> types_Mut_t -> result bool
.

End Itasca_FunsExternal.
