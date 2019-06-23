(* ========================================================================= *)
(** * Graph calculi implemented with absulute (non relative) monads.         *)
(* ========================================================================= *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.CategoryTheory.Monads.RelativeMonads.
Require Import UniMath.CategoryTheory.Monads.RelativeModules.

Local Open Scope cat.

Section Graph_Calculus.

  (** ** Structure of graph calculus on a monad *)

  Definition calculus_on (R : RelMonad (functor_identity HSET) : UU)
    := ∑ (Red : RelModule R),
       RelModule_Mor Red (tautological_RelModule R) ×
       RelModule_Mor Red (tautological_RelModule R).

  Definition make_calculus_on
             {R : RelMonad (functor_identity HSET)}
             (Red :RelModule R)
             (src : RelModule_Mor Red (tautological_RelModule R))
             (trg : RelModule_Mor Red (tautological_RelModule R))
    : calculus_on R
    := Red,, src,, trg.

  Definition redmod {R : RelMonad (functor_identity HSET)}
    : calculus_on R → RelModule R
    := pr1.

  Definition src {R : RelMonad (functor_identity HSET)} (calc : calculus_on R)
    : RelModule_Mor (redmod calc) (tautological_RelModule R)
    := pr12 calc.

  Definition trg {R : RelMonad (functor_identity HSET)} (calc : calculus_on R)
    : RelModule_Mor (redmod calc) (tautological_RelModule R)
    := pr22 calc.

  (** ** Graphic calculi *)

  Definition calculus : UU
    := ∑ R : RelMonad (functor_identity HSET), calculus_on R.

  Definition make_calculus {R : RelMonad (functor_identity HSET)}
    : calculus_on R → calculus
    := tpair _ R.

  Definition monad_of_calculus
    : calculus → RelMonad (functor_identity HSET)
    := pr1.
  Coercion monad_of_calculus : calculus >-> RelMonad.

  Definition get_calculus_on : ∏ calc : calculus, calculus_on calc := pr2.
  Coercion get_calculus_on : calculus >-> calculus_on.

End Graph_Calculus.
