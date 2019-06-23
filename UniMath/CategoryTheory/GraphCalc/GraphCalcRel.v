(* ========================================================================= *)
(** * Grap calculi implemented with absulute (non relative) monads.          *)
(* ========================================================================= *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Graph.
Require Import UniMath.Combinatorics.CGraph.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.CategoryTheory.categories.Graph.
Require Import UniMath.CategoryTheory.categories.CGraph.

Require Import UniMath.CategoryTheory.Monads.RelativeMonads.

(** ** Miscellanea *)

Definition emptyset : hSet
  := make_hSet ∅ isasetempty.

(** ** Embedding of Set into Graph *)

(** Functor that send a set to the discrete graph on that set. *)

Local Open Scope cat.

Definition make_discrete_precgraph (X : UU) : precgraph
  := make_precgraph (N := X) fromempty fromempty.

Definition make_discrete_cgraph (X : hSet) : cgraph
  :=  make_cgraph (make_discrete_precgraph X)
                  (setproperty X)
                  isasetempty.

Definition has_nodeset_make_discrete_precgraph
  : ∏ X : hSet, has_nodeset (make_discrete_precgraph X)
  := setproperty.

Definition is_discrete_cgraph_mor {X Y : hSet} (f : X → Y)
  : @is_cgraph_mor (make_discrete_precgraph X)
                   (make_discrete_precgraph Y)
                   f
                   (idfun ∅)
  := make_dirprod fromemptysec fromemptysec.

Definition make_discrete_cgraph_mor {X Y : hSet} (f : X → Y)
  : cgraph_mor (make_discrete_precgraph X) (make_discrete_precgraph Y)
  := @make_cgraph_mor
       (make_discrete_precgraph X)
       (make_discrete_precgraph Y)
       f (idfun ∅) (is_discrete_cgraph_mor f).

Definition make_discrete_cgraph_functor_data
  : functor_data hset_precategory_ob_mor cgraph_precategory_ob_mor
  := @make_functor_data HSET cgraph_category
       make_discrete_cgraph
       (@make_discrete_cgraph_mor).

Lemma is_functor_make_discrete_cgraph
  : @is_functor HSET cgraph_category make_discrete_cgraph_functor_data.
Proof.
  apply make_dirprod.
  - intro x. cbn.
    apply pair_path_in2. cbn.
    apply pair_path_in2.
    apply pathsdirprod.
    apply funextsec; exact fromemptysec.
    apply funextsec; exact fromemptysec.
  - intros x y z. cbn.
    intros f g.
    apply cgraph_mor_eq_aux; cbn.
    + apply idpath.
    + apply idpath.
    + apply setproperty.
Qed.

Definition make_discrete_cgraph_functor
  : HSET ⟶ cgraph_category
  := @make_functor HSET cgraph_category
       make_discrete_cgraph_functor_data
       is_functor_make_discrete_cgraph.

Definition calculus' : UU
  := RelMonad make_discrete_cgraph_functor.
