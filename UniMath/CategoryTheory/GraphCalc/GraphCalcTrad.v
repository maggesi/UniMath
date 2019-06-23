Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Graph.
Require Import UniMath.Combinatorics.CGraph.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.CategoryTheory.categories.Graph.
Require Import UniMath.CategoryTheory.categories.CGraph.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Monads.RelativeMonads.
Require Import UniMath.CategoryTheory.Monads.RelativeModules.

Require Import UniMath.CategoryTheory.GraphCalc.GraphCalcAbs.
Require Import UniMath.CategoryTheory.GraphCalc.GraphCalcRel.

Local Open Scope cat.

Definition make_RelMonad_data
           {C D : precategory_data}
           (J : functor_data C D)
           (F : C → D)
           (u : ∏ c : C, D ⟦ J c, F c ⟧)
           (b : ∏ c d : C, D ⟦ J c, F d ⟧ → D ⟦ F c, F d ⟧)
  : RelMonad_data J
  := (F,, u,, b).

Definition make_RelMonad
           {C D : precategory_data}
           {J : functor_data C D}
  : ∏ R : RelMonad_data J, RelMonad_axioms R → RelMonad J
  := tpair _.

Definition make_RelModule_Mor
           {C D : precategory_data}
           {J : C ⟶ D}
           {R : RelMonad_data J}
           {M N : RelModule R}
  : ∏ (φ : ∏ a : C, M a --> N a), is_relmodule_mor M N φ → RelModule_Mor M N
  := tpair _.

Definition make_discrete_cgraph_mor
           {X : UU}
           {G : precgraph}
           (p : X → node G)
  : cgraph_mor (make_discrete_precgraph X) G.
Proof.
  use make_cgraph_mor; cbn.
  - exact p.
  - apply fromempty.
  - apply make_dirprod; cbn; exact fromemptysec.
Defined.

Section To_Calculus.

  Variable R : calculus'.

  Local Definition to_relmonad_data : RelMonad_data (functor_identity HSET).
  use make_RelMonad_data.
  - cbn. unfold calculus' in R.
    exact (λ X : hSet, nodeset(R X)).
  - cbn. unfold calculus' in R.
    exact (λ (X : hSet) (x : X), onnode (r_eta R X) x).
  - cbn. unfold calculus' in R.
    intros X Y f x.
    pose (ff := make_discrete_cgraph_mor f).
    exact (onnode (r_bind R ff) x).
  Defined.

  Lemma to_relmonad_axioms : RelMonad_axioms to_relmonad_data.
  Proof.
    repeat apply make_dirprod; cbn; unfold calculus' in R.
    - intro X.
      apply funextfun. intro x.
      change x with (onnode (identity (R X)) x) at 2.
      apply (maponpaths (λ f, onnode f x)).
      etrans.
      2: apply (r_bind_r_eta R X).
      apply (maponpaths (r_bind R)).
      unfold make_discrete_cgraph_mor.
      apply cgraph_mor_eq; cbn.
      + intro y. apply idpath.
      + exact fromemptysec.
    - intros X Y f.
      apply funextfun. intro x.
      change (onnode (r_eta R X · r_bind R (make_discrete_cgraph_mor f)) x =
              onnode (make_discrete_cgraph_mor f) x).
      apply (maponpaths (λ f, f x)).
      pose (H := r_eta_r_bind R X Y (make_discrete_cgraph_mor f)).
      apply (maponpaths onnode) in H.
      exact H.
    - intros X Y Z f g.
      apply funextfun. intro x.
      pose (H := r_bind_r_bind R X Y Z
                               (make_discrete_cgraph_mor f)
                               (make_discrete_cgraph_mor g)).
      apply (maponpaths (λ f, onnode f x)) in H.
      cbn in *.
      etrans.
      1: apply H.
      apply (maponpaths (λ f, onnode f x)).
      apply (maponpaths (r_bind R)).
      apply cgraph_mor_eq; cbn.
      + intro y. apply idpath.
      + exact fromemptysec.
  Qed.

  Local Definition to_relmonad : RelMonad (functor_identity HSET)
    := make_RelMonad to_relmonad_data to_relmonad_axioms.

  Local Definition Arc (X:hSet) : hSet := arcset ((R:RelMonad _) X).

  Local Definition to_bind {X Y : hSet}
        (p : X → nodeset ((R:RelMonad _) Y))
        (f : arcset ((R:RelMonad _) X))
    : arcset ((R:RelMonad _) Y)
    := (onarc (r_bind (R:RelMonad _) (make_discrete_cgraph_mor p)) f).

  Local Definition to_relmodule_data : RelModule_data to_relmonad_data
    := make_relmodule_data to_relmonad_data Arc (@to_bind).

  Local Lemma to_relmodule_laws : RelModule_laws to_relmodule_data.
  Proof.
    unfold calculus' in R.
    apply make_dirprod.
    { exact to_relmonad_axioms. }
    apply make_dirprod; cbn.
    - intro X.
      apply funextfun. intro f.
      unfold to_bind.
      pose (H := r_bind_r_eta R X).
      apply (maponpaths (λ p, onarc p f)) in H.
      etrans.
      2: exact H.
      apply (maponpaths (λ p, onarc p f)).
      apply (maponpaths (r_bind R)).
      apply cgraph_mor_eq; cbn.
      + intro x. apply idpath.
      + apply fromemptysec.
    - intros X Y Z p q.
      apply funextfun. intro f.
      unfold to_bind.
      pose (H := r_bind_r_bind R X Y Z
                               (make_discrete_cgraph_mor p)
                               (make_discrete_cgraph_mor q)).
      apply (maponpaths (λ p, onarc p f)) in H.
      etrans.
      1: exact H.
      apply (maponpaths (λ p, onarc p f)).
      apply (maponpaths (r_bind R)).
      apply cgraph_mor_eq; cbn.
      + intro x. apply idpath.
      + apply fromemptysec.
  Qed.

  Local Definition to_relmodule : RelModule to_relmonad
    := make_RelModule _ to_relmodule_data to_relmodule_laws.

  Local Definition to_src
    : RelModule_Mor to_relmodule (tautological_RelModule to_relmonad).
  Proof.
    unfold calculus' in R.
    use (make_RelModule_Mor); cbn.
    1: exact (λ X : hSet, @CGraph.src (R X:cgraph)).
    unfold is_relmodule_mor. cbn.
    intros X Y p.
    apply funextfun.
    exact (preserves_src (r_bind R (make_discrete_cgraph_mor p))).
  Defined.

  Local Definition to_trg
    : RelModule_Mor to_relmodule (tautological_RelModule to_relmonad).
  Proof.
    unfold calculus' in R.
    use (make_RelModule_Mor); cbn.
    1: exact (λ X : hSet, @CGraph.trg (R X:cgraph)).
    unfold is_relmodule_mor. cbn.
    intros X Y p.
    apply funextfun.
    exact (preserves_trg (r_bind R (make_discrete_cgraph_mor p))).
  Defined.

  Local Definition to_calcolus_on : calculus_on to_relmonad
    := make_calculus_on to_relmodule to_src to_trg.

  Definition to_calculus : calculus
    := make_calculus to_calcolus_on.

End To_Calculus.

Section From_Calculus.

  Variable R : calculus.

  Local Definition calculus_precgraph (X : hSet) : precgraph
    := make_precgraph (λ f : (redmod R) X : hSet, (src R) X f)
                      (λ f : (redmod R) X : hSet, (trg R) X f).

  Local Definition calculus_cgraph (X : hSet) : cgraph.
  Proof.
    apply (make_cgraph (calculus_precgraph X)).
    - apply setproperty.
    - apply setproperty.
  Defined.

  Local Definition calculus_map (X : hSet) : cgraph
    := make_cgraph (calculus_precgraph X)
                   (setproperty ((tautological_RelModule R) X))
                   (setproperty ((redmod R) X)).

  Local Definition calculus_eta (X : hSet)
    : cgraph_mor (make_discrete_precgraph X) (calculus_map X).
  Proof.
    use make_cgraph_mor; cbn.
    - apply (r_eta R).
    - apply fromempty.
    - apply make_dirprod; cbn; exact fromemptysec.
  Defined.

  Local Definition calculus_bind {X Y : hSet}
                   (p : cgraph_mor (make_discrete_precgraph X) (calculus_map Y))
    : cgraph_mor (calculus_map X) (calculus_map Y).
  Proof.
    use make_cgraph_mor; cbn.
    - exact (r_bind R (onnode p)).
    - apply (mbind (redmod R) (onnode p)).
    - apply make_dirprod; cbn.
      + intro f.
        pose (H := relmodule_mor_property (src R) X Y (onnode p)).
        apply (maponpaths (λ p, p f)) in H.
        cbn in H.
        exact H.
      + intro f.
        pose (H := relmodule_mor_property (trg R) X Y (onnode p)).
        apply (maponpaths (λ p, p f)) in H.
        cbn in H.
        exact H.
  Defined.

  Local Definition calculus_RelMonad_data
    : RelMonad_data make_discrete_cgraph_functor.
  Proof.
    use make_RelMonad_data; cbn.
    - exact calculus_map.
    - exact calculus_eta.
    - exact @calculus_bind.
  Defined.

  Axiom Joker : ∏ X : UU, X.

  Local Definition from_calculus
    : RelMonad make_discrete_cgraph_functor.
  Proof.
    use make_RelMonad; cbn.
    - exact calculus_RelMonad_data.
    - repeat apply make_dirprod; cbn.
      + intro X.
        apply (cgraph_mor_eq (calculus_bind (calculus_eta X))); cbn.
        * intro x. pose (H := r_bind_r_eta R X). cbn in H.
          apply (maponpaths (λ p, p x)) in H.
          exact H.
        * intro f. pose (H := mbind_r_eta (redmod R) X). cbn in H.
          apply (maponpaths (λ p, p f)) in H.
          exact H.
      + intros X Y p.
        apply (@cgraph_mor_eq (make_discrete_cgraph X) (calculus_cgraph Y)); cbn.
        * intro x.
          pose (H := r_eta_r_bind R X Y (onnode p)).
          apply (maponpaths (λ p, p x)) in H.
          cbn in H.
          apply H.
        * exact fromemptysec.
      + intros X Y Z p q.
        match goal with |- @paths ?A _ _ => pose (AA := A) end.
        apply (@cgraph_mor_eq (calculus_cgraph X) (calculus_cgraph Z)); cbn.
        * intro x.
          pose (H := r_bind_r_bind R X Y Z (onnode p) (onnode q)).
          apply (maponpaths (λ p, p x)) in H.
          exact H.
        * intro f.
          pose (H := mbind_mbind (redmod R) X Y Z (onnode p) (onnode q)).
          apply (maponpaths (λ p, p f)) in H.
          cbn in H.
          exact H.
  Defined.

End From_Calculus.
