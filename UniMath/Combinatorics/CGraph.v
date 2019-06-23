(* ******************************************************************************* *)
(** * Correspondence graphs

    Marco Maggesi
    June 2019
 ********************************************************************************* *)

(*
We refer to graphs formalized in this file as "correspondence graphs"
(cgraphs for short).  A correspondence is a diagram

    N <--- A ---> N'

In our case A is the type of arcs and N = N' is the type of nodes and
the two arrows are interpreted as source an target of an arc.

This name is chosen to make a name distinction with the graphs
defined in CategoryTheory/Graph.v.

Also, to avoid any overlap of the terminology, here we use the words
"node" and "arc" instead of "vertex" and "edge".

When the type N and A of nodes and arcs are not assumed to be sets,
we use the name "correspondence pregraph", abbreviated "precgraph".
*)

Require Import UniMath.MoreFoundations.Propositions.

(** ** Precgraphs. *)

Definition precgraph : UU
  := ∑ (N : UU) (E : UU), (E → N) × (E → N).

Definition make_precgraph {N : UU} {E : UU} (s t : E → N)
  : precgraph
  := N,, E,, make_dirprod s t.

Definition node : precgraph → UU := pr1.

Definition arc (G : precgraph) : UU
  := pr12 G.

Definition src {G : precgraph}
  : arc G → node G
  := pr122 G.

Definition trg {G : precgraph}
  : arc G → node G
  := pr222 G.

Definition has_nodeset (G : precgraph) : UU
  := isaset (node G).

Definition isaprop_has_nodeset (G : precgraph)
  : isaprop (has_nodeset G)
  := isapropisaset (node G).

Definition has_arcset (G : precgraph) : UU
  := isaset (arc G).

Definition isaprop_has_arcsets (G : precgraph)
  : isaprop (has_arcset G)
  := isapropisaset (arc G).

(** Cgraphs. *)

Definition cgraph : UU
  := ∑ G : precgraph, isaset (node G) × isaset (arc G).

Definition make_cgraph
           (G : precgraph)
           (h : isaset (node G))
           (k : isaset (arc G))
  : cgraph
  := tpair _ G (make_dirprod h k).

Definition precgraph_of_cgraph : cgraph → precgraph := pr1.
Coercion precgraph_of_cgraph : cgraph >-> precgraph.

Definition isaset_node (G : cgraph)
  : isaset (node G)
  := pr12 G.

Definition isaset_arc (G : cgraph)
  : isaset (arc G)
  := pr22 G.

(** ** Cgraph morphisms. *)

Definition is_cgraph_mor {G H : precgraph}
           (p₀ : node G → node H)
           (p₁ : arc G → arc H)
  : UU
  := (∏ f : arc G, src (p₁ f) = p₀ (src f)) ×
     (∏ f : arc G, trg (p₁ f) = p₀ (trg f)).

Definition cgraph_mor (G H : precgraph) : UU
  := ∑ (p₀ : node G → node H)
       (p₁ : arc G → arc H),
     is_cgraph_mor p₀ p₁.

Definition make_cgraph_mor {G H : precgraph}
           (p₀ : node G → node H)
           (p₁ : arc G → arc H)
           (h : is_cgraph_mor p₀ p₁)
  : cgraph_mor G H
  := p₀,, p₁,, h.

Definition onnode {G H : precgraph}
  : cgraph_mor G H → node G → node H
  := pr1.

Definition onarc {G H : precgraph}
  : cgraph_mor G H → arc G → arc H
  := λ f, pr12 f.

Definition preserves_src {G H : precgraph}
           (p : cgraph_mor G H)
  : ∏ x : arc G, src (onarc p x) = onnode p (src x)
  := pr122 p.

Definition preserves_trg {G H : precgraph}
           (p : cgraph_mor G H)
  : ∏ f : arc G, trg (onarc p f) = onnode p (trg f)
  := pr222 p.

Lemma is_cgraph_mor_id (G : precgraph)
  : is_cgraph_mor (idfun (node G)) (idfun (arc G)).
Proof.
  apply make_dirprod; intros; apply idpath.
Defined.

Definition cgraph_mor_id (G : precgraph)
  : cgraph_mor G G
  := make_cgraph_mor (idfun (node G)) (idfun (arc G))
                    (is_cgraph_mor_id G).

Lemma is_cgraph_mor_comp {G H K : precgraph}
      (p : cgraph_mor G H)
      (q : cgraph_mor H K)
  : is_cgraph_mor (onnode q ∘ onnode p) (onarc q ∘ onarc p).
Proof.
  apply make_dirprod.
  - intros. unfold funcomp.
    etrans. apply (preserves_src q).
    apply maponpaths. apply (preserves_src p).
  - intros. unfold funcomp.
    etrans. apply (preserves_trg q).
    apply maponpaths. apply (preserves_trg p).
Defined.

Definition cgraph_mor_comp {G H K : precgraph}
           (p : cgraph_mor G H)
           (q : cgraph_mor H K)
  : cgraph_mor G K
  := make_cgraph_mor (onnode q ∘ onnode p) (onarc q ∘ onarc p)
                    (is_cgraph_mor_comp p q).

Lemma cgraph_mor_id_left {G H : precgraph} (p : cgraph_mor G H) :
  cgraph_mor_comp (cgraph_mor_id G) p = p.
Proof.
  induction p as (p₀,(p₁,h)).
  apply pair_path_in2.
  apply pair_path_in2.
  apply dirprod_paths.
  - apply funextsec. intro f. cbn.
    apply pathscomp0rid.
  - apply funextsec. intro f. cbn.
    apply pathscomp0rid.
Defined.

Lemma cgraph_mor_id_right {G H : precgraph} (p : cgraph_mor G H) :
  cgraph_mor_comp p (cgraph_mor_id H) = p.
Proof.
  induction p as (p₀,(p₁,h)).
  apply pair_path_in2.
  apply pair_path_in2.
  apply dirprod_paths.
  - apply funextsec. intro f. cbn.
    apply maponpathsidfun.
  - apply funextsec. intro f. cbn.
    apply maponpathsidfun.
Defined.

Lemma cgraph_mor_comp_assoc {G1 G2 G3 G4 : precgraph}
      (p : cgraph_mor G1 G2) (q : cgraph_mor G2 G3) (r : cgraph_mor G3 G4)
  : cgraph_mor_comp p (cgraph_mor_comp q r) =
    cgraph_mor_comp (cgraph_mor_comp p q) r.
Proof.
  induction p as (p₀,(p₁,h)).
  induction q as (q₀,(q₁,k)).
  induction r as (r₀,(r₁,l)).
  apply pair_path_in2.
  apply pair_path_in2.
  apply dirprod_paths; cbn.
  - apply funextsec. intro f.
    etrans. { apply pathsinv0, path_assoc. }
    apply maponpaths.
    apply pathsinv0.
    etrans. { apply maponpathscomp0. }
    apply maponpaths.
    apply maponpathscomp.
  - apply funextsec. intro f.
    etrans. { apply pathsinv0, path_assoc. }
    apply maponpaths.
    apply pathsinv0.
    etrans. { apply maponpathscomp0. }
    apply maponpaths.
    apply maponpathscomp.
Defined.

Lemma isaprop_is_cgraph_mor {G H : precgraph}
      (p₀ : node G → node H)
      (p₁ : arc G → arc H)
      (h : has_nodeset H)
  : isaprop (is_cgraph_mor p₀ p₁).
Proof.
  apply isapropdirprod; apply impred_isaprop; intro f; apply h.
Qed.

Lemma isaset_cgraph_mor {G H : precgraph}
      (h : has_nodeset H) (k : has_arcset H)
  : isaset (cgraph_mor G H).
Proof.
  apply isaset_total2.
  - exact (funspace_isaset h).
  - intro p₀.
    apply isaset_total2.
    + exact (funspace_isaset k).
    + intro p₁.
      apply isasetaprop.
      apply isaprop_is_cgraph_mor.
      exact h.
Qed.
