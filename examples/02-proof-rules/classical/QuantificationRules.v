Require Import Coq.Strings.String.
Require Import Classical.
Require Import turtle.tla.TLA.
Require Import turtle.examples.proofrules.QuantificationRules.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* Quantification                                                             *)
(* ========================================================================== *)

(* Not from refs *)
Lemma FF4 {V : Type} (x : string) (F G : property (State V)) :
    valid (F \impl \AA x : F) -> (* x not free in F *)
        valid ((\AA x : (F \lor G))
            \equiv (F \lor (\AA x : G))).
Proof.
(* TODO *) Admitted.
