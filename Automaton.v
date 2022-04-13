From automatons Require Export BaseDefinitions.

Require Import Notations.
Require Import Ltac.
Require Import Logic.
Require Import Bool.

(* Set up notattion for Alphabet (list) *)
Notation "x :: l" := (cons x l)(at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Q      - a finite set of states,
 * Sigma  - a finite set of input symbols 
 * delta  - a transition function
 * q0     - an initial state
 * F      - set of accept states
*)

(* Deterministic Finite Automaton *)
Structure DFA  (Sigma:Alphabet) : Type := createDFA { 
                                Q:      Set;
                                delta:  Q -> Sigma -> Q;
                                q0:     Q;
                                F:      Q -> bool
}.

(* Define transition function *)
Section Transition.
Variable Sigma: Alphabet.
Variable Automaton: DFA Sigma.
(* Q -> Word -> Q *)
Fixpoint Transition (q: Q Sigma Automaton)(w: Word Sigma) : Q Sigma Automaton :=
match w with
| nil => q
| h::t => 
        let q':= delta Sigma Automaton q h 
        in  Transition q' t
end.

(* Inductive proposition *)
Let Q:= Q Sigma Automaton.
Let delta:= delta Sigma Automaton.
Variable h t: Word Sigma.
Inductive transition: Q -> Word Sigma -> Q -> Prop :=
|trans_empty: forall q, transition q nil q
|trans_ind : forall q q' q'' h t, delta q h = q' -> transition q' t q'' -> transition q (h::t) q''
.

Lemma transition_nil: forall q1 q2, transition q1 nil q2 <-> q1 = q2.
Proof.
  intros. split.
  - intros. inversion H. reflexivity.
  - intros. inversion H. apply trans_empty.
Qed.

Lemma transition_intermediate: forall q1 h t q2, 
      transition q1 (h::t) q2 <-> exists q3, delta q1 h = q3 /\ transition q3 t q2.
Proof.
 intros. split.
  - intros. inversion H. 
    + rewrite H3. exists q'. split. 
      * reflexivity.
      * apply H5.
  -
Admitted. 
End Transition.

(* Define Accepts word function *)
Section Accept.
Variable Sigma: Alphabet.
Variable Automaton: DFA Sigma.
Variable word: Word Sigma.
Let q0 := q0 Sigma Automaton.
Let q' := Transition Sigma Automaton q0 word.

Definition Accepts_word : bool :=
  F Sigma Automaton q'.
End Accept.


Section Automaton_Operations.
Variable Sigma: Alphabet.
Variable Automaton_a: DFA Sigma.
Variable Automaton_b: DFA Sigma.

Let Q_a := Q Sigma Automaton_a.
Let Q_b := Q Sigma Automaton_b.
Let Q := Q_a * Q_b.

Let delta_a := delta Sigma Automaton_a. 
Let delta_b := delta Sigma Automaton_b.

Let q0_a := q0 Sigma Automaton_a.
Let q0_b := q0 Sigma Automaton_b.
Let q0 := pair q0_a q0_b.

Let qend_a := F Sigma Automaton_a.
Let qend_b := F Sigma Automaton_b.

Definition delta_union (q: Q)(a: Sigma) : Q :=
  let (q1, q2) := q in
  let q1':= delta_a q1 a in
  let q2':= delta_b q2 a in
    pair q1' q2'.

Definition qend_union (q: Q) : bool := 
  let (q1, q2) := q in
  orb (qend_a q1)(qend_b q2).

Definition qend_intersection (q: Q) : bool := 
  let (q1, q2) := q in
  andb (qend_a q1)(qend_b q2).

Definition Union_automata: DFA Sigma :=
  createDFA Sigma Q delta_union q0 qend_union.

Definition Intersection_automata (a: DFA Sigma)(b: DFA Sigma) : DFA Sigma :=
  createDFA Sigma Q delta_union q0 qend_intersection.

(* Add concatenation *)

(* Add complement *)

End Automaton_Operations.

(* TODO Proof for acceptance of words for both Automatons when accepted in Union_auto *)
Section proof.

Lemma Union_trans : forall Sigma (Automaton_a Automaton_b : DFA Sigma), 
                  let automaton_union := Union_automata Sigma Automaton_a Automaton_b in
                  let Q1 := Q Sigma Automaton_a in
                  let Q2 := Q Sigma Automaton_b in
                  forall (w: Word Sigma)(q1 q1': Q1)(q2 q2': Q2),
                    transition Sigma automaton_union (pair q1 q2) w (pair q1' q2') <-> (transition Sigma Automaton_a q1 w q1' /\ transition Sigma Automaton_b q2 w q2').

Proof.
  intros Sigma Automaton_a Automaton_b automaton_union Q1 Q2.
  induction w.
    - intros. split. 
      + intros. apply transition_nil in H. inversion H. split.
        apply trans_empty. apply trans_empty. 
      + intros. destruct H as [H1 H2]. apply transition_nil in H1. apply transition_nil in H2. rewrite H1. rewrite H2.
      apply trans_empty. 
    - intros. split.
      + intros H. apply transition_intermediate in H.
Admitted.