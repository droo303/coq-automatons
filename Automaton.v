From automatons Require Export BaseDefinitions.

Require Import Notations.
Require Import Ltac.
Require Import Logic.

(* Q      - a finite set of states,
 * Sigma  - a finite set of input symbols 
 * delta  - a transition function
 * q0     - an initial state
 * F      - set of accept states
*)

(* Basic Automaton Prototype *)
Structure Automaton := createAuto { Q:Set;
                                Sigma: Alphabet;
                                delta: Q -> Sigma -> Q;
                                q0: Q;
                                F: Q -> bool}.

(* Parametrized Automaton *)
Structure DFA  (Sigma:Alphabet) : Type := createDFA { 
                                dfa_states: Set;
                                dfa_trans: dfa_states -> Sigma -> dfa_states;
                                dfa_q0: dfa_states;
                                dfa_end: dfa_states -> bool}.

(* Set up notattion for Alphabet (list) *)
Notation "x :: l" := (cons x l)(at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Define transition function *)
Section Transition.

Variable Sigma: Alphabet.
Variable Automaton: DFA Sigma.

(* Transition to state by word, q - starting state *)
Fixpoint Transition (q: Automaton.(dfa_states Sigma))(w: Word Sigma) : Automaton.(dfa_states Sigma) :=
match w with
| nil => q
| h::t => 
        let q':= Automaton.(dfa_trans Sigma) q h 
        in  Transition q' t
end.

End Transition.

(* Define Accepts word function *)
Section Accept.

Variable Sigma: Alphabet.
Variable Automaton: DFA Sigma.

Definition Accepts_word (w: Word Sigma) : bool :=
let q0 := dfa_q0 Sigma Automaton in
  let q' := Transition Sigma Automaton q0 w
  in Automaton.(dfa_end Sigma) q'.

End Accept.

Print Accepts_word.
(* Define Transition Inductively *)
Section Transition_Inductive.

Variable Sigma: Alphabet.
Variable Automaton: DFA Sigma.
Variable h t: Word Sigma.

Let Q:= Automaton.(dfa_states Sigma).
Let delta:= Automaton.(dfa_trans Sigma).

Inductive trans: Q -> Word Sigma -> Q -> Prop :=
|t_a : forall q, trans q nil q
|t_b : forall q q' q'' h t, delta q h = q' -> trans q' t q'' -> trans q (h::t) q''
.

End Transition_Inductive.


Section Union_Automaton.

Variable Sigma: Alphabet.
Variable Automaton_a: DFA Sigma.
Variable Automaton_b: DFA Sigma.

Let Q_a := Automaton_a.(dfa_states Sigma).
Let Q_b := Automaton_b.(dfa_states Sigma).
Let Q := pair Q_a Q_b.

Let delta_a := Automaton_a.(dfa_trans Sigma). 
Let delta_b := Automaton_b.(dfa_trans Sigma).

(* Let delta := delta_a (fst Q) -> delta_b (snd Q) -> Q. *)

Let q0_a := Automaton_a.(dfa_q0 Sigma).
Let q0_b := Automaton_b.(dfa_q0 Sigma).
Let q0 := pair q0_a q0_b.

Let qend_a := Automaton_a.(dfa_end Sigma).
Let qend_b := Automaton_b.(dfa_end Sigma).
(* Let qend := qend_a (fst Q) \/ qend_b (snd Q). *)

(* Definition Union_auto (a: Automaton)(b: Automaton) : Automaton :=
  createDFA Q delta q0 qend. *)

End Union_Automaton.


Section Intersection_Automaton.

Variable Sigma: Alphabet.
Variable Automaton_a: DFA Sigma.
Variable Automaton_b: DFA Sigma.

Let Q_a := Automaton_a.(dfa_states Sigma).
Let Q_b := Automaton_b.(dfa_states Sigma).
Let Q := pair Q_a Q_b.

Let delta_a := Automaton_a.(dfa_trans Sigma). 
Let delta_b := Automaton_b.(dfa_trans Sigma).

(* Let delta := delta_a (fst Q) -> delta_b (snd Q) -> Q. *)

Let q0_a := Automaton_a.(dfa_q0 Sigma).
Let q0_b := Automaton_b.(dfa_q0 Sigma).
Let q0 := pair q0_a q0_b.

Let qend_a := Automaton_a.(dfa_end Sigma).
Let qend_b := Automaton_b.(dfa_end Sigma).

(* Let qend := qend_a (fst Q) /\ qend_b (snd Q). *)

(* Definition Intersection_auto (a: Automaton)(b: Automaton) : Automaton :=
  createDFA Q delta q0 qend.
 *)
End Intersection_Automaton.


Section Concatenation_Automaton.

Variable Sigma: Alphabet.
Variable Automaton_a: DFA Sigma.
Variable Automaton_b: DFA Sigma.

Let Q_a := Automaton_a.(dfa_states Sigma).
Let Q_b := Automaton_b.(dfa_states Sigma).
Let Q := Q_a + Q_b.

Variable delta : Q -> Sigma -> Q. 

Let q0_a := Automaton_a.(dfa_q0 Sigma).
Let qend_b := Automaton_b.(dfa_end Sigma).

Check createDFA.

(* Definition Concatenation_auto : DFA Sigma :=
  createDFA Sigma Q delta q0_a qend_b. *)

End Concatenation_Automaton.