From automatons Require Export BaseDefinitions.

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
Let Q:= Automaton.(dfa_states Sigma).
Let delta:= Automaton.(dfa_trans Sigma).
Variable h t: Word Sigma.

Inductive trans: Q -> Word Sigma -> Q -> Prop :=
|t_a : forall q, trans q nil q
|t_b : forall q q' q'' h t, delta q h = q' -> trans q' t q'' -> trans q (h::t) q''
.



End Transition_Inductive.
