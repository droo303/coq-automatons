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


(* DFA -> Word -> Q1 -> Q2 *)
(* Definition move (Sigma: Alphabet)(auto: DFA Sigma)(w: Word Sigma)(Q: Set) : Q :=
auto.(dfa_trans) Q
.
*)

(* Moved DFA *)
(* Fixpoint move (Sigma: Alphabet)(auto: DFA Sigma)(w: Word Sigma) : DFA Sigma :=
match w with
| nil => auto
| h :: t => (createDFA Sigma auto.(dfa_states) auto.(dfa_trans) auto.(dfa_q0) -> auto.(dfa_trans) auto.(dfa_end))
end. *)

(* Fixpoint accepts_word {Sigma: Alphabet}(auto: DFA Sigma)(w: Word Sigma)(Q: Set) : Q :=
match w with
| nil => False 
| h::t => match dfa_end h with
            | bool  => True
            | false => accepts_word (auto, t, dfa_trans Q)
          end
end.
*)

(* DFA intersection *)
Definition aut_intersection (Sigma: Alphabet) (A1 A2: DFA Sigma) : DFA Sigma := 
createDFA Sigma 
(A1.(dfa_states) * A2.(dfa_states)) 
(A1.(dfa_trans) -> A2.(dfa_trans)) 
(A1.(dfa_end) A2.(dfa_end) .


Theorem aut_intersection : forall a1 DFA, a2: DFA.

Inductive DFA -> DFA -> Prop


(* 1:02 *)