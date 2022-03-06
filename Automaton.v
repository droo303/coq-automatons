From automatons Require Export BaseDefinitions.

Definition Automaton(Q:Set)(Sigma: Alphabet)(delta:Q->Sigma->Q)(Epsilon: Set)(q0: Q)(F: Q -> bool) : Type->Type :=  list.