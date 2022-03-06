Module BaseDefinitions.

(* Alphabet is Set of characters *)
Definition Alphabet := Set.

(* Word is list of characters from Alphabet *)
Definition Word (Sigma : Alphabet) : Set := list Sigma.

(* Concatenation of words of alphabet *)
Definition ConcatWord (Sigma : Alphabet)(w1:Word Sigma)(w2: Word Sigma) : Word Sigma := 
  app w1 w2.

(* Language is  *)
Definition Language (Sigma : Alphabet):= Word Sigma -> Prop.

(* Intersection of languages *)
Definition LangIntersection (Sigma : Alphabet) (L1 L2:Language Sigma):=
  fun w: Word Sigma => L1 w /\ L2 w. 

Definition LangUnification (Sigma : Alphabet) (L1 L2: Language Sigma):=
  fun w: Word Sigma => L1 w \/ L2 w.  
 
End BaseDefinitions.

