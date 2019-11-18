Require Import PropLang.
Require Import List.

Require Import Coq.Lists.List.
Import ListNotations.

Section SequentCalculus.

Context {atom : Type}.

Reserved Notation "Γ1 ---> Γ2" (no associativity, at level 62).

Inductive G : list (prop atom) -> list (prop atom) -> Prop :=
| leave_everything {Γ1 Γ2 Γ3 Γ4 X} :
  [X] ---> [X] ->
  Γ1 ++ [X] ++ Γ2 ---> Γ3 ++ [X] ++ Γ4
| switch_arrow {Γ1 Γ2 Γ3 Γ4 X Y} :
  Γ1 ++[Y] ++ Γ2 ++ [X] ++ Γ3 ---> Γ4 ->
  Γ1 ++ [X] ++ Γ2 ++ [Y] ++ Γ3 ---> Γ4
| arrow_switch {Γ1 Γ2 Γ3 Γ4 X Y} :
  Γ1 ---> Γ2 ++ [Y] ++ Γ3 ++ [X] ++ Γ4 ->
  Γ1 ---> Γ2 ++ [X] ++ Γ3 ++ [Y] ++ Γ4
| axioma {X} : [X] ---> [X]
| arrow_impl {Γ1 Γ2 X Y} :
  [X] ++ Γ1 ---> [Y] ++ Γ2 ->
  Γ1 ---> [X ⊃ Y] ++ Γ2
| arrow_conj {Γ1 Γ2 X Y} :
  Γ1 ---> [X] ++ Γ2 ->
  Γ1 ---> [Y] ++ Γ2 ->
  Γ1 ---> [X ∧ Y] ++ Γ2
| arrow_disj {Γ1 Γ2 X Y} :
  Γ1 ---> [X] ++ [Y] ++ Γ2 ->
  Γ1 ---> [X ∨ Y] ++ Γ2
| arrow_neg {Γ1 Γ2 X} :
  [X] ++ Γ1 ---> Γ2 ->
  Γ1 ---> [¬ X] ++ Γ2
| impl_arrow {Γ1 Γ2 X Y} :
  Γ1 ---> [X] ++ Γ2 ->
  [Y] ++ Γ1 ---> Γ2 ->
  [X ⊃ Y] ++ Γ1 ---> Γ2
| conj_arrow {Γ1 Γ2 X Y} :
  [X] ++ [Y] ++ Γ1 ---> Γ2 ->
  [X ∧ Y] ++ Γ1 ---> Γ2
| disj_arrow {Γ1 Γ2 X Y} :
  [X] ++ Γ1 ---> Γ2 ->
  [Y] ++ Γ1 ---> Γ2 ->
  [X ∨ Y] ++ Γ1 ---> Γ2
| neg_arrow {Γ1 Γ2 X} :
  Γ1 ---> [X] ++ Γ2 ->
  [¬ X] ++ Γ1 ---> Γ2
where "Γ1 ---> Γ2" := (G Γ1 Γ2).

Theorem addNilInSeq_L (Γ1: list (prop atom)) (Γ2 : list (prop atom)) :
  nil ++ Γ1 ---> Γ2 = Γ1 ---> Γ2.
Proof.
  rewrite app_nil_l.
  reflexivity.
Qed.

Theorem addNilInSeq_R (Γ1 : list (prop atom)) (Γ2 : list (prop atom)) :
  Γ1 ---> nil ++ Γ2 = Γ1 ---> Γ2.
Proof.
  rewrite app_nil_l.
  reflexivity.
Qed.

Example example1 {A B C} :
  [A] ++ [B] ++ [¬C] ---> [¬C] ++ [¬A] ++ [A ∧ B].
Proof.
  apply @arrow_neg with (X := C).
  rewrite <- addNilInSeq_L.
  apply @switch_arrow with (X := C) (Y := ¬C) (Γ1 := []) (Γ2 := [A]++[B]) (Γ3 := []).
  apply @neg_arrow with (X := C).
  rewrite <- addNilInSeq_R.
  apply @leave_everything with (X := C).
  apply @axioma.
Qed.

Example example2 {A B C} :
  [A] ++ [B] ++ [¬C] ---> [¬C] ++ [¬A] ++ [A ∧ B].
Proof.
  rewrite <- addNilInSeq_R.
  apply @arrow_switch with (X := ¬C) (Y := A ∧ B).
  apply @arrow_conj with (X := A) (Y := B).
  + rewrite <- addNilInSeq_R.
    rewrite <- addNilInSeq_L.
    apply @leave_everything with (X := A).
    apply @axioma.
  + rewrite <- addNilInSeq_R.
    rewrite <- addNilInSeq_L.
    apply @leave_everything with (X := B).
    apply @axioma.
Qed.

(*\subset- implikálás*)
Example example3 {A B}:
  [¬(A ⊃ B)] ---> [¬A ∨ ¬B].
Proof.
  apply @neg_arrow with(X:= A ⊃ B).
  apply @arrow_impl with (X := A) (Y:= B).
  rewrite <- addNilInSeq_R.
  apply @arrow_switch with (X := B) (Y:= ¬A ∨ ¬B).

Example example4 {A B C} :
  [(A ∨ B) ⊃ C] ---> [(A ⊃ C) ∧ (B ⊃ C)].

Example example5 {A B} :
  [¬(A ⊃ B)] ---> [¬A ∨ ¬B].
 
(*\lnot!!*)
Example nyomozos {F K A} :
  [F ⊃ K] ++ [K ⊃ A] ++ [¬A] ---> [¬F].

  