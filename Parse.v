
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive id : Type :=
  | Id : string -> id.

Inductive symbol : Type :=
  | N : id -> symbol
  | T : id -> symbol
  | D : id -> symbol.

Definition nonterminal (s : symbol) : bool :=
  match s with
  | T _ => false
  | _ => true
  end.

Definition terminal (s : symbol) : bool :=
  match s with
  | T _ => true
  | _ => false
  end.

Definition dummy (s : symbol) : bool :=
  match s with
  | D _ => true
  | _ => false
  end.

Inductive Rule : Type :=
  | R : symbol -> list symbol -> Rule.

Inductive Grammar : Type :=
  | G : list Rule -> Grammar.

(* S -> aSa | a *)
Definition simple_grammar : Grammar :=
  G (
      (R (N (Id "S")) (T (Id "a") :: N (Id "S") :: T (Id "a") ::  nil)) 
        :: (R (N (Id "S")) (T (Id "a") :: nil))
        :: nil
    ).

Check simple_grammar.

Definition lhs (r : Rule) : symbol :=
  match r with
  | R x _ => x
  end.

Definition rhs (r : Rule) : list symbol :=
  match r with
  | R _ ys => ys
  end.

Inductive Tree : Type :=
  | Leaf : symbol -> Tree
  | Node : symbol -> list Tree -> Tree.

Check Node (N (Id "S")) (Leaf (T (Id "a")) :: nil).