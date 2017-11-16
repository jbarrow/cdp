
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Inductive NonTerminal : Type :=
  | S : NonTerminal.

Inductive Terminal : Type :=
  | a : Terminal
  | b : Terminal.      

Inductive Symbol : Type :=
  | N : NonTerminal -> Symbol
  | T : Terminal -> Symbol.

Inductive Rule : Type :=
  | R : NonTerminal -> list Symbol -> Rule.

Inductive Grammar : Type :=
  | G : list Rule -> Grammar.

(* S -> aSa | a *)
Definition simple_grammar : Grammar :=
  G ((R S (T a :: N S :: T a :: nil)) :: (R S (T a :: nil)) :: nil).

Check simple_grammar.

Definition lhs (r : Rule) : NonTerminal :=
  match r with
  | R x _ => x
  end.

Definition rhs (r : Rule) : list Symbol :=
  match r with
  | R _ ys => ys
  end.

Inductive Tree : Type :=
  | Leaf : Terminal -> Tree
  | Node : NonTerminal -> list Tree -> Tree.

Check Node S (Leaf a :: nil).