
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
  negb (nonterminal s).

Definition dummy (s : symbol) : bool :=
  match s with
  | D _ => true
  | _ => false
  end.

Inductive Rule : Type :=
  | R : symbol -> list symbol -> Rule.

Inductive Grammar : Type :=
  | G : list Rule -> Grammar.

Notation "'N' a" := (N (Id a)) (at level 60).
Notation "'T' a" := (T (Id a)) (at level 60).
Notation "'D' a" := (D (Id a)) (at level 60).

Notation "a '-->' b" := (R a b) (at level 80).

Check N "s".

(* Starting with a simple grammar of { a^n | n % 2 == 1 }.
 * S -> aSa | a *)
Definition simple_grammar : list Rule :=
  [
    N "S" --> [T "a" ; N "S" ; T "a"] ;
      N "S" --> [T "a"]
  ].

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

(* This is the derivation tree for the smallest string in the
 * language `simple_grammar`, a. *)
Check Node (N "S") (Leaf (T "a") :: nil).

(* Exercise : check that the lhs of every rule in the grammar is a nonterminal symbol. *)
Fixpoint valid_grammar (g : list Rule) : bool :=
  match g with
  | h :: t => match (lhs h) with
                  | N _ => valid_grammar t
                  | _ => false
                  end
  | nil => true
  end.

Lemma valid : forall (l:list Rule) (r:Rule),
    In r l -> valid_grammar l = true -> nonterminal (lhs r) = true.
Proof.