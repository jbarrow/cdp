
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

Definition nonterminal (s : symbol) : Prop :=
  match s with
  | T _ => False
  | _ => True
  end.

Definition terminal (s : symbol) : Prop :=
  ~ (nonterminal s).

Definition dummy (s : symbol) : Prop :=
  match s with
  | D _ => True
  | _ => False
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

Definition valid_rule (r : Rule) : Prop :=
  nonterminal (lhs r).

Fixpoint valid_grammar (g : list Rule) : Prop :=
  match g with
  | h :: t => match valid_rule h with
              | True => valid_grammar t
              end
  | nil => True
  end.

(*
 * Exercise: Prove the following lemma
 *
 *   If the Rule r is in the Grammar l, and l is valid (that is, 
 *   the left-hand side of every rule in l is a nonterminal), then 
 *   the left hand side of r is a nonterminal.
 *)
Lemma valid_is_mappable : forall (l : list Rule) (r : Rule),
    valid_grammar (r :: l) -> valid_rule r.
Proof. intros.  Admitted.

Lemma valid_is_composable : forall (l : list Rule) (r : Rule),
    valid_grammar (r :: l) -> valid_grammar l.
Proof. intros. Admitted.
  
Lemma valid : forall (l:list Rule) (r:Rule),
    In r l -> valid_grammar l -> valid_rule r.
Proof with eauto.
  intros. generalize dependent r. 
Admitted.
    
Inductive item : Type := .