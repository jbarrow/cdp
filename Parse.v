Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Datatypes.
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

Definition start_symbol (g : list Rule) : option symbol :=
  match g with
  | h :: _ => Some (lhs h)
  | nil => None
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
  | h :: t => valid_rule h /\ valid_grammar t
  | nil => True
  end.

(*
 * Exercise: Prove the following lemma
 *
 *   If the Rule r is in the Grammar l, and l is valid (that is, 
 *   the left-hand side of every rule in l is a nonterminal), then 
 *   the left hand side of r is a nonterminal.
 *)
Lemma valid_item : forall (l : list Rule) (r : Rule),
    valid_grammar (r :: l) -> valid_rule r.
Proof. intros. induction l; inversion H; apply H0. Qed.

Lemma valid_composition : forall (l : list Rule) (r : Rule),
    valid_grammar (r :: l) -> valid_grammar l.
Proof. intros. induction l; inversion H; apply H1. Qed.       

Lemma valid : forall (l:list Rule) (r:Rule),
    In r l -> valid_grammar l -> valid_rule r.
Proof with eauto.
  intros. induction l; inversion H.
  - subst. apply valid_item in H0. apply H0.
  - apply valid_composition in H0. apply IHl...
Qed.

Inductive item : Type :=
  | I : nat -> symbol -> list symbol -> list symbol -> nat -> list Tree -> item.

Definition trees (i : item) : list Tree :=
  match i with
  | I _ _ _ _ _ t => t
  end.

Definition axioms (g : list Rule) : option item :=
  match start_symbol g with
  | Some s => Some (I 0 (D "S'") [] [s] 0 [])
  | None => None
  end.

Definition goal (g : list Rule) (s : list id) (i : item) : Prop :=
  match i with
  | I i symbol symbols symbols' k trees => i = 0 /\ dummy symbol /\ symbols' = []
  end.
                                                                                 