Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive id : Type :=
  | Id : string -> id.

Inductive symbol : Type :=
  | Nonterminal : id -> symbol
  | Terminal : id -> symbol
  | Dummy : id -> symbol.

Definition nonterminal (s : symbol) : Prop :=
  match s with
  | Terminal _ => False
  | _ => True
  end.

Definition terminal (s : symbol) : Prop :=
  ~ (nonterminal s).

Definition dummy (s : symbol) : Prop :=
  match s with
  | Dummy _ => True
  | _ => False
  end.

Inductive Rule : Type :=
  | R : symbol -> list symbol -> Rule.

Inductive Grammar : Type :=
  | G : list Rule -> Grammar.

Notation "'N' a" := (Nonterminal (Id a)) (at level 60).
Notation "'T' a" := (Terminal (Id a)) (at level 60).
Notation "'D' a" := (Dummy (Id a)) (at level 60).

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

Definition beq_symbol (s1 s2 : symbol) : bool :=
  match s1 with
  | N x => match s2 with
           | N y => if string_dec x y then true else false
           | _ => false
           end
  | T x => match s2 with
           | T y => if string_dec x y then true else false
           | _ => false
           end
  | D _ => match s2 with
           | D _ => true
           | _ => false
           end
  end.

Definition start_symbol (g : list Rule) : option symbol :=
  match g with
  | h :: _ => Some (lhs h)
  | nil => None
  end.

Definition valid_rule (r : Rule) : Prop :=
  nonterminal (lhs r) /\ ~ dummy (lhs r).

Fixpoint valid_grammar (g : list Rule) : Prop :=
  match g with
  | h :: t => valid_rule h /\ valid_grammar t
  | nil => True
  end.

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
