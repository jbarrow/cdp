Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive token : Type :=
  | Token : string -> token.

Inductive symbol : Type :=
  | Nonterminal : token -> symbol
  | Terminal : token -> symbol.

Definition nonterminal (s : symbol) : Prop :=
  match s with
  | Terminal _ => False
  | _ => True
  end.

Definition terminal (s : symbol) : Prop :=
  ~ (nonterminal s).

Inductive rule : Type :=
  | Rule : symbol -> list symbol -> rule.

Notation "'N' a" := (Nonterminal (Token a)) (at level 60).
Notation "'T' a" := (Terminal (Token a)) (at level 60).

Notation "a '-->' b" := (Rule a b) (at level 80).

Check N "s".

(* Starting with a simple grammar of { a^n | n % 2 == 1 }.
 * S -> aSa | a *)
Definition simple_grammar : list rule :=
  [
    N "S" --> [T "a" ; N "S" ; T "a"] ;
      N "S" --> [T "a"]
  ].

Check simple_grammar.

Definition lhs (r : rule) : symbol :=
  match r with
  | Rule x _ => x
  end.

Definition rhs (r : rule) : list symbol :=
  match r with
  | Rule _ ys => ys
  end.

Definition beq_symbol (s1 s2 : symbol) : bool :=
  match s1 with
  | N x =>
    match s2 with
    | N y => if string_dec x y then true else false
    | _ => false
    end
  | T x =>
    match s2 with
    | T y => if string_dec x y then true else false
    | _ => false
    end
  end.

Definition start_symbol (g : list rule) : option symbol :=
  match g with
  | h :: _ => Some (lhs h)
  | nil => None
  end.

Definition valid_rule (r : rule) : Prop :=
  nonterminal (lhs r).

Fixpoint valid_grammar (g : list rule) : Prop :=
  match g with
  | h :: t => valid_rule h /\ valid_grammar t
  | nil => True
  end.

Lemma valid_item : forall (l : list rule) (r : rule),
    valid_grammar (r :: l) -> valid_rule r.
Proof. intros. induction l; inversion H; apply H0. Qed.

Lemma valid_composition : forall (l : list rule) (r : rule),
    valid_grammar (r :: l) -> valid_grammar l.
Proof. intros. induction l; inversion H; apply H1. Qed.       

Lemma valid : forall (l:list rule) (r: rule),
    In r l -> valid_grammar l -> valid_rule r.
Proof with eauto.
  intros. induction l; inversion H.
  - subst. apply valid_item in H0. apply H0.
  - apply valid_composition in H0. apply IHl...
Qed.
