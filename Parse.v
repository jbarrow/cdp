Require Import Grammar.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Datatypes.
Require Import PeanoNat.
Import ListNotations.

Inductive Tree : Type :=
  | Leaf : symbol -> Tree
  | Node : symbol -> list Tree -> Tree.

(* This is the derivation tree for the smallest string in the
 * language `simple_grammar`, a. *)
Check Node (N "S") (Leaf (T "a") :: nil).


Inductive item : Type :=
  | I : nat -> symbol -> list symbol -> list symbol -> nat -> list Tree -> item.

Notation "'{' i ',' b '==>' s '*' ss ',' j '}'" := (I i b s ss j []) (at level 60).

Definition trees (i : item) : list Tree :=
  match i with
  | I _ _ _ _ _ t => t
  end.

Definition axioms (g : list Rule) : list item :=
  match start_symbol g with
  | Some s => [I 0 (D "S'") [] [s] 0 []]
  | None => []
  end.

Compute axioms simple_grammar.

(* TODO: Fix goal *)
Definition goal (g : list Rule) (s : list id) (i : item) : Prop :=
  match i with
  | I i symbol symbols symbols' k trees => i = 0 /\ dummy symbol /\ symbols' = []
  end.

Definition beq_s_r (s : symbol) (r : Rule) :=
  beq_symbol s (lhs r).

(* The `scan` rule for our Earley parser has the form:
 * 
 *   i, A → α • wjβ, j
 * ----------------------
 * i, A → αwj • β, j + 1
 *)
Definition scan (tokens : list id) (trigger : item) : list item :=
  match trigger with
  | I i a alpha [] j ts => []
  | I i a alpha (symbol :: b) j ts =>
    if (Nat.ltb (Datatypes.length tokens) j)
    then []
    else (
        if beq_symbol symbol (Terminal (nth j tokens (Id "")))
        then [I i a (alpha ++ [symbol]) b (j+1) (ts ++ [Leaf (Terminal (nth j tokens (Id "")))])]
        else []
      )
  end.

(* The `predict` rule for our Earley parser has the form:
 * 
 * i, A → α • B
 * ------------- β, j
 * j, B → •γ, j
 *
 *)
Definition predict_item (j : nat) (r : Rule) : item :=
  match r with
  | R b gamma => I j b [] gamma j []
  end.
  
Definition predict (g : list Rule) (trigger : item) : list item :=
  match trigger with
  | I i a alpha [] j ts => []
  | I i a alpha (symbol :: b) j ts =>
    map (predict_item j) (filter (beq_s_r symbol) g)
  end.

(* The `complete` rule for our Earley parser has the form:
 *
 * i, A → α • Bβ, k k, B → γ•, j
 * -------------------------------
 *       i, A → αB • β, j
 *)
Definition complete (trigger : item) (stored : list item) : list item :=
  match trigger with
  | I i a alpha ((N x) :: b) k ts => []
  | I k (N x) gamma [] j ts => []
  | _ => []
  end.

Definition consequences
           (grammar : list Rule) (tokens : list id)
           (trigger : item) (stored : list item) : list item :=
  (scan tokens trigger) ++ (predict grammar trigger) ++ (complete trigger stored).

Definition initial_store (g : list Rule) : (list item * list item) :=
  ([], axioms g).

Fixpoint exhaust_agenda (g : list Rule) (tokens : list id) (store : list item * list item) : (list item * list item) :=
  match store with
  | (chart, []) => (chart, [])
  | (chart, trigger :: rest) =>
    exhaust_agenda g tokens
                   (
                     chart ++ [trigger],
                     rest ++ (consequences g tokens trigger chart)
                   )
  end.

