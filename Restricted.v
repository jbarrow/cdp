Require Import Grammar.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive nonterminal : Type :=
| NT : string -> nonterminal.

Inductive terminal : Type :=
| Te : string -> terminal.

Definition production : Type := terminal * option nonterminal.
Definition grammar : Type := (nonterminal -> list (production)).
Definition token : Type := string.

Definition a : string := "a".
Definition b : string := "b".
Definition c : string := "c".

Definition simple_grammar : grammar :=
  fun s =>
    match s with
    | NT "S" => [(Te "a", Some (NT "B"))]
    | NT "B" => [(Te "a", Some (NT "B"));(Te "b", None)]
    | _ => []
    end.

Fixpoint check_rec (str : list string) (g : grammar) (p : production) : bool :=
  match str, p with
  | _ :: _ :: _, (Te _, None) => false
  | f :: r, (Te x, None) => if string_dec x f then true else false
  | f :: r, (Te x, Some (NT n)) =>
    if string_dec x f
    then (fold_left orb (map (check_rec r g) (g (NT n))) false)
    else false
  | _, _ => false
  end.

Definition check (str : list string) (g : grammar) (start : nonterminal) : bool :=
  fold_left orb (map (check_rec str g) (g start)) false.

Compute check [a] simple_grammar (NT "S").
Compute check [a;b;b] simple_grammar (NT "S").
Compute check [a;b;b;b] simple_grammar (NT "S").
Compute check [a;b;b;b;b] simple_grammar (NT "S").
Compute check [a;a;b;c] simple_grammar (NT "S").
Compute check [a;a;b;c;c] simple_grammar (NT "S").
Compute check [a;a;b] simple_grammar (NT "S").
Compute check [a;a;c] simple_grammar (NT "S").

Inductive tree : Type :=
  | Leaf : terminal -> tree
  | Node : nonterminal -> list tree -> tree.

Fixpoint left_branching (t : tree) : Prop :=
  match t with
  | Leaf _ => True
  | Node _ ((Leaf _) :: tr) => fold_left and (map left_branching tr) True
  | Node _ ((Node _ _) :: tr) => False
  | Node _ [] => False
  end.

Definition option_left_branching (t : option tree) : Prop :=
  match t with
  | Some t => left_branching t
  | None => False
  end.

Lemma lbleaf : left_branching (Leaf (Te "a")) = True.
Proof. unfold left_branching. reflexivity. Qed.

Fixpoint first_true (str : list string) (g : grammar) (ps : list production) : option production :=
  match ps with
  | p :: t => if check_rec str g p then Some p else first_true str g t
  | [] => None
  end. 

Fixpoint parse (str : list string) (g : grammar) (n : nonterminal) : option tree :=
  match first_true str g (g n) with
  | Some p =>
    match str, p with
    | f :: r, (t, None) => Some (Node n [Leaf t])
    | f :: r, (t, Some n') =>
      match parse r g n' with
      | None => None
      | Some t' => Some (Node n ([Leaf t; t']))
      end
    | _, _ => None
    end
  | None => None
  end.


Compute parse [a;a;b] simple_grammar (NT "S").
Compute parse [a;b] simple_grammar (NT "S").
Compute parse [a] simple_grammar (NT "S").
Compute parse [a;a;b;b] simple_grammar (NT "S").

Definition parse_exists (str : list string) (g : grammar) (s : nonterminal) : Prop :=
  match parse str g s with
  | Some _ => True
  | None => False
  end.

Lemma check_equal_to_parse : forall (g : grammar) (str : list string) (s : nonterminal),
    check str g s = true -> parse_exists str g s.
Admitted.

Lemma parse_left_branching : forall (g : grammar) (str : list string) (s : nonterminal),
    parse_exists str g s -> option_left_branching (parse str g s).
Admitted.