Require Import Grammar.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive nonterminal : Type :=
| NT : string -> nonterminal.

Inductive terminal : Type :=
| Te : string -> terminal.

Definition production : Type := terminal * list nonterminal.
Definition grammar : Type := (nonterminal -> production).

Definition a : string := "a".
Definition b : string := "b".
Definition c : string := "c".

Definition simple_grammar : grammar :=
  fun s =>
    match s with
    | NT "S" => ((Te "a"),[(NT "B");(NT "B")])
    | NT "B" => ((Te "b"),[])
    | _ => ((Te ""), [])
    end. 

Fixpoint check (g : grammar) (tokens : list string) (nt : nonterminal) : bool * list string :=
  match tokens, g nt with
  | token :: ts, (Te x, []) => if string_dec token x then (true, ts) else (false, [])
  | token :: ts, (Te x, ns) =>
    if string_dec token x then
      fold_left (fun ts' nt =>
                   match ts' with
                   | (true, tmp) => check g tmp nt
                   | (false, _) => (false, [])
                   end) ns (true, ts)
    else (false, [])
  | _, _ => (false, [])
  end.
