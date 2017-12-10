Require Import Grammar.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive nonterminal : Type := | NT : string -> nonterminal.
Inductive terminal : Type := | Te : string -> terminal.

Definition production : Type := terminal * list nonterminal.
Definition grammar : Type := (nonterminal -> list (production)).

Definition simple_grammar : grammar :=
  fun s =>
    match s with
    | NT "S" => [((Te "a"),[(NT "B");(NT "B")])]
    | NT "B" => [((Te "b"),[])]
    | _ => []
    end. 
Definition a : string := "a".
Definition b : string := "b".
Definition c : string := "c".
  

Fixpoint check_rec (chars : list string) (g : grammar) (p : production) : bool * list string :=
  match chars, p with
  | char :: rest, (Te x, []) =>
    if string_dec char x then (true, rest) else (false, char :: rest)
  | char :: rest, (Te x, nts) =>
    if string_dec char x
    then
      (fold_left
         (fun old nt =>
            match old with
            | (true, tmp) =>
              fold_left
                (fun r1 r2 =>
                   match r1, r2 with
                   | (true, r), (_, _) => (true, r)
                   | (_, _), (true, r) => (true, r)
                   | (_, _), (_, _) => (false, [])
                   end
                )
                (map (check_rec' tmp g) (g nt))
                (true, rest)
            | (false, _) => (false, [])
            end)
         (nts)
         (true, rest))
    else (false, char :: rest)
  | _, _ => (false, [])
  end.

Definition check (str : list string) (g : grammar) (start : nonterminal) : bool :=
  fold_left orb (map (check_rec str g []) (g start)) false.

Compute check [a] simple_grammar (NT "S").
Compute check [a;b;b] simple_grammar (NT "S").
Compute check [a;b;b;b] simple_grammar (NT "S").
Compute check [a;b;b;b;b] simple_grammar (NT "S").
Compute check [a;a;b;c] simple_grammar (NT "S").
Compute check [a;a;b;c;c] simple_grammar (NT "S").
Compute check [a;a;b] simple_grammar (NT "S").
