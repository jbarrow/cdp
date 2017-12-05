# Deductive Parsing in Coq

This is the CMSC 631 final project for [Denis Peskov]() and [Joe Barrow](). When completed, it will be a formally verified Earley parser in Coq for parsing natural languages.

## Grammars

In our formalism, `Grammar`s are defined as lists of `Rule`s, and a `Rule` is consists of a non-terminal symbol going to a list of symbols. For example, the following code outlines the grammar for the language of `a^n` where `n` is odd.

```coq
Definition grammar : Grammar :=
  G [(N "S") --> [(T "a") ; (N "S") ; (T "a")] ; (N "S") --> [T "a"]].
```

To compile the grammar, run:

```
coqc Grammar.v
```

This is required in order to run the Parse.v file.

## Parsing

TODO
