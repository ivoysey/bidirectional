- so that i don't have to implement an ABT library in agda---which is a
  worthy but hard project of its very own---i'm making a very strong
  assumption about variables throughout this file. that is to say, i'm
  assuming every term is already in something i want to call a "de bruijn
  normal form", and therefore any time you see a variable named with a
  particular nat it is meant to be the same variable as anything else in
  the whole term named with that nat -- and it's up to the programmer to
  not mess this up.


- here's an interesting thing. in the straight forward encoding of the
  declarative system into a dependent type, there are a few constructors
  with unconstrained arguments. this makes sense in the typing rule, but
  when you actually ask agda to cough up an inhabitant for the type that
  represents a particular derivation, some of the implicit arguments are
  unbound

  for example, with out the annotation here, agda doesn't load cleanly
```agda
    ex2 : · ⊢ case (inl <>) (V , fst < X V , <> >) (V , <>) :: unit
    ex2 = TCase {t2 = unit} (TInl TUnit) (TFst (TProd (TX ∈h) TUnit)) TUnit
```
  because anything in \tau will work there -- the actual program doesn't do
  anything with t2 so it doesn't really appear

  Q: are the places where you need to annotate in the metalanguage the same
     places that a bidirectional system would switch from ==> to <== in the
     object language? or is this coincidence?
