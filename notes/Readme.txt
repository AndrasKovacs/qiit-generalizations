
Term algebras with eliminators for QIITs.

Note:
- signatures with an empty universe U are necessarily finitary with
  non-recursive equations.
- We can *not* build term models with non-empty U and sort equations at the same time!
  Non-empty U requires semantic types to respect (lift) base isomorphisms, but
  sort equations fail to lift isos!

TODO:
- see whether term models can be given strictly even with non-empty U.
- generalize every external type to some arbitrary universe level.
