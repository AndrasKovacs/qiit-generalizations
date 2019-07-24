# qiit-generalizations

The goal here is to write a paper about generalizing [quotient inductive-inductive types](https://dl.acm.org/citation.cfm?doid=3302515.3290315) to support:
- Large parameters; consider W-types, for example, which are parameterized by an external set of shapes and an external family of positions.
- Infinitary constructors. Again W-types are a classic example.
- Sort equations, or equalities between type constructors. They were permitted in Cartmell's [generarlized algebraic theories](https://www.sciencedirect.com/science/article/pii/0168007286900539?via%3Dihub). They are not widely used though, declaring Russell-style universes is the canonical example. 
- Recursive equations, i.e. equalities appearing as fields/hypotheses in a constructor. For recent examples, these appear in cubical type theories as boundary conditions.

## Content which is already mostly done

- Syntax for new QIITs. Two new versions:
  - Variant 1. Large, finitary, with sort equations. This is a superset of Cartmell's GATs.
  - Variant 2. Large, infinitary, with recurive equations but **no** sort equations.
  - We split the two versions, because we have term modell constructions for them *separately*, but not when every feature is
    mixed together.
- Semantics: 
  - For both variants: for each signature a CwF+Sigma+Id+K of algebras, abbreviated here as flCwF. Compared to "constructing QIITs", we add sigmas to the semantics, because then we get a nice sructure: by [Clairambault & Dybjer](https://arxiv.org/abs/1112.3456), the 2-cat of flCwFs is biequivalent to the 2-cat of finitely complete categories, hence the abbreviation.
  - For Variant 2, extension to "constructing QIITs": for each type in the theory of signatures, we get a split flCwF isofibration instead of a plain displayed flCwF. This gives us a strong form of invariance under isomorphisms of algebras. An illustrating special case: if we have A ~ B isomorphic sets, and A is a group, then B is also a group, and they are also isomorphic as groups.
    - This fails for Variant 1. Sort equations are **not** invariant under iso. E.g., if we have two isomorphic pairs of sets (A, B) ~ (A', B') and A = B, then A' = B' is not necessarily true. It is necessarily true in a univalent setting, but we work with UIP.
  - Term model construction. For variant 1, it's the same as in "constructing QIITs". For variant 2, it's a more complicated construction which requires iso invariance. From term model construction, we get that:
    - For each universe level, we uniformly have a Variant 2 QIIT such that all Variant 1 & 2 QIITs below that level are constructible from it.
    
## Possible content which is not done, and won't likely be in any next paper

- Showing that every algebraic flCwF morphism (i.e. a morphism given as the interpretation of a substitution of signatures) has a left adjoint. 
- Parts of Birkhoff HSP theorem for QIITs. The easy direction (lifting of monos/epis to appropriate displayed morphisms, for certain restricted types) seems clearly more feasible.
- Extending semantics with more constructions, e.g. coproducts, coequalizers, to get finite colimits on the top of finite limits. Then, we can try to show that categories of algebras are [regular](https://ncatlab.org/nlab/show/regular+category).
- Generalizing semantics to functorial semantics
  - Simple & stupid way: we just abstract over models of extensional TT. Example: notion of algebra for natural numbers consists of a model of ETT which has natural numbers. Then, the "classifying category" for each signature is just the syntax of ETT extended with the inductive type given by the signature. This is pretty easy because each "classifying category" is also just given by a QIIT. This way is a bit stupid becuase a model of ETT has more structure than what's actually needed to talk about algebras and induction.
  - Hard way: redo the entire flCwF semantics in functorial style, where every algebra lives in a given CwF (or something like that). The idea is the same as in the "stupid" version, but this is much harder, because we don't have universes or function space in plain CwFs, so we need to rework the semantics. "Classifying CwFs" are also just QIITs here as well.
- Be able to give not just flCwF isofibrations, but fibartions/opfibrations as well. This requires a "polarized" syntax of signatures, where we keep track of whether a type is covariant, contravariant or invaraiant in the preceding context. This would be a nice syntax for building lots of fibrations.
