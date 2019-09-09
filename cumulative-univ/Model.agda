{-# OPTIONS --rewriting #-}

open import StrictLib
  renaming (zero to lzero; suc to lsuc)
  hiding (lift)

open import Data.Nat hiding (_≤_)
open import Data.Nat.Properties
open import Data.Bool

Lvl : Set₁
Lvl = Σ Set λ A → A → Set

data UU (l : Lvl) : Set
EL : ∀ {l} → UU l → Set

data UU l where
  U' Bool' : UU l
  Π' Σ'    : (a : UU l) → (EL a → UU l) → UU l
  El'      : l .₁ → UU l

EL {l} U'      = l .₁
EL Bool'       = Bool
EL (Π' a b)    = (x : EL a) → EL (b x)
EL (Σ' a b)    = ∃ λ (x : EL a) → EL (b x)
EL {l} (El' a) = l .₂ a

U   : ℕ → Set
↓U  : ℕ → Set
↓El : ∀ {n} → ↓U n → Set
U n         = UU (↓U n , ↓El {n})
↓U zero     = ⊥
↓U (suc n)  = U n
↓El {suc n} = EL {↓U n , ↓El {n}}

--------------------------------------------------------------------------------

El : ∀ i → U i → Set
El i = EL {↓U i , ↓El}

_⇒'_ : ∀ {l} → UU l → UU l → UU l
a ⇒' b = Π' a λ _ → b
infixr 3 _⇒'_

_×'_ : ∀ {l} → UU l → UU l → UU l
a ×' b = Σ' a λ _ → b
infixr 4 _×'_

--------------------------------------------------------------------------------

id' : ∀ {i} → El i (Π' U' λ A → El' A ⇒' El' A)
id' {i} A x = x

foo : (Bool → Bool) → Bool → Bool
foo = id' {1} (Bool' ⇒' Bool')

apply' : ∀ {i} → El i (
  Π' U' λ A → Π' (El' A ⇒' U') λ B
  → (Π' (El' A) λ x → El' (B x)) ⇒' (Π' (El' A) λ x → El' (B x)))
apply' {i} A B = id' {suc i} (Π' (El' A) λ x → El' (B x))

uncurry' : ∀ {i} → El i (Π' U' λ A → Π' U' λ B → Π' U' λ C
  → (El' A ⇒' El' B ⇒' El' C) ⇒' (El' A ×' El' B) ⇒' El' C)
uncurry' A B C f (x , y) = f x y


-- cumulativity
--------------------------------------------------------------------------------

data sub : ∀ {i j} → U i → U j → Set
lift : ∀ {i j a b} → sub a b → El i a → El j b

data sub where -- can be also implemented without IR, with recursive sub
  Bool' : ∀ {i}{j} → sub {i}{j} Bool' Bool'
  U'    : ∀ {i j} → sub {i}{j + i} U' U'
  Π'    : ∀ {i j a a' b b'}
          → (p : sub {j}{i} a' a)
          → (∀ x → sub (b (lift p x)) (b' x))
          → sub (Π' a b) (Π' a' b')
  Σ'    : ∀ {i j a a' b b'}
          → (p : sub {i}{j} a a')
          → (∀ x → sub (b x) (b' (lift p x)))
          → sub (Σ' a b) (Σ' a' b')
  El'   : ∀ {i j a a'} → sub {i}{j} a a'
          → sub (El' a) (El' a')

lift Bool'            x = x
lift (U' {j = zero})  x = x
lift (U' {j = suc j}) x = El' (lift U' x)
lift (Π' p q)         f = λ α → lift (q _) (f (lift p α))
lift (Σ' p q)         t = lift p (t .₁) , lift (q _) (t .₂)
lift (El' p)          x = lift p x

subUProp : ∀ {i j k}(p' : sub {i}{k} U' U')(r : k ≡ j + i)
     → U' ≡ tr (λ x → sub {i}{x} U' U') r p'
subUProp {i} {j} {.(j₁ + i)} (U' {j = j₁}) r with +-cancelʳ-≡ j₁ j r | r
... | refl | refl = refl

subProp : ∀ {i j a b}(p p' : sub {i}{j} a b) → p ≡ p'
subProp Bool' Bool' = refl
subProp U'    p'    = subUProp p' refl
subProp (Π' p q) (Π' p' q') rewrite subProp p p' =
  Π' p' & ext (λ x → subProp (q x) (q' x))
subProp (Σ' p q) (Σ' p' q') rewrite subProp p p' =
  Σ' p' & ext λ x → subProp (q x) (q' x)
subProp (El' p) (El' p') = El' & subProp p p'

-- TODO
-- coh: sub a (lift p a)
-- rfl: sub a a
-- trs: ...

-- examples
--------------------------------------------------------------------------------

{-# REWRITE +-suc #-}

Uj+ : ∀ {i j} → sub {suc i}{suc (j + i)} U' U'
Uj+ {i}{j} = U'

U+i : ∀ {i j} → sub {suc j}{suc (j + i)} U' U'
U+i {i}{j} =
  tr (λ x → sub {suc j}{x} U' U') (suc & +-comm i j) (U'{suc j}{i})

hΠ' : ∀ {i j} → (a : U i) → ((x : El (j + i) (lift Uj+ a)) → U j) → U (j + i)
hΠ' {i}{j} a b = Π' (lift Uj+ a) λ x → lift (U+i{i}{j}) (b x)

coh : ∀ {i j}(a : U i) → sub a (lift (Uj+{i}{j}) a)
coh {i} {zero}  U' = U'
coh {i} {suc j} U' = {!!}
coh Bool' = {!!}
coh (Π' a x) = {!!}
coh (Σ' a x) = {!!}
coh (El' x) = {!!}

--------------------------------------------------------------------------------

codSub : ∀ {i j a b b'} → (∀ x → sub {i} {j + i} (b x) (b' {!!})) →
  sub {i}{j + i} (Π' a b) (Π' (lift Uj+ a) b')
codSub = {!!}



-- ex1 : ∀ {i} → U (2 + i)
-- ex1 = Π' {!UU.U'!} {!!}
