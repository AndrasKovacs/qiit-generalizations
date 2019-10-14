{-# OPTIONS --without-K #-}

open import Data.Bool
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl x = x

ap = cong

postulate
  -- function extensionality
  ext : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
        → ((x : A) → f x  ≡ g x) → f ≡ g

--------------------------------------------------------------------------------

-- semantic levels: finite or infinite lists
Lvl : Set₁
Lvl = List Set ⊎ (ℕ → Set)

Below : Lvl → Set₀
Below (inj₁ xs) = Fin (length xs)
Below (inj₂ f ) = ℕ

data UU (l : Lvl) : Set
EL : ∀ {l} → UU l → Set

data UU l where
  U'          : Below l → UU l
  Bool' ⊤' ℕ' : UU l
  Π' Σ'       : (a : UU l) → (EL a → UU l) → UU l

EL {inj₁ xs} (U' x) = lookup xs x
EL {inj₂ f}  (U' x) = f x
EL Bool'            = Bool
EL ℕ'               = ℕ
EL ⊤'               = ⊤
EL (Π' a b)         = (x : EL a) → EL (b x)
EL (Σ' a b)         = ∃ λ x → EL (b x)

finlvl : ℕ → List Set
finlvl zero    = []
finlvl (suc n) = let As = finlvl n in UU (inj₁ As) ∷ As

U : ℕ → Set -- universes at finite lvls
U n = UU (inj₁ (finlvl n))

Uω : Set
Uω = UU (inj₂ U)

-- finite El
El : ∀ {n} → U n → Set
El = EL

Elω : Uω → Set
Elω = EL

-- lifting a finite level by 1
↑   : ∀ {i} → U i → U (suc i)
El↑ : ∀ {i}(a : U i) → El (↑ a) ≡ El a
↑ (U' x)   = U' (suc x)
↑ Bool'    = Bool'
↑ ℕ'       = ℕ'
↑ ⊤'       = ⊤'
↑ (Π' a b) = Π' (↑ a) (λ x → ↑ (b (coe (El↑ a) x)))
↑ (Σ' a b) = Σ' (↑ a) (λ x → ↑ (b (coe (El↑ a) x)))
El↑ (U' x) = refl
El↑ Bool'  = refl
El↑ ℕ'     = refl
El↑ ⊤'     = refl
El↑ (Π' a b) rewrite El↑ a = ap (λ f → ∀ x → f x) (ext (El↑ ∘ b))
El↑ (Σ' a b) rewrite El↑ a = ap ∃ (ext (El↑ ∘ b))

-- -- lifting a finite level to ω
dropFin : ∀ {α A} xs → Fin (length {α}{A} xs) → List A
dropFin (_ ∷ xs) zero    = xs
dropFin (_ ∷ xs) (suc x) = dropFin xs x

lem1 : ∀ i → length (finlvl i) ≡ i
lem1 zero    = refl
lem1 (suc i) = ap suc (lem1 i)

lem2 : ∀ i (x : Fin (length (finlvl i)))
       → UU (inj₁ (finlvl (length (dropFin (finlvl i) x))))
       ≡ lookup (finlvl i) x
lem2 (suc i) zero rewrite lem1 i = refl
lem2 (suc i) (suc x) = lem2 i x

↑ω   : ∀ {i} → U i → Uω
El↑ω : ∀ {i}(a : U i) → Elω (↑ω a) ≡ El a
↑ω {i} (U' x)   = U' (length (dropFin (finlvl i) x))
↑ω Bool'        = Bool'
↑ω ℕ'           = ℕ'
↑ω ⊤'           = ⊤'
↑ω (Π' a b)     = Π' (↑ω a) λ x → ↑ω (b (coe (El↑ω a) x))
↑ω (Σ' a b)     = Σ' (↑ω a) λ x → ↑ω (b (coe (El↑ω a) x))
El↑ω {i} (U' x) = lem2 i x
El↑ω Bool'      = refl
El↑ω ℕ'         = refl
El↑ω ⊤'         = refl
El↑ω (Π' a b) rewrite El↑ω a = ap (λ f → ∀ x → f x) (ext (El↑ω ∘ b))
El↑ω (Σ' a b) rewrite El↑ω a = ap ∃ (ext (El↑ω ∘ b))

-- examples
--------------------------------------------------------------------------------

↓1 : ∀ {i} → Below (inj₁ (finlvl (1 + i)))
↓1 {i} = zero

↓2 : ∀ {i} → Below (inj₁ (finlvl (2 + i)))
↓2 {i} = suc zero

↓3 : ∀ {i} → Below (inj₁ (finlvl (3 + i)))
↓3 {i} = suc (suc zero)

_⇒'_ : ∀ {l} → UU l → UU l → UU l
a ⇒' b = Π' a λ _ → b
infixr 3 _⇒'_

_×'_ : ∀ {l} → UU l → UU l → UU l
a ×' b = Σ' a λ _ → b
infixr 4 _×'_

-- external level polymorphism
id' : ∀ i → El {suc i} (Π' (U' (↓1{i})) λ A → ↑ A ⇒' ↑ A)
id' i A x = x

-- internal level polymorphism
id'ω : Elω (Π' ℕ' λ i → Π' (U' i) λ A → ↑ω A ⇒' ↑ω A)
id'ω i A x = x
