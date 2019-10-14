{-# OPTIONS --prop #-}

{-
Transfinite, cumulative, Russell-style, inductive-recursive universes in Agda.

Checked with: Agda 2.6.0.1, stdlib 1.0

My original motivation was to give inductive-recursive (or equivalently: large inductive)
semantics to to Jon Sterling's cumulative algebraic TT paper:

  https://arxiv.org/abs/1902.08848

This requires cumulativity (obviously), Russell universes and tranfinite universes because
the standard model for Jon's TT requires Setω for the interpretation of contexts.

Prior art that I know about:
  - Conor:
      https://personal.cis.strath.ac.uk/conor.mcbride/pub/Hmm/Hier.agda
  - Larry Diehl:
      gist:   https://gist.github.com/larrytheliquid/3909860
      thesis: https://pdfs.semanticscholar.org/fc9a/5a2a904a7dff3562bcf31275d4b029894b5f.pdf
              section 8.1.3

However, these don't support Russell and transfinite universes.

-}


-- Preliminaries
--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Sum
open import Function
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality
open import Level renaming (suc to lsuc; zero to lzero; _⊔_ to lub)

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl x = x

_&_ = cong;  infixl 9 _&_; {-# DISPLAY cong  = _&_ #-}
_◾_ = trans; infixr 4 _◾_; {-# DISPLAY trans = _◾_ #-}
_⁻¹ = sym;   infix  6 _⁻¹; {-# DISPLAY sym   = _⁻¹ #-}

coe∘ : ∀ {i}{A B C : Set i}(p : B ≡ C)(q : A ≡ B)(a : A)
       → coe p (coe q a) ≡ coe (q ◾ p) a
coe∘ refl refl _ = refl

UIP : ∀ {i}{A : Set i}{x y : A}{p q : x ≡ y} → p ≡ q
UIP {p = refl}{refl} = refl

-- function extensionality
postulate
  ext : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
        → ((x : A) → f x  ≡ g x) → f ≡ g

  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : ∀ {x} → B x}
          → ((x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g

unAcc : ∀ {α β A R i} → Acc {α}{β}{A} R i → ∀ j → R j i → Acc R j
unAcc (acc f) = f

Acc-prop : ∀ {α β A R i}(p q : Acc {α}{β}{A} R i) → p ≡ q
Acc-prop (acc f) (acc g) = acc & ext λ j → ext λ p → Acc-prop (f j p) (g j p)

--------------------------------------------------------------------------------

-- Definition of a type-theoretic ordinal number, according to HoTT book chapter 10.3.

-- Ordinals below an i : Ord corrsepond to elements of i .Lvl (from each j : O.Lvl, we
-- get a j* : Ord, with j* .Lvl = ∃ λ k → k < j)

-- We'll get a universe hierarchy from each ordinal i, where levels are ordinals
-- below i.

-- We drop the extensionality condition from the HoTT book.

record Ordinal : Set₁ where
  infix 4 _<_
  field
    Lvl         : Set
    _<_         : Lvl → Lvl → Set
    <-prop      : ∀ {i j}{p q : i < j} → p ≡ q
    transitive  : ∀ {i j k} → i < j → j < k → i < k
    instance
      well-founded : ∀ {i} → Acc _<_ i

  <-irrefl : ∀ {i} → i < i → ⊥
  <-irrefl {i} p = go well-founded p where
    go : ∀ {i} → Acc _<_ i → i < i → ⊥
    go {i} (acc f) q = go (f i q) q


--------------------------------------------------------------------------------

module IR-Univ (ord : Ordinal) where
  open Ordinal ord
  open import Data.Nat hiding (_<_; _≤_)

  module _ {i}(l : ∀ j → j < i → Set) where
    infix 4 _<'_
    data UU : Set
    EL : UU → Set

    data UU where
      U'    : ∀ {j} → j < i → UU
      ℕ'    : UU
      Lvl'  : UU
      _<'_  : Lvl → Lvl → UU
      Π' Σ' : (a : UU) → (EL a → UU) → UU

    EL (U' p)   = l _ p
    EL ℕ'       = ℕ
    EL Lvl'     = Lvl
    EL (i <' j) = i < j
    EL (Π' a b) = ∀ x → EL (b x)
    EL (Σ' a b) = ∃ λ x → EL (b x)

  U↓ : ∀ {i} {{_ : Acc _<_ i}} j → j < i → Set
  U↓ {{acc f}} j p = UU (U↓ {{f j p}})

  U : Lvl → Set
  U i = UU (U↓ {i})

  El : ∀ {i} → U i → Set
  El = EL U↓

  U↓-compute : ∀ {i a j p} → U↓ {i}{{a}} j p ≡ U j
  U↓-compute {i} {acc f} {j} {p}
    = (λ a → UU (U↓ {{a}})) & Acc-prop (f j p) well-founded

  -- Cumulativity
  --------------------------------------------------------------------------------

  ↑   : ∀ {i j} → i < j → U i → U j
  El↑ : ∀ {i j} p a → El (↑ {i}{j} p a) ≡ El a
  ↑   p (U' q)   = U' (transitive q p)
  ↑   p ℕ'       = ℕ'
  ↑   p Lvl'     = Lvl'
  ↑   p (i <' j) = i <' j
  ↑   p (Π' a b) = Π' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (Σ' a b) = Σ' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  El↑ p (U' q)   = U↓-compute ◾ U↓-compute ⁻¹
  El↑ p ℕ'       = refl
  El↑ p Lvl'     = refl
  El↑ p (i <' j) = refl
  El↑ p (Π' a b) rewrite El↑ p a = (λ f → ∀ x → f x) & ext (El↑ p ∘ b)
  El↑ p (Σ' a b) rewrite El↑ p a = ∃ & ext (El↑ p ∘ b)


  -- Lift composition
  --------------------------------------------------------------------------------

  -- congruence helper
  ΠΣ≡ : ∀ {i l}
          (F' : (a : UU {i} l) → (EL l a → UU l) → UU l)
          {a₀ a₁ : UU l}(a₂ : a₀ ≡ a₁)
          {b₀ : EL l a₀ → UU l}{b₁ : EL l a₁ → UU l}
        → (∀ x → b₀ x ≡ b₁ (coe (EL l & a₂) x))
        → F' a₀ b₀ ≡ F' a₁ b₁
  ΠΣ≡ {i} {l} F' {a₀} refl {b₀} {b₁} b₂ = F' a₀ & ext b₂

  ↑↑ : ∀ {i j k}(p : i < j)(q : j < k) a → ↑ q (↑ p a) ≡ ↑ (transitive p q) a
  ↑↑ p q (U' r)   = U' & <-prop
  ↑↑ p q ℕ'       = refl
  ↑↑ p q Lvl'     = refl
  ↑↑ p q (i <' j) = refl
  ↑↑ p q (Π' a b) =
    ΠΣ≡ Π' (↑↑ p q a)
        (λ x → ↑↑ p q _
             ◾ (λ x → ↑ (transitive p q) (b x)) &
                  (coe∘ (El↑ p a) (El↑ q (↑ p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (El↑ (transitive p q) a) (EL _ & ↑↑ p q a) x ⁻¹))
  ↑↑ p q (Σ' a b) =
    ΠΣ≡ Σ' (↑↑ p q a)
        (λ x → ↑↑ p q _
             ◾ (λ x → ↑ (transitive p q) (b x)) &
                  (coe∘ (El↑ p a) (El↑ q (↑ p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (El↑ (transitive p q) a) (EL _ & ↑↑ p q a) x ⁻¹))

  -- Conveniences
  --------------------------------------------------------------------------------

  _⇒'_ : ∀ {i l} → UU {i} l → UU l → UU l
  a ⇒' b = Π' a λ _ → b
  infixr 3 _⇒'_

  _×'_ : ∀ {i l} → UU {i} l → UU l → UU l
  a ×' b = Σ' a λ _ → b
  infixr 4 _×'_

  ↑U : ∀ {i j}(p : i < j) → El (U' p) → U j
  ↑U p a = ↑ p (coe U↓-compute a)

  -- Example for supporting cumulative Russell universes in TT
  --------------------------------------------------------------------------------
  Con : Lvl → Set
  Con = U
  -- Jon Sterling has instead Con : Set, and his contexts are interpreted as U Top
  -- where Top is a chosen level such that every syntactic level is
  -- interpreted below it. The reason for this is that we'd like to just ignore
  -- context levels and lifts in the syntax of our TT.

  Ty : ∀ {i} → Con i → Lvl → Set
  Ty Γ j = El Γ → U j

  Tm : ∀ {i} Γ {j} → Ty {i} Γ j → Set
  Tm Γ A = (γ : El Γ) → El (A γ)

  ↑Ty : ∀ {j k i Γ} → j < k → Ty {i} Γ j → Ty Γ k
  ↑Ty p A γ = ↑ p (A γ)

  Cumulative : ∀ {i Γ j k p A} → Tm Γ A ≡ Tm Γ (↑Ty {j}{k}{i}{Γ} p A)
  Cumulative {p = p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ p (A γ) ⁻¹

  u : ∀ {i Γ j k} → j < k → Ty {i} Γ k
  u p _ = U' p

  Russell : ∀ {i Γ j k p} → Tm Γ (u {i}{Γ}{j}{k} p) ≡ Ty Γ j
  Russell = (λ f → ∀ x → f x) & ext λ γ → U↓-compute




-- Classical ordinals are additionall trichotomous (HoTT book 10.4)
--------------------------------------------------------------------------------
record ClassicalOrdinal (ord : Ordinal) : Set where
  open Ordinal ord
  field
    cmp : ∀ i j → i < j ⊎ j < i ⊎ i ≡ j

  _≤_ : Lvl → Lvl → Set; infix 4 _≤_
  i ≤ j = i < j ⊎ i ≡ j

  _⊔_ : Lvl → Lvl → Lvl; infixr 5 _⊔_
  i ⊔ j with cmp i j
  ... | inj₁  _ = j
  ... | inj₂₁ _ = i
  ... | inj₂₂ _ = i

  ⊔₁ : ∀ i j → i ≤ i ⊔ j
  ⊔₁ i j with cmp i j
  ... | inj₁  p = inj₁ p
  ... | inj₂₁ p = inj₂ refl
  ... | inj₂₂ p = inj₂ refl

  ⊔₂ : ∀ i j → j ≤ i ⊔ j
  ⊔₂ i j with cmp i j
  ... | inj₁  p = inj₂ refl
  ... | inj₂₁ p = inj₁ p
  ... | inj₂₂ p = inj₂ (p ⁻¹)

  ⊔-least : ∀ {i j k} → i ≤ k → j ≤ k → i ⊔ j ≤ k
  ⊔-least {i}{j}{k} p q with cmp i j
  ... | inj₁  _ = q
  ... | inj₂₁ _ = p
  ... | inj₂₂ _ = p

  ≤-prop : ∀ {i j}{p q : i ≤ j} → p ≡ q
  ≤-prop {p = inj₁ p}    {inj₁ q}    = inj₁ & <-prop
  ≤-prop {p = inj₁ p}    {inj₂ refl} = ⊥-elim (<-irrefl p)
  ≤-prop {p = inj₂ refl} {inj₁ q}    = ⊥-elim (<-irrefl q)
  ≤-prop {p = inj₂ p}    {inj₂ q}    = inj₂ & UIP


module IR-Univ-ClassicalOrdinal {ord} (clOrd : ClassicalOrdinal ord) where
  open ClassicalOrdinal clOrd public
  open IR-Univ ord public

  -- non-strict lifts
  ↑≤ : ∀ {i j} → i ≤ j → U i → U j
  ↑≤ (inj₁ p)    a = ↑ p a
  ↑≤ (inj₂ refl) a = a

  El↑≤ : ∀ {i j} p a → El (↑≤ {i}{j} p a) ≡ El a
  El↑≤ (inj₁ p)    a = El↑ p a
  El↑≤ (inj₂ refl) a = refl

  -- example: alternative type formation with _⊔_
  -- We might need this for models of TTs.
  Π'' : ∀ {i j}(a : U i) → (El a → U j) → U (i ⊔ j)
  Π'' {i}{j} a b = Π' (↑≤ (⊔₁ i j) a) λ x → ↑≤ (⊔₂ i j) (b (coe (El↑≤ (⊔₁ i j) a) x))

  -- context extension
  _▶_ : ∀ {i}(Γ : Con i){j} → Ty Γ j → Con (i ⊔ j)
  _▶_ {i} Γ {j} A = Σ' (↑≤ (⊔₁ i j) Γ) λ γ → ↑≤ (⊔₂ i j) (A (coe (El↑≤ (⊔₁ i j) Γ) γ))



-- Examples
--------------------------------------------------------------------------------

-- finite levels
module ℕ-example where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Induction.Nat

  ord : Ordinal
  ord = record {
      Lvl          = ℕ
    ; _<_          = _<_
    ; <-prop       = <-irrelevant _ _
    ; transitive   = <-trans
    ; well-founded = <-wellFounded _
    }

  open IR-Univ ord hiding (_<_)

  <suc : ∀ {i} → i < suc i
  <suc {i} = ≤-refl

  id' : ∀ {i} → El {suc i} (Π' (U' <suc) λ A → ↑U <suc A ⇒' ↑U <suc A)
  id' {i} A x = x

  const₀' : El {1} (Π' (U' <suc) λ A → Π' (U' <suc) λ B → ↑U <suc A ⇒' ↑U <suc B ⇒' ↑U <suc A)
  const₀' A B x y = x

-- ω*ω levels
module ℕ*ℕ-example where

  import Data.Nat as N
  open import Data.Nat.Properties
  open import Induction.Nat
  open Lexicographic N._<_ (λ _ → N._<_)

  trs : ∀ {i j k} → i < j → j < k → i < k
  trs (left  p) (left  q) = left (<-trans p q)
  trs (left  p) (right q) = left p
  trs (right p) (left  q) = left q
  trs (right p) (right q) = right (<-trans p q)

  <-prop : ∀ {i j} {p q : i < j} → p ≡ q
  <-prop {p = left  p} {left  q} = left & <-irrelevant _ _
  <-prop {p = left  p} {right q} = ⊥-elim (<-irrefl refl p)
  <-prop {p = right p} {left  q} = ⊥-elim (<-irrefl refl q)

  <-prop {p = right p} {right q} = right & <-irrelevant _ _

  --  representation: (i, j) ~ (ω*i + j)
  ord : Ordinal
  ord = record {
      Lvl          = N.ℕ × N.ℕ
    ; _<_          = _<_
    ; transitive   = trs
    ; <-prop       = <-prop
    ; well-founded = wellFounded <-wellFounded <-wellFounded _
    }

  open Ordinal ord hiding (_<_; transitive)
  open IR-Univ ord

  -- raise by 1
  <suc : ∀ {i j} → (i , j) < (i , N.suc j)
  <suc {i} = right ≤-refl

  -- raise to closest limit level
  <Suc : ∀ {i} j → (i , j) < (N.suc i , 0)
  <Suc {i} j = left ≤-refl

  ω : Lvl
  ω = 1 , 0

  #_ : N.ℕ → Lvl; infix 10 #_
  # n = 0 , n

  _+_ : Lvl → Lvl → Lvl; infix 6 _+_
  (i , j) + (i' , j') = i N.+ i' , j N.+ j'

  idω : El {ω} (Π' ℕ' λ i → Π' (U' (<Suc i)) λ A → ↑U (<Suc i) A ⇒' ↑U (<Suc i) A)
  idω i A x = x

  idω' : El {ω} (Π' Lvl' λ i → Π' (i <' ω) λ p → Π' (U' p) λ A → ↑U p A ⇒' ↑U p A)
  idω' i p A x = x

  fω+2 : El {ω + # 2} (U' (trs <suc <suc) ⇒' U' <suc)
  fω+2 = ↑U <suc
