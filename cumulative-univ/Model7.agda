{-# OPTIONS --prop #-}

open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Nat.Properties
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Sum
open import Function
open import Induction.WellFounded
open import Induction.Nat
open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to lub)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl x = x
_&_ = cong; infixl 9 _&_; {-# DISPLAY cong = _&_ #-}
_◾_ = trans; infixr 4 _◾_; {-# DISPLAY trans = _◾_ #-}
_⁻¹ = sym; infix 6 _⁻¹; {-# DISPLAY sym = _⁻¹ #-}

coe∘ : ∀ {i}{A B C : Set i}(p : B ≡ C)(q : A ≡ B)(a : A)
       → coe p (coe q a) ≡ coe (q ◾ p) a
coe∘ refl refl _ = refl

UIP : ∀ {i}{A : Set i}{x y : A}{p q : x ≡ y} → p ≡ q
UIP {p = refl}{refl} = refl

-- function extensionality
postulate
  ext : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
        → ((x : A) → f x  ≡ g x) → f ≡ g

  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

unAcc : ∀ {α β A R i} → Acc {α}{β}{A} R i → ∀ j → R j i → Acc R j
unAcc (acc f) = f

record LevelStruct : Set₁ where
  infix 4 _<_
  field
    Lvl         : Set
    _<_         : Lvl → Lvl → Set
    trs         : ∀ {i j k} → i < j → j < k → i < k
    cmp         : Trichotomous _≡_ _<_
    instance wf : ∀ {i} → Acc _<_ i
    irrelevant  : ∀ {i j}{p q : i < j} → p ≡ q

module IRU (lvl : LevelStruct) where
  open LevelStruct lvl public
  open import Data.Nat hiding (_<_; _≤_; _⊔_)

  ⟦_⟧ᴸ : Lvl → Set₁
  ⟦ i ⟧ᴸ = ∀ {j} → j < i → Set

  infix 4 _<'_

  data UU {i}(l : ⟦ i ⟧ᴸ) : Set
  EL : ∀ {i}{l : ⟦ i ⟧ᴸ} → UU l → Set

  ------------------------------------------------------------
  data UU {i} l where
    U'    : ∀ {j} → j < i → UU l
    ℕ' L' : UU l
    _<'_  : Lvl → Lvl → UU l
    Π' Σ' : (a : UU l) → (EL a → UU l) → UU l

  EL {_}{l}(U' p) = l p
  EL ℕ'           = ℕ
  EL L'           = Lvl
  EL (i <' j)     = i < j
  EL (Π' a b)     = ∀ x → EL (b x)
  EL (Σ' a b)     = ∃ λ x → EL (b x)
  ------------------------------------------------------------

  U↓ : ∀ i {{_ : Acc _<_ i}} → ⟦ i ⟧ᴸ
  U↓ i {{acc f}} {j} p = UU (U↓ j {{f j p}})

  -- we need the ordering and wf proofs to make U↓ well-founded,
  -- but the result only depends on the low index
  U↓-irr : ∀ {j i i' a a' p p'} → U↓ i {{a}} {j} p ≡ U↓ i' {{a'}} {j} p'
  U↓-irr {j} {i} {i'} {acc f} {acc f'} {p} {p'} =
    UU {j} & exti λ k → ext λ q → U↓-irr {_}{_}{_}{f j p}{f' j p'}

  U : Lvl → Set
  U i = UU (U↓ i)

  El : ∀ {i} → U i → Set
  El = EL

  -- requires: trs
  ↑   : ∀ {i j} → i < j → U i → U j
  El↑ : ∀ {i j} p a → El (↑ {i}{j} p a) ≡ El a
  ↑   p (U' q)   = U' (trs q p)
  ↑   p ℕ'       = ℕ'
  ↑   p L'       = L'
  ↑   p (i <' j) = i <' j
  ↑   p (Π' a b) = Π' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (Σ' a b) = Σ' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  El↑ p (U' q)   = U↓-irr
  El↑ p ℕ'       = refl
  El↑ p L'       = refl
  El↑ p (i <' j) = refl
  El↑ p (Π' a b) rewrite El↑ p a = (λ f → ∀ x → f x) & ext (El↑ p ∘ b)
  El↑ p (Σ' a b) rewrite El↑ p a = ∃ & ext (El↑ p ∘ b)

  F'≡ : ∀ {i}{l : ⟦ i ⟧ᴸ}
          (F' : (a : UU l) → (EL a → UU l) → UU l)
          {a₀ a₁ : UU l}(a₂ : a₀ ≡ a₁)
          {b₀ : EL a₀ → UU l}{b₁ : EL a₁ → UU l}
        → (∀ x → b₀ x ≡ b₁ (coe (EL & a₂) x))
        → F' a₀ b₀ ≡ F' a₁ b₁
  F'≡ {i} {l} F' {a₀} refl {b₀} {b₁} b₂ = F' a₀ & ext b₂

  ↑↑ : ∀ {i j k}(p : i < j)(q : j < k) a → ↑ q (↑ p a) ≡ ↑ (trs p q) a
  ↑↑ p q (U' r)   = U' & irrelevant
  ↑↑ p q ℕ'       = refl
  ↑↑ p q L'       = refl
  ↑↑ p q (i <' j) = refl
  ↑↑ p q (Π' a b) =
    F'≡ Π' (↑↑ p q a)
        (λ x → ↑↑ p q _
             ◾ (λ x → ↑ (trs p q) (b x)) &
                  (coe∘ (El↑ p a) (El↑ q (↑ p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (El↑ (trs p q) a) (EL & ↑↑ p q a) x ⁻¹))
  ↑↑ p q (Σ' a b) =
    F'≡ Σ' (↑↑ p q a)
        (λ x → ↑↑ p q _
             ◾ (λ x → ↑ (trs p q) (b x)) &
                  (coe∘ (El↑ p a) (El↑ q (↑ p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (El↑ (trs p q) a) (EL & ↑↑ p q a) x ⁻¹))

  -- _⊔_
  --------------------------------------------------------------------------------

  _≤_ : Lvl → Lvl → Set; infix 4 _≤_
  i ≤ j = i < j ⊎ i ≡ j

  _⊔_ : Lvl → Lvl → Lvl; infixr 5 _⊔_
  i ⊔ j with cmp i j
  ... | tri< _ _ _ = j
  ... | tri≈ _ _ _ = j
  ... | tri> _ _ _ = i

  ⊔₁ : ∀ i j → i ≤ i ⊔ j
  ⊔₁ i j with cmp i j
  ... | tri< a ¬b ¬c = inj₁ a
  ... | tri≈ ¬a b ¬c = inj₂ b
  ... | tri> ¬a ¬b c = inj₂ refl

  ⊔₂ : ∀ i j → j ≤ i ⊔ j
  ⊔₂ i j with cmp i j
  ... | tri< a ¬b ¬c = inj₂ refl
  ... | tri≈ ¬a b ¬c = inj₂ refl
  ... | tri> ¬a ¬b c = inj₁ c

  ⊔-rec : ∀ {i j k} → i ≤ k → j ≤ k → i ⊔ j ≤ k
  ⊔-rec {i}{j}{k} p q with cmp i j
  ... | tri< _ _ _ = q
  ... | tri≈ _ _ _ = q
  ... | tri> _ _ _ = p

  -- convenience
  --------------------------------------------------------------------------------

  _⇒'_ : ∀ {i}{l : ⟦ i ⟧ᴸ} → UU l → UU l → UU l
  a ⇒' b = Π' a λ _ → b
  infixr 3 _⇒'_

  _×'_ : ∀ {i}{l : ⟦ i ⟧ᴸ} → UU l → UU l → UU l
  a ×' b = Σ' a λ _ → b
  infixr 4 _×'_

  -- implied by missing eta law for Acc
  U↓η : ∀ {i}(a : Acc _<_ i) → (λ {j} → U↓ i {{a}} {j}) ≡ (λ {j} p → UU (U↓ j {{unAcc a j p}}))
  U↓η {i}(acc f) = refl

  U↓-irr' : ∀ {i a a'} → (λ {j} → U↓ i {{a}} {j}) ≡ U↓ i {{a'}}
  U↓-irr' {i} {acc f} {acc g} = exti λ j → ext λ p → UU & exti λ _ → ext λ _ → U↓-irr

  ↑U : ∀ {i j}(p : i < j) → EL {_} {U↓ j {{wf}}} (U' p) → U j
  ↑U {i} {j} p A = ↑ p (coe ((λ f → f p) & U↓η {j} wf ◾ UU & U↓-irr') A)

  -- Π with _⊔_




-- -- module ℕ-example where
-- --   open import Data.Nat

-- --   univ : Univ
-- --   univ = record {
-- --       Lvl = ℕ
-- --     ; _<_ = _<_
-- --     ; trs = <-trans
-- --     ; wf  = <-wellFounded _
-- --     ; ass = λ _ _ _ → <-irrelevant _ _
-- --     }

-- --   open IRU univ

-- --   <suc : ∀ {i} → i < suc i
-- --   <suc {i} = ≤-refl

-- --   id' : ∀ {i} → El {suc i} (Π' (U' <suc) λ A → ↑U <suc A ⇒' ↑U <suc A)
-- --   id' {i} A x = x

-- --   const₀' : El {1} (Π' (U' <suc) λ A → Π' (U' <suc) λ B → ↑U <suc A ⇒' ↑U <suc B ⇒' ↑U <suc A)
-- --   const₀' A B x y = x

-- -- module ℕ*ℕ-example where
-- --   import Data.Nat as N

-- --   open Lexicographic N._<_ (λ _ → N._<_)

-- --   trs : ∀ {i j k} → i < j → j < k → i < k
-- --   trs (left  p) (left  q) = left (<-trans p q)
-- --   trs (left  p) (right q) = left p
-- --   trs (right p) (left  q) = left q
-- --   trs (right p) (right q) = right (<-trans p q)

-- --   <-irr : ∀ {i j}(p q : i < j) → p ≡ q
-- --   <-irr (left  p) (left  q) = left & <-irrelevant _ _
-- --   <-irr (left  p) (right q) = ⊥-elim (<-irrefl refl p)
-- --   <-irr (right p) (left q)  = ⊥-elim (<-irrefl refl q)
-- --   <-irr (right p) (right q) = right & <-irrelevant _ _

-- --   univ : Univ
-- --   univ = record {
-- --       Lvl = N.ℕ × N.ℕ
-- --     ; _<_ = _<_
-- --     ; trs = trs
-- --     ; wf  = wellFounded <-wellFounded <-wellFounded _
-- --     ; ass = λ p q r → <-irr _ _
-- --     }

-- --   open IRU univ

-- --   -- raise small level
-- --   <suc : ∀ {i j} → (i , j) < (i , N.suc j)
-- --   <suc {i} = right ≤-refl

-- --   -- raise large level (raise to closest limit level)
-- --   <Suc : ∀ {i} j → (i , j) < (N.suc i , 0)
-- --   <Suc {i} j = left ≤-refl

-- --   ω : Lvl
-- --   ω = 1 , 0

-- --   #_ : N.ℕ → Lvl; infix 10 #_
-- --   # n = 0 , n

-- --   _+_ : Lvl → Lvl → Lvl; infix 6 _+_
-- --   (i , j) + (i' , j') = i N.+ i' , j N.+ j'

-- --   idω : El {ω} (Π' ℕ' λ i → Π' (U' (<Suc i)) λ A → ↑U (<Suc i) A ⇒' ↑U (<Suc i) A)
-- --   idω i A x = x

-- --   idω' : El {ω} (Π' L' λ i → Π' (i <' ω) λ p → Π' (U' p) λ A → ↑U p A ⇒' ↑U p A)
-- --   idω' _ p A x = x

-- --   idω+1 : El {ω + # 1} ((Π' L' λ i → Π' (i <' ω + # 1) λ p → Π' (U' p) λ A → ↑U p A ⇒' ↑U p A))
-- --   idω+1 i p A x = x

-- --   -- we can't compute past ↑U nicely
-- --   call = idω+1 ω <suc (Π' ℕ' λ i → Π' (U' (<Suc i)) λ A → ↑U (<Suc i) A ⇒' ↑U (<Suc i) A)
-- --                  {!!}
