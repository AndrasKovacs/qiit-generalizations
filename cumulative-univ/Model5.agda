{-# OPTIONS --without-K  #-}

open import Data.Empty
open import Data.Nat
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl x = x
ap = cong
_◾_ = trans; infixr 4 _◾_
_⁻¹ = sym; infix 6 _⁻¹

-- function extensionality
postulate
  ext : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
        → ((x : A) → f x  ≡ g x) → f ≡ g

-- "ordinals"
--------------------------------------------------------------------------------

data O : Set where
  zero : O
  suc  : O → O
  lim  : (ℕ → O) → O

infix 4 _∈_
_∈_ : O → O → Set
i ∈ zero  = ⊥
i ∈ suc j = i ≡ j ⊎ i ∈ j
i ∈ lim f = ∃ λ n → i ≡ f n ⊎ i ∈ f n

trs : ∀ {i j k} → i ∈ j → j ∈ k → i ∈ k
trs {k = suc k} p (inj₁ refl)     = inj₂ p
trs {k = suc k} p (inj₂ q)        = inj₂ (trs p q)
trs {k = lim f} p (n , inj₁ refl) = n , inj₂ p
trs {k = lim f} p (n , inj₂ q)    = n , inj₂ (trs p q)

--------------------------------------------------------------------------------

Lvl : O → Set₁
Lvl i = ∀ {j} → j ∈ i → Set

infix 4 _∈'_

data UU {i}(l : Lvl i) : Set
EL : ∀ {i}{l : Lvl i} → UU l → Set

data UU {i} l where
  U'    : ∀ {j} → j ∈ i → UU l
  ℕ' O' : UU l
  _∈'_  : O → O → UU l
  Π' Σ' : (a : UU l) → (EL a → UU l) → UU l

EL {_}{l}(U' p) = l p
EL ℕ'           = ℕ
EL O'           = O
EL (i ∈' j)     = i ∈ j
EL (Π' a b)     = ∀ x → EL (b x)
EL (Σ' a b)     = ∃ λ x → EL (b x)

lvl : ∀ i → Lvl i
lvl (suc i) (inj₁ refl)     = UU (lvl i)
lvl (suc i) (inj₂ p)        = lvl i p
lvl (lim f) (n , inj₁ refl) = UU (lvl (f n))
lvl (lim f) (n , inj₂ p)    = lvl (f n) p

-- actually, only the lowest index matters!
lvl↑ : ∀ {i j k}(p : i ∈ j)(q : k ∈ i) → lvl j {k} (trs q p) ≡ lvl i {k} q
lvl↑ {j = suc j} (inj₁ refl)     q = refl
lvl↑ {j = suc j} (inj₂ p)        q = lvl↑ p q
lvl↑ {j = lim f} (n , inj₁ refl) q = refl
lvl↑ {j = lim f} (n , inj₂ p)    q = lvl↑ p q

U : O → Set
U i = UU (lvl i)

El : ∀ {i} → U i → Set
El = EL

↑   : ∀ {i j} → i ∈ j → U i → U j
El↑ : ∀ {i j} p a → El (↑ {i}{j} p a) ≡ El a
↑   p (U' q)   = U' (trs q p)
↑   p ℕ'       = ℕ'
↑   p O'       = O'
↑   p (i ∈' j) = i ∈' j
↑   p (Π' a b) = Π' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
↑   p (Σ' a b) = Σ' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
El↑ p (U' q)   = lvl↑ p q
El↑ p ℕ'       = refl
El↑ p O'       = refl
El↑ p (i ∈' j) = refl
El↑ p (Π' a b) rewrite El↑ p a = ap (λ f → ∀ x → f x) (ext (El↑ p ∘ b))
El↑ p (Σ' a b) rewrite El↑ p a = ap ∃ (ext (El↑ p ∘ b))

--------------------------------------------------------------------------------

lem : ∀ {i j}(p : i ∈ j) → lvl j p ≡ U i
lem {j = suc j} (inj₁ refl    ) = refl
lem {j = suc j} (inj₂ p       ) = lem {j = j} p
lem {j = lim f} (n , inj₁ refl) = refl
lem {j = lim f} (n , inj₂ p   ) = lem {j = f n} p

-- only the lowest level determines lvl
lvl-irr : ∀ {i j k p p'} → lvl j {k} p' ≡ lvl i {k} p
lvl-irr {i} {j} {k} {p} {p'} = lem p' ◾ lem p ⁻¹

-- _∈_ is irrelevant in lvl, but not in ↑

↑' : ∀ {i j}(p : i ∈ j) → lvl j p → U j
↑' p a = ↑ p (coe (lem p) a)

-- examples
--------------------------------------------------------------------------------

#_ : ℕ → O; infix 10 #_
# zero  = zero
# suc n = suc (# n)

∈suc : ∀ i → i ∈ suc i
∈suc i = inj₁ refl

ω : O
ω = lim #_

n∈ω : ∀ n → # n ∈ ω
n∈ω n = n , inj₁ refl

_⇒'_ : ∀ {i}{l : Lvl i} → UU l → UU l → UU l
a ⇒' b = Π' a λ _ → b
infixr 3 _⇒'_

_×'_ : ∀ {i}{l : Lvl i} → UU l → UU l → UU l
a ×' b = Σ' a λ _ → b
infixr 4 _×'_

idω : El {ω} (Π' ℕ' λ n → Π' (U' (n∈ω n)) λ A → ↑ (n∈ω n) A ⇒' ↑ (n∈ω n) A)
idω i A x = x

idω' : El {ω} (Π' O' λ i → Π' (i ∈' ω) λ p → Π' (U' p) λ A → ↑' p A  ⇒' ↑' p A)
idω' i p A x = x

id1+ω : El {suc ω} (Π' (U' (∈suc ω)) λ A → ↑ (∈suc ω) A ⇒' ↑ (∈suc ω) A)
id1+ω A x = x

idℕ : ℕ → ℕ
idℕ = idω 0 ℕ'

idℕ' : ℕ → ℕ
idℕ' = idω' (# 0) (n∈ω 0) ℕ'

foo : ℕ → ℕ
foo = id1+ω (Π' ℕ' λ n → Π' (U' (n∈ω n)) λ A → ↑ (n∈ω n) A ⇒' ↑ (n∈ω n) A)
            (λ _ _ x → x) 0 ℕ'

--------------------------------------------------------------------------------

_+ₒ_ : O → O → O; infixl 6 _+ₒ_
zero  +ₒ j = j
suc i +ₒ j = suc (i +ₒ j)
lim f +ₒ j = lim (λ n → f n +ₒ j)

_*ₒ_ : O → O → O; infixl 7 _*ₒ_
zero  *ₒ j = zero
suc i *ₒ j = j +ₒ i *ₒ j
lim f *ₒ j = lim (λ n → f n *ₒ j)

exp : O → O → O
exp i zero    = # 1
exp i (suc j) = i *ₒ exp i j
exp i (lim f) = lim (λ n → exp i (f n))

natrec : ∀ {α}{A : Set α} → (A → A) → A → ℕ → A
natrec s z zero    = z
natrec s z (suc n) = s (natrec s z n)

ε₀ : O
ε₀ = lim (natrec (flip exp ω) ω)
