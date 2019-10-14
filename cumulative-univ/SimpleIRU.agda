
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Sum
open import Function hiding (id; _∘_)
import Function as F
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

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

------------------------------------------------------------

-- simple version: finite levels, non-Russell (cumulative)

open import Data.Nat hiding (_<_)

Lvl : Set₁
Lvl = Σ Set λ U → (U → Set)

data UU (l : Lvl) : Set
EL : ∀ {l} → UU l → Set

data UU l where
  ℕ'  : UU l
  U'  : UU l
  Π'  : (a : UU l) → (EL a → UU l) → UU l
  El' : l .₁ → UU l

EL ℕ'          = ℕ
EL {l} U'      = l .₁
EL {l} (El' a) = l .₂ a
EL (Π' a b)    = ∀ x → EL (b x)

U   : ℕ → Set
U↓  : ℕ → Set
El↓ : ∀ {i} → U↓ i → Set
U n           = UU (U↓ n , El↓ {n})
U↓ zero       = ⊥
U↓ (suc n)    = U n
El↓ {suc i} a = EL a

El : ∀ {i} → U i → Set
El = EL

--------------------------------------------------------------------------------

infix 3 _<_
data _<_ : ℕ → ℕ → Set where
  here  : ∀ {n} → n < suc n
  there : ∀ {n m} → n < m → n < suc m

<-trs : ∀ {i j k} → i < j → j < k → i < k
<-trs p here      = there p
<-trs p (there q) = there (<-trs p q)

<-pred : ∀ {i j} → suc i < j → i < j
<-pred here = there here
<-pred (there p) = there (<-pred p)

<-irrefl : ∀ {i} → i < i → ⊥
<-irrefl (there p) = <-irrefl (<-pred p)

<-prop : ∀ {i j}{p q : i < j} → p ≡ q
<-prop {p = here}    {here}    = refl
<-prop {p = here}    {there q} = ⊥-elim (<-irrefl q)
<-prop {p = there p} {here}    = ⊥-elim (<-irrefl p)
<-prop {p = there p} {there q} = there & <-prop

--------------------------------------------------------------------------------

↑ : ∀ {i j} → i < j → U i → U j
↑ here      a = El' a
↑ (there p) a = El' (↑ p a)

El↑ : ∀ {i j a p} → El {i} a ≡ El {j} (↑ p a)
El↑ {p = here}    = refl
El↑ {p = there p} = El↑ {p = p}

↑↑ : ∀ {i j k}{p : i < j}{q : j < k}{a} → ↑ q (↑ p a) ≡ ↑ (<-trs p q) a
↑↑ {p = p} {here}    {a} = refl
↑↑ {p = p} {there q} {a} = El' & ↑↑ {p = p}{q} {a}

--------------------------------------------------------------------------------

Con : Set₁
Con = Set

Ty : Con → ℕ → Set
Ty Γ j = Γ → U j

↑Ty : ∀ {Γ i j} → i < j → Ty Γ i → Ty Γ j
↑Ty p A γ = ↑ p (A γ)

Tm : ∀ (Γ : Con){j} → Ty Γ j → Set
Tm Γ A = (γ : Γ) → El (A γ)

Cumulative : ∀ {Γ i j}{p : i < j}{A : Ty Γ i} → Tm Γ A ≡ Tm Γ (↑Ty p A)
Cumulative {p = here}    = refl
Cumulative {p = there p} = Cumulative {p = p}

Sub : Con → Con → Set
Sub Γ Δ = Γ → Δ

id : ∀ {Γ} → Sub Γ Γ
id γ = γ

infixr 5 _∘_
_∘_ : ∀ {Γ Δ θ} → Sub Δ θ → Sub Γ Δ → Sub Γ θ
(σ ∘ δ) γ = σ (δ γ)

ass : ∀ {Γ Δ θ Ξ}{σ : Sub θ Ξ}{δ}{ν : Sub Γ Δ} → (σ ∘ δ) ∘ ν ≡ σ ∘ δ ∘ ν
ass = refl

idl : ∀ {Γ Δ}{σ : Sub Γ Δ} → id ∘ σ ≡ σ
idl = refl

idr : ∀ {Γ Δ}{σ : Sub Γ Δ} → σ ∘ id ≡ σ
idr = refl

∙ : Con
∙ = ⊤

ε : ∀ {Γ} → Sub Γ ∙
ε = _

εη : ∀ {Γ σ} → σ ≡ ε {Γ}
εη = refl

infixl 5 _[_]T
_[_]T : ∀ {Γ Δ i} → Ty Δ i → Sub Γ Δ → Ty Γ i
A [ σ ]T = λ γ → A (σ γ)

[id]T : ∀ {Γ i}{A : Ty Γ i} → A [ id {Γ} ]T ≡ A
[id]T {Γ}{i}{A} = refl

[∘]T : ∀{i}{Θ : Con}{Δ : Con}{σ : Sub Θ Δ}{Γ : Con}{δ : Sub Γ Θ}
        {A : Ty Δ i} → A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T
[∘]T = refl


infixl 5 _[_]t
_[_]t : ∀ {Γ Δ i A} → Tm Δ {i} A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t t σ γ = t (σ γ)

[id]t : ∀ {Γ i}{A : Ty Γ i}{t : Tm Γ A} → _[_]t {Γ}{Γ}{i}{A} t (id {Γ}) ≡ t
[id]t = refl

[∘]t : ∀{i}{Θ : Con}{Δ : Con}{σ : Sub Θ Δ}{Γ : Con}{δ : Sub Γ Θ}
        {A : Ty Δ i}{t : Tm Δ A} → {!_[_]t!} ≡ _[_]t {A = A} t (σ ∘ δ)
[∘]t = {!!}


infixl 3 _▶_
_▶_ : (Γ : Con) → ∀ {i} → Ty Γ i → Con
Γ ▶ A = Σ Γ λ γ → El (A γ)

p : ∀ {Γ i}{A : Ty Γ i} → Sub (Γ ▶ A) Γ
p = ₁

q : ∀ {Γ i}{A : Ty Γ i} → Tm (Γ ▶ A) {i} (_[_]T {Γ ▶ A}{Γ}{i} A (p {Γ}{i}{A}))
q = ₂

u : ∀ {Γ i j} → i < j → Ty Γ j
u here      γ = U'
u (there p) γ = El' (u p γ)

↑u : ∀ {Γ}{i j k}{p : i < j}{q : j < k} → ↑Ty q (u {Γ}{i}{j} p) ≡ u {Γ}{i}{k} (<-trs p q)
↑u {q = here}    = refl
↑u {q = there q} = (El' F.∘_) & ↑u

Russell : ∀ {i j Γ p} → Ty Γ i ≡ Tm Γ (u {Γ}{i}{j} p)
Russell {p = here}    = refl
Russell {p = there p} = Russell {p = p}



-- ▶↑ : ∀ {i Γ}{A : Ty Γ i} → (Γ ▶ A) ≡ (Γ ▶ Ty↑ A)
-- ▶↑ = refl

-- Π : ∀ {i}{Γ : Con}(A : Ty Γ i) → Ty (Γ ▶ A) i → Ty Γ i
-- Π {i} {Γ} A B γ = Π' (A γ) λ x → B (γ , x)

-- ------------------------------------------------------------

-- -- interpret rules in this paper:
-- -- https://arxiv.org/abs/1902.08848





-- -- ω*ω + Russell + cumulative + level polymorphism
-- -- std model, canonicity









-- -- data UU (i : ℕ) : Set
-- -- EL : ∀ {i} → UU i → Set

-- -- data UU i where
-- --   ℕ'  : UU i
-- --   U'  : UU i
-- --   Π'  : (a : UU i) → (EL a → UU i) → UU i

-- -- EL ℕ' = ℕ
-- -- EL {zero} U' = ⊥
-- -- EL {suc i} U' = UU i
-- -- EL (Π' a b) = {!!}
