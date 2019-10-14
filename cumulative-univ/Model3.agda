
{-# OPTIONS --rewriting #-}

open import StrictLib
  renaming (zero to lzero; suc to lsuc)
  hiding (lift; _⊔_; Lift; lower)

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool
open import Data.List hiding (lookup)
open import Data.Fin

data Pos {α}{A : Set α} : List A → Set where
  zero : ∀ {x xs} → Pos (x ∷ xs)
  suc  : ∀ {x xs} → Pos xs → Pos (x ∷ xs)

↓1 : ∀ {α A x xs} → Pos {α}{A} (x ∷ xs)
↓1 = zero

↓2 : ∀ {α A a b xs} → Pos {α}{A} (a ∷ b ∷ xs)
↓2 = suc zero

↓3 : ∀ {α A a b c xs} → Pos {α}{A} (a ∷ b ∷ c ∷ xs)
↓3 = suc (suc zero)

↓4 : ∀ {α A a b c d xs} → Pos {α}{A} (a ∷ b ∷ c ∷ d ∷ xs)
↓4 = suc (suc (suc zero))

lookup : ∀ {α}{A : Set α}{xs : List A} → Pos xs → A
lookup (zero {x}) = x
lookup (suc x)    = lookup x

--------------------------------------------------------------------------------

Lvl : Set₁
Lvl = List Set

data UU (l : Lvl) : Set
EL : ∀ {l} → UU l → Set

data UU l where
  U'       : Pos l → UU l
  Bool' ⊤' : UU l
  Π' Σ'    : (a : UU l) → (EL a → UU l) → UU l

EL (U' x)   = lookup x
EL Bool'    = Bool
EL ⊤'       = ⊤
EL (Π' a b) = ∀ x → EL (b x)
EL (Σ' a b) = ∃ λ x → EL (b x)

lvl : ℕ → Lvl
lvl zero    = []
lvl (suc n) = let A = lvl n in UU A ∷ A

U : ℕ → Set
U n = UU (lvl n)

El : ∀ {n} → U n → Set
El = EL

--------------------------------------------------------------------------------

↑   : ∀ {i} → U i → U (suc i)
El↑ : ∀ {i}(a : U i) → El (↑ a) ≡ El a
↑ (U' x)   = U' (suc x)
↑ Bool'    = Bool'
↑ ⊤'       = ⊤'
↑ (Π' a b) = Π' (↑ a) λ x → ↑ (b (coe (El↑ a) x))
↑ (Σ' a b) = Σ' (↑ a) λ x → ↑ (b (coe (El↑ a) x))
El↑ (U' x)   = refl
El↑ Bool'    = refl
El↑ ⊤'       = refl
El↑ (Π' a b) rewrite El↑ a = (λ f → ∀ x → f x) & ext (El↑ ∘ b)
El↑ (Σ' a b) rewrite El↑ a = ∃ & ext (El↑ ∘ b)

postulate
 suc⊔ : ∀ i j → suc i ⊔ j ≡ suc (i ⊔ j)
{-# REWRITE suc⊔ #-}

⊔↑ : ∀ {i} j → U i → U (j ⊔ i)
⊔↑ zero    a = a
⊔↑ (suc j) a = ↑ (⊔↑ j a)

↑⊔ : ∀ {i} → U i → ∀ j → U (i ⊔ j)
↑⊔ {i} a j = tr U (⊔-comm i j ⁻¹) (⊔↑ j a)

postulate
  El↑⊔ : ∀ {i} a j → El (↑⊔ {i} a j) ≡ El a

--------------------------------------------------------------------------------

_⇒'_ : ∀ {i} → U i → U i → U i
a ⇒' b = Π' a λ _ → b
infixr 3 _⇒'_

_×'_ : ∀ {i} → U i → U i → U i
a ×' b = Σ' a λ _ → b
infixr 4 _×'_

id' : ∀ i → El {suc i} (Π' (U' ↓1) λ A → ↑ A ⇒' ↑ A)
id' i A x = x

--------------------------------------------------------------------------------

Con : Set
Con = ∃ U

Ty : Con → ℕ → Set
Ty (i , Γ) j = El Γ → U j

Sub : Con → Con → Set
Sub (_ , Γ) (_ , Δ) = El Γ → El Δ

Tm : (Γ : Con) → ∀ {j} → Ty Γ j → Set
Tm (i , Γ) {j} A = (γ : El Γ) → El (A γ)

↑T : ∀ {Γ i} → Ty Γ i → Ty Γ (suc i)
↑T {i , Γ}{j} A γ = ↑ (A γ)

↑Tm : ∀ {Γ i}{A : Ty Γ i} → Tm Γ (↑T {Γ}{i} A) ≡ Tm Γ A
↑Tm {i , Γ} {j} {A} = (λ f → ∀ x → f x) & ext λ γ → El↑ (A γ)

infixl 4 _▶_
_▶_ : (Γ : Con) → ∀ {j} → Ty Γ j → Con
_▶_ (i , Γ) {j} A = i ⊔ j , Σ' (↑⊔ Γ j) λ x → ⊔↑ i (A (coe (El↑⊔ Γ j) x))

-- does not work! Perhaps only works with U ω
↑▶ : ∀ {Γ : Con}{i}{A : Ty Γ i} → (Γ ▶ A) ≡ (Γ ▶ ↑T {Γ}{i} A)
↑▶ {i , Γ} {j} {A} = {!!}

Pi : ∀ {Γ}{i}(A : Ty Γ i) → Ty (Γ ▶ A) i → Ty Γ i
Pi {i , Γ}{j} A B γ =
  -- coercion hell but plausible
  Π' (A γ) (λ x → B ((coe (El↑ Γ ⁻¹ ◾ {!!}) γ) , {!x!}))


-- question: when do we *not* get coercion hell?

-- Semantic U has homogeneous type operators!
-- If we only use homogeneous type operators, then everything is fine
-- But: we don't get russell univs or even univs easily!


-- Con : ℕ → Set
-- Con = U

-- Ty : ∀ {i} → Con i → Set
-- Ty {i} Γ = El Γ → U i

-- Sub : ∀ {i} → Con i → Con i → Set
-- Sub {i} Γ Δ = El Γ → El Δ

-- Tm : ∀ {i}(Γ : Con i) → Ty Γ → Set
-- Tm {i} Γ A = (γ : El Γ) → El (A γ)

-- ∙ : ∀ {i} → Con i
-- ∙ = ⊤'

-- infixl 3 _▶_
-- _▶_ : ∀ {i}(Γ : Con i) → Ty Γ → Con i
-- _▶_ = Σ'

-- infix 4 _[_]T
-- _[_]T : ∀ {i Γ Δ}(A : Ty {i} Δ)(σ : Sub Γ Δ) → Ty Γ
-- _[_]T A σ γ = A (σ γ)

-- FinToPos : ∀ {i} → Fin i → Pos (lvl i)
-- FinToPos zero    = zero
-- FinToPos (suc x) = suc (FinToPos x)

-- -- No Russell univ with this indexing!
-- u : ∀ {i}{Γ : Con i} → Fin i → Ty Γ
-- u {i}{Γ} x _ = U' (FinToPos x)

-- subFin : ∀ {i} → Fin i → ℕ
-- subFin {suc n} zero    = n
-- subFin {suc n} (suc x) = subFin {n} x

-- lookupFinToPos : ∀ {i} x → lookup (FinToPos {i} x) ≡ UU (lvl (subFin x))
-- lookupFinToPos zero    = refl
-- lookupFinToPos (suc x) = lookupFinToPos x

-- el : ∀ {i}{Γ : Con i}{x} → Tm Γ (u {i}{Γ} x) → Ty Γ
-- el {i}{Γ}{x} a γ = {!coe (lookupFinToPos x) (a γ)!}
--   -- we still need to lift this back to i..

-- c : Ty (↑ Γ) → Tm Γ (n



-- -- NO RUSSELL with this indexing!
-- -- Russell : ∀ {i}{Γ : Con i}{x : Fin i} → Tm Γ (u x) ≡ Ty Γ
-- -- {j}{x : Fin j} → Tm {i} Γ (u {i}{Γ} j x) ≡ Ty Γ (subFin x)


-- -- u : ∀ {i}{Γ : Con i} → ∀ j → Fin j → Ty Γ j
-- -- u j x _ = U' (FinToPos x)

-- -- Russell : ∀ {i}{Γ : Con i}{j}{x : Fin j} → Tm {i} Γ (u {i}{Γ} j x) ≡ Ty Γ (subFin x)
-- -- Russell {i} {Γ} {j} {x} = (λ x → El Γ → x) & lookupFinToPos x

-- -- Pi : ∀ {i j}{Γ : Con i}(A : Ty Γ j) → Ty (↑⊔ Γ j ▶ ⊔↑T A) j → Ty Γ j


-- let's index Con and Ty

-- Con : ℕ → Set
-- Con = U

-- Ty : ∀ {i} → Con i → ℕ → Set
-- Ty {i} Γ j = El Γ → U j

-- ↑T : ∀ {i j}{Γ : Con i} → Ty Γ j → Ty Γ (suc j)
-- ↑T A γ = ↑ (A γ)

-- Ty↑Γ : ∀ {i j Γ} → Ty {suc i} (↑ Γ) j ≡ Ty Γ j
-- Ty↑Γ {i} {j}{Γ} = (λ a b → a → b) & El↑ Γ ⊗ refl

-- -- this one is derivable
-- ↑T' : ∀ {i j}{Γ : Con i} → Ty Γ j → Ty (↑ Γ) (suc j)
-- ↑T' {i}{j}{Γ} A γ = ↑ (A (coe (El↑ Γ) γ))

--  -- let A' : Ty (↑ Γ) j
--  --     A' = coe (Ty↑Γ {i}{j}{Γ} ⁻¹) A
--  -- in ↑T {suc i}{j}{↑ Γ} A'

-- ⊔↑T : ∀ {i Γ j} → Ty {i} Γ j → Ty (↑⊔ Γ j) (i ⊔ j)
-- ⊔↑T {i}{Γ}{j} A γ = ⊔↑ i (A (coe (El↑⊔ {i} Γ j) γ))

-- Sub : ∀ {i} → Con i → ∀ {j} → Con j → Set
-- Sub Γ Δ = El Γ → El Δ

-- Sub↑ΓΔ : ∀ {i Γ j Δ} → Sub (↑ {i} Γ) (↑ {j} Δ) ≡ Sub Γ Δ
-- Sub↑ΓΔ {i}{Γ}{j}{Δ} = (λ a b → a → b) & El↑ Γ ⊗ El↑ Δ

-- Tm : ∀ {i}(Γ : Con i){j} → Ty Γ j → Set
-- Tm Γ A = (γ : El Γ) → El (A γ)

-- Tm↑ΓA : ∀ {i}{Γ : Con i}{j}{A : Ty Γ j}
--   → Tm {suc i} (↑ Γ){suc j} (↑T' {i}{j}{Γ} A) ≡ Tm Γ A
-- Tm↑ΓA {i} {Γ} {j} {A} rewrite El↑ Γ =
--   (λ f → ∀ x → f x) & ext λ γ → El↑ (A γ)

-- ∙ : ∀ {i} → Con i
-- ∙ = ⊤'

-- infixl 3 _▶_
-- _▶_ : ∀ {i}(Γ : Con i) → Ty Γ i → Con i
-- _▶_ = Σ'

-- infix 4 _[_]T
-- _[_]T : ∀ {i Γ j Δ k}(A : Ty {j} Δ k)(σ : Sub Γ Δ) → Ty {i} Γ k
-- _[_]T A σ γ = A (σ γ)

-- FinToPos : ∀ {i} → Fin i → Pos (lvl i)
-- FinToPos zero    = zero
-- FinToPos (suc x) = suc (FinToPos x)

-- subFin : ∀ {i} → Fin i → ℕ
-- subFin {suc n} zero    = n
-- subFin {suc n} (suc x) = subFin {n} x

-- lookupFinToPos : ∀ {i} x → lookup (FinToPos {i} x) ≡ UU (lvl (subFin x))
-- lookupFinToPos zero    = refl
-- lookupFinToPos (suc x) = lookupFinToPos x

-- u : ∀ {i}{Γ : Con i} → ∀ j → Fin j → Ty Γ j
-- u j x _ = U' (FinToPos x)

-- Russell : ∀ {i}{Γ : Con i}{j}{x : Fin j} → Tm {i} Γ (u {i}{Γ} j x) ≡ Ty Γ (subFin x)
-- Russell {i} {Γ} {j} {x} = (λ x → El Γ → x) & lookupFinToPos x

-- Pi : ∀ {i j}{Γ : Con i}(A : Ty Γ j) → Ty (↑⊔ Γ j ▶ ⊔↑T A) j → Ty Γ j
-- Pi {i}{j}{Γ} A B γ = Π' (A γ) (λ x → B ((coe {!!} γ) , coe {!!} x))
--   -- a bit awful


-- Con : ℕ → Set
-- Con = U

-- -- LiftC : ∀ {i} → Con i → Con (suc i)
-- -- LiftC Γ = ↑ Γ

-- Ty : ∀ {i} → Con i → ℕ → Set
-- Ty {i} Γ j = El Γ → U j

-- Sub : ∀ {i} → Con i → Con i → Set
-- Sub Γ Δ = El Γ → El Δ

-- Tm : ∀ {i}(Γ : Con i){j} → Ty Γ j → Set
-- Tm Γ A = (γ : El Γ) → El (A γ)

-- ∙ : ∀ {i} → Con i
-- ∙ = ⊤'

-- infixl 3 _▶_
-- _▶_ : ∀ {i}(Γ : Con i) → Ty Γ i → Con i
-- _▶_ = Σ'

-- infix 4 _[_]T
-- _[_]T : ∀ {i Γ Δ}(A : Ty {i} Δ i)(σ : Sub Γ Δ) → Ty Γ i
-- _[_]T A σ γ = A (σ γ)

-- FinToPos : ∀ {i} → Fin i → Pos (lvl i)
-- FinToPos zero    = zero
-- FinToPos (suc x) = suc (FinToPos x)

-- subFin : ∀ {i} → Fin i → ℕ
-- subFin {suc n} zero    = n
-- subFin {suc n} (suc x) = subFin {n} x

-- lookupFinToPos : ∀ {i} x → lookup (FinToPos {i} x) ≡ UU (lvl (subFin x))
-- lookupFinToPos zero    = refl
-- lookupFinToPos (suc x) = lookupFinToPos x

-- u : ∀ {i}{Γ : Con i} → ∀ j → Fin j → Ty Γ j
-- u j x _ = U' (FinToPos x)

-- Russell : ∀ {i}{Γ : Con i}{j}{x : Fin j} → Tm {i} Γ (u {i}{Γ} j x) ≡ Ty Γ (subFin x)
-- Russell {i} {Γ} {j} {x} = (λ x → El Γ → x) & lookupFinToPos x

-- Pi : ∀ {i j}{Γ : Con i}(A : Ty Γ j) → Ty (Γ ▶ {!!}) j → Ty Γ j






-- open import Data.Fin hiding (lift)
-- open import Data.Vec

-- Lvl : Set₁
-- Lvl = Σ ℕ λ n → Fin n → Set

-- data UU (l : Lvl) : Set
-- El : ∀ {l} → UU l → Set

-- data UU l where
--   U'    : Fin (l .₁) → UU l
--   Bool' : UU l
--   Π' Σ' : (a : UU l) → (El a → UU l) → UU l

-- El {l} (U' i) = l .₂ i
-- El Bool'      = Bool
-- El (Π' a b)   = ∀ x → El (b x)
-- El (Σ' a b)   = ∃ λ x → El (b x)

-- U   : ℕ → Set
-- ↓El : ∀ n → Fin n → Set
-- U n = UU (n , ↓El n)
-- ↓El (suc n) zero    = UU (0 , (λ ()))
-- ↓El (suc n) (suc x) = UU ((toℕ (suc x)) , {!↓El n!})






-- U   : ℕ → Set
-- ↓U  : ℕ → Set
-- U n = UU ({!!} , {!!})
-- U n         = UU (↓U n , ↓El {n})
-- ↓U zero     = ⊥
-- ↓U (suc n)  = U n
-- ↓El {suc n} = El {↓U n , ↓El {n}}

-- Lift  : ∀ {i} → U i → U (suc i)
-- lift  : ∀ {i}(a : U i) → El a ≡ El (Lift a)
-- Lift U'              = U'
-- Lift Bool'           = Bool'
-- Lift (Π' a b)        = Π' (Lift a) λ x → Lift (b (coe (lift a ⁻¹) x))
-- Lift (Σ' a b)        = Σ' (Lift a) λ x → Lift (b (coe (lift a ⁻¹) x))
-- Lift {suc i} (El' a) = El' (Lift a)
-- lift {i} U' = {!!}        -- ISSUE, we don't have U i in a larger universe!!
-- lift Bool' = refl
-- lift (Π' a b) rewrite lift a = (λ f → ∀ x   → f x) & ext (lift ∘ b)
-- lift (Σ' a b) rewrite lift a = (λ f → ∃ λ x → f x) & ext (lift ∘ b)
-- lift {suc i} (El' a) = lift a

-- Lvl : Set₁
-- Lvl = Σ Set λ A → A → Set

-- data UU (l : Lvl) : Set
-- El : ∀ {l} → UU l → Set

-- data UU l where
--   U' Bool' : UU l
--   Π' Σ'    : (a : UU l) → (El a → UU l) → UU l
--   El'      : l .₁ → UU l

-- El {l} U'      = l .₁
-- El Bool'       = Bool
-- El (Π' a b)    = (x : El a) → El (b x)
-- El (Σ' a b)    = ∃ λ (x : El a) → El (b x)
-- El {l} (El' a) = l .₂ a

-- U   : ℕ → Set
-- ↓U  : ℕ → Set
-- ↓El : ∀ {n} → ↓U n → Set
-- U n         = UU (↓U n , ↓El {n})
-- ↓U zero     = ⊥
-- ↓U (suc n)  = U n
-- ↓El {suc n} = El {↓U n , ↓El {n}}

-- Lift  : ∀ {i} → U i → U (suc i)
-- lift  : ∀ {i}(a : U i) → El a ≡ El (Lift a)
-- Lift U'              = U'
-- Lift Bool'           = Bool'
-- Lift (Π' a b)        = Π' (Lift a) λ x → Lift (b (coe (lift a ⁻¹) x))
-- Lift (Σ' a b)        = Σ' (Lift a) λ x → Lift (b (coe (lift a ⁻¹) x))
-- Lift {suc i} (El' a) = El' (Lift a)
-- lift {i} U' = {!!}        -- ISSUE, we don't have U i in a larger universe!!
-- lift Bool' = refl
-- lift (Π' a b) rewrite lift a = (λ f → ∀ x   → f x) & ext (lift ∘ b)
-- lift (Σ' a b) rewrite lift a = (λ f → ∃ λ x → f x) & ext (lift ∘ b)
-- lift {suc i} (El' a) = lift a


-- Lift  : ∀ {i} → U i → U (suc i)
-- lift  : ∀ {i}(a : U i) → El a → El (Lift a)
-- lower : ∀ {i}(a : U i) → El (Lift a) → El a
-- io    : ∀ {i}(a : U i) x → lift a (lower a x) ≡ x
-- oi    : ∀ {i}(a : U i) x → lower a (lift a x) ≡ x
-- Lift U'                = U'
-- Lift Bool'             = Bool'
-- Lift (Π' a b)          = Π' (Lift a) λ x → Lift (b (lower a x))
-- Lift (Σ' a b)          = Σ' (Lift a) λ x → Lift (b (lower a x))
-- Lift (El' a)           = El' (lift U' a)
-- lift {suc i} U' t      = Lift t
-- lift Bool' t           = t
-- lift (Π' a b) t        = λ x → lift (b (lower a x)) (t (lower a x))
-- lift (Σ' a b) t        = (lift a (t .₁))
--                        , lift (b (lower a (lift a (t .₁))))
--                               (tr (El ∘ b) (oi a (t .₁) ⁻¹) (t .₂))
-- lift {suc i} (El' a) t = lift a t


-- Liftr   : ∀ {i j} → U i → U (i ⊔ j)
-- Liftl   : ∀ {i j} → U j → U (i ⊔ j)
-- liftr   : ∀ {i j}(a : U i) → El a → El (Liftr {i}{j} a)
-- unliftr : ∀ {i j}(a : U i) → El (Liftr {i}{j} a) → El a
-- liftl   : ∀ {i j}(a : U j) → El a → El (Liftl {i}{j} a)
-- unliftl : ∀ {i j}(a : U j) → El (Liftl {i}{j} a) → El a

-- Liftr U'       = U'
-- Liftr Bool'    = Bool'
-- Liftr (Π' a b) = Π' (Liftr a) λ x → Liftr (b (unliftr a x))
-- Liftr (Σ' a b) = Σ' (Liftr a) λ x → Liftr (b (unliftr a x))
-- Liftr (El' a)  = El' (liftr U' a)
-- Liftl U'       = U'
-- Liftl Bool'    = Bool'
-- Liftl (Π' a b) = Π' (Liftl a) (λ x → Liftl (b (unliftl a x)))
-- Liftl (Σ' a b) = Σ' (Liftl a) (λ x → Liftl (b (unliftl a x)))
-- Liftl (El' a)  = El' (liftl U' a)

-- liftr U'       t = {!!}
-- liftr Bool'    t = t
-- liftr (Π' a b) t = λ x → {!!}
-- liftr (Σ' a b) t = {!!}
-- liftr (El' a)  t = {!!}
-- unliftr = {!!}
-- liftl   = {!!}
-- unliftl = {!!}

--------------------------------------------------------------------------------

-- Con : ℕ → Set
-- Con = U

-- Ty : ∀ {i} → Con i → ℕ → Set
-- Ty {i} Γ j = El Γ → U j

-- Sub : ∀ {i} → Con i → ∀ {j} → Con j → Set
-- Sub Γ Δ = El Γ → El Δ

-- Tm : ∀ {i}(Γ : Con i) → ∀ {j} → Ty Γ j → Set
-- Tm Γ A = (γ : El Γ) → El (A γ)

-- -- infixl 3 _▶_
-- -- _▶_ : ∀ {i}(Γ : Con i){j} → Ty Γ j → Con (i ⊔ j)
-- -- _▶_ {i} Γ {j} A = Σ' (Liftr Γ) (λ γ → Liftl (A (unliftr {i}{j} Γ γ)))

-- u : ∀ {j}{Γ : Con j} i → Ty Γ (suc i)
-- u i _ = U'

-- russell : ∀ {i}{Γ : Con i}{j} → Tm Γ (u {_}{Γ}j) ≡ Ty Γ j
-- russell = refl

-- Π : ∀ {i}{Γ : Con i}{j}(A : Ty Γ j) → {!Ty (!} → {!!}


-- --------------------------------------------------------------------------------

-- El : ∀ i → U i → Set
-- El i = EL {↓U i , ↓El}

-- _⇒'_ : ∀ {l} → UU l → UU l → UU l
-- a ⇒' b = Π' a λ _ → b
-- infixr 3 _⇒'_

-- _×'_ : ∀ {l} → UU l → UU l → UU l
-- a ×' b = Σ' a λ _ → b
-- infixr 4 _×'_

-- --------------------------------------------------------------------------------

-- id' : ∀ {i} → El i (Π' U' λ A → El' A ⇒' El' A)
-- id' {i} A x = x

-- foo : (Bool → Bool) → Bool → Bool
-- foo = id' {1} (Bool' ⇒' Bool')

-- apply' : ∀ {i} → El i (
--   Π' U' λ A → Π' (El' A ⇒' U') λ B
--   → (Π' (El' A) λ x → El' (B x)) ⇒' (Π' (El' A) λ x → El' (B x)))
-- apply' {i} A B = id' {suc i} (Π' (El' A) λ x → El' (B x))

-- uncurry' : ∀ {i} → El i (Π' U' λ A → Π' U' λ B → Π' U' λ C
--   → (El' A ⇒' El' B ⇒' El' C) ⇒' (El' A ×' El' B) ⇒' El' C)
-- uncurry' A B C f (x , y) = f x y


-- -- cumulativity
-- --------------------------------------------------------------------------------

-- data sub : ∀ {i j} → U i → U j → Set
-- lift : ∀ {i j a b} → sub a b → El i a → El j b
-- liftU : ∀ {i} → ↓U (suc i) → ↓U (suc (suc i))

-- data sub where -- can be also implemented without IR, with recursive sub
--   Bool' : ∀ {i}{j} → sub {i}{j} Bool' Bool'
--   U'    : ∀ {i j} → sub {i}{j + i} U' U'
--   Π'    : ∀ {i j a a' b b'}
--           → (p : sub {j}{i} a' a)
--           → (∀ x → sub (b (lift p x)) (b' x))
--           → sub (Π' a b) (Π' a' b')
--   Σ'    : ∀ {i j a a' b b'}
--           → (p : sub {i}{j} a a')
--           → (∀ x → sub (b x) (b' (lift p x)))
--           → sub (Σ' a b) (Σ' a' b')
--   El'   : ∀ {i j a a'} → sub {i}{j} a a'
--           → sub (El' a) (El' a')

-- liftU U' = U'
-- liftU Bool' = Bool'
-- liftU (Π' a b) = Π' (liftU a) λ x → liftU (b {!x!})
-- liftU (Σ' a b) = Σ' (liftU a) λ x → liftU (b {!!})
-- liftU (El' x) = {!!}


-- lift Bool'            x = x
-- lift U' x = {!!}
-- -- lift (U' {j = zero})  x = x
-- -- lift (U' {j = suc j}) x = El' (lift U' x)
-- lift (Π' p q)         f = λ α → lift (q _) (f (lift p α))
-- lift (Σ' p q)         t = lift p (t .₁) , lift (q _) (t .₂)
-- lift (El' p)          x = lift p x

-- subUProp : ∀ {i j k}(p' : sub {i}{k} U' U')(r : k ≡ j + i)
--      → U' ≡ tr (λ x → sub {i}{x} U' U') r p'
-- subUProp {i} {j} {.(j₁ + i)} (U' {j = j₁}) r with +-cancelʳ-≡ j₁ j r | r
-- ... | refl | refl = refl

-- subProp : ∀ {i j a b}(p p' : sub {i}{j} a b) → p ≡ p'
-- subProp Bool' Bool' = refl
-- subProp U'    p'    = subUProp p' refl
-- subProp (Π' p q) (Π' p' q') rewrite subProp p p' =
--   Π' p' & ext (λ x → subProp (q x) (q' x))
-- subProp (Σ' p q) (Σ' p' q') rewrite subProp p p' =
--   Σ' p' & ext λ x → subProp (q x) (q' x)
-- subProp (El' p) (El' p') = El' & subProp p p'

-- -- TODO
-- -- coh: sub a (lift p a)
-- -- rfl: sub a a
-- -- trs: ...

-- -- examples
-- --------------------------------------------------------------------------------

-- {-# REWRITE +-suc #-}

-- Uj+ : ∀ {i j} → sub {suc i}{suc (j + i)} U' U'
-- Uj+ {i}{j} = U'

-- U+i : ∀ {i j} → sub {suc j}{suc (j + i)} U' U'
-- U+i {i}{j} =
--   tr (λ x → sub {suc j}{x} U' U') (suc & +-comm i j) (U'{suc j}{i})

-- hΠ' : ∀ {i j} → (a : U i) → ((x : El (j + i) (lift Uj+ a)) → U j) → U (j + i)
-- hΠ' {i}{j} a b = Π' (lift Uj+ a) λ x → lift (U+i{i}{j}) (b x)

-- -- coh : ∀ {i j}(a : U i) → sub a (lift (Uj+{i}{j}) a)
-- -- coh {i} {zero}  U' = U'
-- -- coh {i} {suc j} U' = {!!}
-- -- coh Bool' = {!!}
-- -- coh (Π' a x) = {!!}
-- -- coh (Σ' a x) = {!!}
-- -- coh (El' x) = {!!}

-- --------------------------------------------------------------------------------

-- codSub : ∀ {i j a b b'} → (∀ x → sub {i} {j + i} (b x) (b' {!!})) →
--   sub {i}{j + i} (Π' a b) (Π' (lift Uj+ a) b')
-- codSub = {!!}


-- kek : U 10
-- kek = U' ⇒' U'

-- brek : U 2
-- brek = U' ⇒' U'


-- -- ex1 : ∀ {i} → U (2 + i)
-- -- ex1 = Π' {!UU.U'!} {!!}
