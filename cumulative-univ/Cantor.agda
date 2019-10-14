

open import Data.Nat hiding (_<_)
import Data.Nat as N


-- data O : Set
-- data _<_ : O → O → Set
-- data fst_≡_ : O → O → Set

-- data O where
--   zero : O
--   cons : (a b : O) → ℕ → ∀ {fb} → fst b ≡ fb → a < fb → O
-- data _<_ where
--   zero< : ∀ {a b n fb p q} → zero < cons a b n {fb} p q
--   cons₁ : ∀ {a b n fb p q a' b' n' fb' p' q'}
--           → a < a'
--           → cons a b n {fb} p q < cons a' b' n' {fb'} p' q'
--   cons₂ : ∀ {a b n fb p q b' n' fb' p' q'}
--           → b < b'
--           → cons a b n {fb} p q < cons a b' n' {fb'} p' q'

-- data O : El O' → Set
-- -- data _<_ : O → O → Set

-- -- data O where
-- --   zero : O
-- --   ω^_+_[_] : (a b : O) →
