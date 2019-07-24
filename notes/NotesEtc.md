
We (temporarily) include here the -ᴬ, -ᴰ, -ᴹ, -ˢ interpretations of infinitary
functions, because it's not included in CQIIT paper.


(Π̃ T b)ᴬ i :≡ (α : T) → (b α)ᴬ i
(t @̃ α)ᴬ i :≡ tᴬ i α
(lam̃ f)ᴬ i :≡ λ α. (f α)ᴬ i

(Π̂ T b)ᴰ {i} i* f :≡ (α : T) → (b α)ᴰ i* (f α)
(t @̃ α)ᴰ     i*   :≡ tᴰ i* α
(lam̃ f)ᴰ     i*   :≡ λ α. (f α)ᴰ i*

(Π̃ T b)ᴹ {i}{j} (f : Γᴹ i j) :≡ λ g α. (b α)ᴹ f (g α)
(t @̃ α)ᴹ f :≡ happly (tᴹ f) α
(lam̃ g)ᴹ f :≡ funext ((g α)ᴹ f)

(Π̃ T b)ˢ {i}{i*} f* :≡ λ g α. (b α)ˢ f* (g α)
(t @̃ α)ˢ f* :≡ happly α (tˢ f*)
(lam̃ g)ˢ f* :≡ funext ((g α)ˢ f*)


Sort equations, also temporarily:

(IdU a b)ᴬ i  :≡ aᴬ i = bᴬ i
(ReflU a)ᴬ i  :≡ refl
(ReflectU e)ᴬ :≡ funext eᴬ
(UIPU e)ᴬ     :≡ UIP

(IdU a b)ᴰ i* e :≡ tr (λ A. A → Set₀) e (aᴰ i*) = (bᴰ i*)
(ReflU a)ᴰ i*   :≡ refl
(ReflectU e)ᴰ   :≡ funext eᴰ
(UIPU e)ᴰ       :≡ UIP

(IdU a b)ᴹ f  e₀ e₁ :≡ ⊤
(ReflU a)ᴹ f        :≡ tt
(ReflectU e)ᴹ       :≡ refl
(UIPU e)ᴹ           :≡ refl

(IdU a b)ˢ f* e eᴰ :≡ ⊤
(ReflU a)ˢ f*      :≡ tt
(ReflectU e)ˢ      :≡ refl
(UIPU e)ˢ          :≡ refl

-- iso-cleaving fails for sort equations!

-- for example, consider Σ(A : Set)×(B : Set)×(e : A = B) as algebras.
-- then, if A, A', B, B' : Set, and (A, B) and (A', B') are isomorphic,
-- and we have (e : A = B), then A' = B' may be still false!

--------------------------------------------------------------------------------

CwF model for sort equations:

- just pointwise equality, all structures and equations
  given by UIP

IdU (a b : Tm Γ U) : Ty Γ
  ᴬ i      :≡ aᴬ i  = bᴬ i
  ᴰ i*     :≡ aᴰ i* = bᴰ i*
  ᴹ _ _ f  :≡ aᴹ f  = bᴹ f
  ˢ _ _ f* :≡ aˢ f* = bˢ f*

ReflU    : pointwise refl
UIPU     : pointwise UIP
ReflectU : pointwise funext
-- etc, obviously

-- note: *strict* term model and eliminator works for sort equations

(IdU a b)ᶜ ν (e : Tm Ω (IdU a[ν] b[ν]))
  : (IdU a b)ᴬ (Γᶜ ν)
  : aᴬ (Γᶜ ν) = bᴬ (Γᶜ ν)

  aᶜ ν : Tm Ω (El a[ν]) = aᴬ (Γᶜ ν)
  bᶜ ν : Tm Ω (El b[ν]) = bᴬ (Γᶜ ν)

  to show: Tm Ω (El a[ν]) = Tm Ω (El b[ν])
  OK -- by equality reflection for e

-- rest: UIP

(IdU a b)ᴱ ν (e : Tm Ω (IdU a[ν] b[ν])) : ⊤
-- everything trivial
