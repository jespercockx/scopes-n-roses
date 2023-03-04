open import Utils
open Variables

open import Scope

open import Data.Nat.Base

module Syntax 
    {Name     : Set} 
    (iScope   : IScope Name) (let open IScope iScope)
    (atoms    : Scope)
  where

data Term  (@0 α : Scope) : Set
data Branch (@0 α : Scope) : Set
data Branches (@0 α : Scope) : Set

data _⇒_ : (@0 α β : Scope) → Set where
  ⇒weaken : α ⊆ β → α ⇒ β
  ⇒const  : Term β → α ⇒ β
  ⇒join   : α₁ ⋈ α₂ ≡ α → α₁ ⇒ β → α₂ ⇒ β → α ⇒ β

data Term α where
  var    : (@0 x : Name) → {{x ∈ α}} → Term α
  lam    : (@0 x : Name) (v : Term (x ◃ α)) → Term α
  app    : (v : Term α) (e : Term α) → Term α
  pi     : (@0 x : Name) (a : Term α) (b : Term (x ◃ α)) → Term α
  type   : ℕ → Term α
  let′   : (@0 x : Name) (u : Term α) (v : Term (x ◃ α)) → Term α
  atom   : (@0 c : Name) → {{_ : c ∈ atoms}} → Term α
  case   : (@0 x : Name) {{x∈α : x ∈ α}} (bs : Branches (diff x∈α)) → Term α

data Branch α where
  branch : (@0 c : Name) → {{_ : c ∈ atoms}} → Term α → Branch α

data Branches α where
  []  : Branches α
  _∷_ : Branch α → Branches α → Branches α

lookupEnv : α ⇒ β → (@0 x : Name) → {{x ∈ α}} → Term β
lookupEnv (⇒weaken w) x ⦃ q ⦄ = var x {{coerce w q}}
lookupEnv (⇒const u) x = u
lookupEnv (⇒join p f g) x ⦃ q ⦄ = ⋈-case p q (λ r → lookupEnv f x {{r}}) (λ r → lookupEnv g x {{r}})

coerceEnv : α ⊆ β → β ⇒ γ → α ⇒ γ
coerceEnv p (⇒weaken q) = ⇒weaken (⊆-trans p q)
coerceEnv p (⇒const x) = ⇒const x
coerceEnv p (⇒join q f g) = 
  let < p₁ , p₂ , r > = ⊆-⋈-split p q
  in  ⇒join r (coerceEnv p₁ f) (coerceEnv p₂ g)

lookupBranch : Branches α → (@0 c : Name) {{p : c ∈ atoms}} → Maybe (Term α)
lookupBranch [] c = nothing
lookupBranch (branch c₁ {{p}} v ∷ bs) c {{q}} = case c ≟ c₁ of λ where
  (yes refl) → just v
  (no _)     → lookupBranch bs c

weaken : α ⊆ β → Term α → Term β
weakenBranch : α ⊆ β → Branch α → Branch β
weakenBranches : α ⊆ β → Branches α → Branches β
weakenEnv : β ⊆ γ → α ⇒ β → α ⇒ γ

weaken p (var x {{q}})     = var x {{coerce p q}}
weaken p (lam x v)         = lam x (weaken (⊆-◃ p) v)
weaken p (app u v)         = app (weaken p u) (weaken p v)
weaken p (pi x a b)        = pi x (weaken p a) (weaken (⊆-◃ p) b)
weaken p (type n)          = type n
weaken p (let′ x v t)      = let′ x (weaken p v) (weaken (⊆-◃ p) t)
weaken p (atom c)          = atom c
weaken p (case x {{q}} bs) = case x {{coerce p q}} (weakenBranches (diff-⊆-trans q p) bs)

weakenBranch p (branch c v) = branch c (weaken p v)

weakenBranches p []       = []
weakenBranches p (b ∷ bs) = weakenBranch p b ∷ weakenBranches p bs

weakenEnv p (⇒weaken q) = ⇒weaken (⊆-trans q p)
weakenEnv p (⇒const x) = ⇒const (weaken p x)
weakenEnv p (⇒join q f g) = ⇒join q (weakenEnv p f) (weakenEnv p g) 

liftEnv : β ⇒ γ → (α <> β) ⇒ (α <> γ)
liftEnv f = ⇒join ⋈-refl (⇒weaken (left ⊆-refl)) (weakenEnv (right ⊆-refl) f)

raiseEnv : α ⇒ β → (α <> β) ⇒ β
raiseEnv f = ⇒join ⋈-refl f (⇒weaken ⊆-refl)

substTerm  : α ⇒ β → Term α → Term β
substBranch : α ⇒ β → Branch α → Branch β
substBranches : α ⇒ β → Branches α → Branches β
substEnv : α ⇒ β → γ ⇒ α → γ ⇒ β

substTerm f (var x)           = lookupEnv f x
substTerm f (lam x v)         = lam x (substTerm (liftEnv f) v)
substTerm f (app u v)         = app (substTerm f u) (substTerm f v)
substTerm f (pi x a b)        = pi x (substTerm f a) (substTerm (liftEnv f) b)
substTerm f (type n)          = type n
substTerm f (let′ x u v)      = let′ x (substTerm f u) (substTerm (liftEnv f) v)
substTerm f (atom c)          = atom c
substTerm f (case x {{p}} bs) = 
  let′ x (lookupEnv f x) 
      (case x {{here}} (substBranches (coerceEnv (diff-⊆ p) f) bs))

substBranch f (branch c u) = branch c (substTerm f u)

substBranches f [] = []
substBranches f (b ∷ bs) = substBranch f b ∷ substBranches f bs

substEnv f (⇒weaken x) = coerceEnv x f
substEnv f (⇒const x) = ⇒const (substTerm f x)
substEnv f (⇒join x g₁ g₂) = ⇒join x (substEnv f g₁) (substEnv f g₂)

substTop : Term α → Term (x ◃ α) → Term α
substTop {α = α} u = substTerm (⇒join ⋈-refl (⇒const u) (⇒weaken ⊆-refl))

step : Term α → Maybe (Term α)
step (app (lam x u) v) = just (substTop v u)
step (app u v) = Maybe.map (λ u → app u v) (step u)
step (let′ x (atom c) (case y {{p}} bs)) = 
  case p ∈-≟ here of λ where
    (yes refl) → case lookupBranch bs c of λ where
      (just v) → just v
      nothing → nothing
    (no _) → nothing
step (let′ x u v) = case step u of λ where
  (just u') → just (let′ x u' v)
  nothing   → just (substTop u v)
step _ = nothing

reduce : ℕ → Term α → Maybe (Term α)
reduce zero u = nothing
reduce (suc n) u = case (step u) of λ where
  (just u') → reduce n u'
  nothing   → just u
