-- An abstract interface to representations of scopes

open import Utils

module Scope (Name : Set) where

open Variables hiding (A;B;C;P;Q;R)

private variable
  @0 A B C : Set
  @0 P Q R : @0 A → Set

record IScope : Set₁ where
  no-eta-equality
  field
    Scope : Set
    ∅     : Scope
    [_]   : @0 Name → Scope
    _<>_  : Scope → Scope → Scope

  field
    _⋈_≡_         : (@0 α β γ : Scope) → Set
    ⋈-∅-left      : ∅ ⋈ β ≡ β
    ⋈-∅-right     : α ⋈ ∅ ≡ α
    ⋈-refl        : α ⋈ β ≡ (α <> β)
    ⋈-comm        : α ⋈ β ≡ γ → β ⋈ α ≡ γ
    ⋈-assoc       : α ⋈ β ≡ δ → δ ⋈ γ ≡ ε → α ⋈ (β <> γ) ≡ ε
    ⋈-assoc'      : α ⋈ β ≡ δ → δ ⋈ γ ≡ ε → (γ <> α) ⋈ β ≡ ε

  _⊆_ : (α β  : Scope) → Set
  α ⊆ β = Σ0 Scope (λ γ → α ⋈ γ ≡ β)

  _∈_  : @0 Name → Scope → Set
  x ∈ α = [ x ] ⊆ α

  field
    -- This is formulated in continuation-passing style to make them more efficient and easier to use.
    ∅-case  : @0 (x ∈ ∅) → A
    []-case : @0 (x ∈ [ y ]) → (x ≡ y → A) → A
    ⋈-case : α ⋈ β ≡ γ → x ∈ γ → (x ∈ α → A) → (x ∈ β → A) → A

  field
    ⋈-quad : α₁ ⋈ α₂ ≡ γ → β₁ ⋈ β₂ ≡ γ
            → Σ0 (Scope × Scope × Scope × Scope) λ (γ₁ , γ₂ , γ₃ , γ₄) →
              (γ₁ ⋈ γ₂ ≡ α₁) × (γ₃ ⋈ γ₄ ≡ α₂) × (γ₁ ⋈ γ₃ ≡ β₁) × (γ₂ ⋈ γ₄ ≡ β₂)

  field
    _⋈-≟_ : (p q : α ⋈ β ≡ γ) → Dec (p ≡ q)
    _⊆-≟_ : (p q : α ⊆ β) → Dec (p ≡ q)
    _∈-≟_ : (p : x ∈ α) (q : y ∈ α) → Dec (_≡_ {A = Σ Name (_∈ α)} (x , p) (y , q))

  _≟_ : (@0 x y : Name) {{p : x ∈ α}} {{q : y ∈ α}} 
      → Dec (_≡_ {A = Σ Name (_∈ α)} (x , p) (y , q))
  x ≟ y = it ∈-≟ it

  _◃_   : @0 Name → Scope → Scope
  x ◃ α = [ x ] <> α

  infixr 10 _◃_

  ⊆-trans : α ⊆ β → β ⊆ γ → α ⊆ γ
  ⊆-trans < p > < q > = < ⋈-assoc p q >

  coerce : α ⊆ β → x ∈ α → x ∈ β
  coerce p q = ⊆-trans q p

  ⊆-left : α ⋈ β ≡ γ → α ⊆ γ
  ⊆-left p = < p >

  ⊆-right : α ⋈ β ≡ γ → β ⊆ γ
  ⊆-right p = < ⋈-comm p >

  ⊆-∅ : ∅ ⊆ α
  ⊆-∅ = ⊆-left ⋈-∅-left

  ⊆-refl : α ⊆ α
  ⊆-refl = ⊆-left ⋈-∅-right

  left : α ⊆ β → α ⊆ (β <> γ)
  left p = ⊆-trans p (⊆-left ⋈-refl)

  right : α ⊆ γ → α ⊆ (β <> γ)
  right p = ⊆-trans p (⊆-right ⋈-refl)

  here : x ∈ (x ◃ α)
  here = ⊆-left ⋈-refl

  there : x ∈ α → x ∈ (y ◃ α)
  there p = right p

  ⊆-<> : β₁ ⊆ β₂ → (α <> β₁) ⊆ (α <> β₂)
  ⊆-<> p = < ⋈-assoc' (proj₂ p) (⋈-comm ⋈-refl) >

  ⊆-◃  : α ⊆ β → (y ◃ α) ⊆ (y ◃ β)
  ⊆-◃ = ⊆-<>

  <>-case  : x ∈ (α <> β) → (x ∈ α → A) → (x ∈ β → A) → A
  <>-case = ⋈-case ⋈-refl

  ◃-case : x ∈ (y ◃ α) → (x ≡ y → A) → (x ∈ α → A) → A
  ◃-case p f g = <>-case p (λ q → []-case q f) g


  @0 _ᶜ : α ⊆ β → Scope
  _ᶜ = get ∘ proj₁

  diff-left : (p : α ⋈ β ≡ γ) → (⊆-left p) ᶜ ≡ β
  diff-left p = refl

  diff-right : (p : α ⋈ β ≡ γ) → (⊆-right p) ᶜ ≡ α
  diff-right p = refl

  ⋈-diff : (p : α ⊆ β) → α ⋈ p ᶜ ≡ β
  ⋈-diff = proj₂

  diff-⊆-trans : (p : α ⊆ β) (q : β ⊆ γ) → (p ᶜ) ⊆ ((⊆-trans p q) ᶜ)
  diff-⊆-trans p q = < ⋈-refl >

  diff-⊆ : (p : α ⊆ β) → (p ᶜ) ⊆ β
  diff-⊆ p = ⊆-right (⋈-diff p)

  diff-case : (p : α ⊆ β) → x ∈ β → (x ∈ α → A) → (x ∈ (p ᶜ) → A) → A
  diff-case p = ⋈-case (⋈-diff p)

  ⊆-⋈-split : α ⊆ β → β₁ ⋈ β₂ ≡ β
          → Σ0 (Scope × Scope) λ (α₁ , α₂) → α₁ ⊆ β₁ × α₂ ⊆ β₂ × α₁ ⋈ α₂ ≡ α
  ⊆-⋈-split < p > q =
    let < r₁ , r₂ , r₃ , r₄ > = ⋈-quad p q
    in  < < r₃ > , < r₄ > , r₁ >

  ⊆-<>-split : α ⊆ (β₁ <> β₂) → Σ0 (Scope × Scope) λ (α₁ , α₂) → α₁ ⊆ β₁ × α₂ ⊆ β₂ × α₁ ⋈ α₂ ≡ α
  ⊆-<>-split p = ⊆-⋈-split p ⋈-refl
