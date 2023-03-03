{-# OPTIONS --overlapping-instances #-}

open import Utils
open import Scope
open import ScopeImpl

open Variables

Name = String

open IScope (simpleScope Name)

instance
  top : x ∈ (x ◃ α)
  top = here

  pop : {{x ∈ α}} → x ∈ (y ◃ α)
  pop {{p}} = there p

atoms = "true" ◃ "false" ◃ ∅

open import Syntax (simpleScope Name) atoms

`true : Term α
`true = atom "true"
`false : Term α
`false = atom "false"

∞ : ℕ
∞ = 9999999999999999

module Tests (@0 x y z : Name) where

  testTerm₁ : Term ∅
  testTerm₁ = app (lam x (var x)) (type 0)

  test₁ : reduce ∞ testTerm₁ ≡ just (type 0)
  test₁ = refl

  testTerm₂ : Term ∅
  testTerm₂ = let′ x `true (case x (branch "true" `false ∷ branch "false" `true ∷ []))

  test₂ : reduce ∞ testTerm₂ ≡ just (atom "false")
  test₂ = refl
