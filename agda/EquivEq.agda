{-# OPTIONS --without-K #-}

open import Equality

module EquivEq {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude
open Derived-definitions-and-properties eq
open import Equivalence eq
open import Equality.Decision-procedures eq using (module Fin)


lemma : ∀ {A B : Set} → Decidable-equality A → ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → (A ≃ B)
lemma decA ⊤⊎A≃⊤⊎B = record
  { to = {!!}
  ; is-equivalence = {!!}
  }
  where
  open _≃_ ⊤⊎A≃⊤⊎B using (to; from)

Fin≃→≡ : ∀ {n₁ n₂ : ℕ} → (Fin n₁ ≃ Fin n₂) → (n₁ ≡ n₂)
Fin≃→≡ {zero}   {zero}   e = refl 0
Fin≃→≡ {zero}   {suc n₂} e with (_≃_.from e (inj₁ tt))
... | ()
Fin≃→≡ {suc n₁} {zero}   e with (_≃_.to   e (inj₁ tt))
... | ()
Fin≃→≡ {suc n₁} {suc n₂} e = cong suc (Fin≃→≡ (lemma Fin._≟_ e))
