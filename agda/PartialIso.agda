{-# OPTIONS --without-K #-}

open import Equality

module PartialIso {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude as P hiding (id; _∘_)
open Derived-definitions-and-properties eq
open import Equivalence eq as Equiv hiding (id; _∘_)

inj₂-inj : ∀ {ℓ : Level} {A B : Set ℓ} {b b' : B} → B → (inj₂ b ≡ inj₂ b') → (b ≡ b')
inj₂-inj {_} {A} {B} def = cong proj
  where
    proj : A ⊎ B → B
    proj (inj₁ _) = def
    proj (inj₂ x) = x

PartialIso′ : (ℓ : Level) → Set ℓ → Set ℓ → Set ℓ
PartialIso′ ℓ S T =

  ∃ λ (f : S → T) →

  ∃ λ (f′ : T → (↑ ℓ ⊤) ⊎ S) →

  ((s : S) → f′ (f s) ≡ inj₂ s) ×

  ((s : S) → (t : T) → (f′ t ≡ inj₂ s) → (t ≡ f s))

record PartialIso (ℓ : Level) (S T : Set ℓ) : Set ℓ where
  field
    partialIso : PartialIso′ ℓ S T

  to : S → T
  to = proj₁ partialIso

  from : T → (↑ ℓ ⊤) ⊎ S
  from = proj₁ (proj₂ partialIso)

  from-to : (s : S) → from (to s) ≡ inj₂ s
  from-to = proj₁ (proj₂ (proj₂ partialIso))

  to-from : (s : S) → (t : T) → (from t ≡ inj₂ s) → (t ≡ to s)
  to-from = proj₂ (proj₂ (proj₂ partialIso))

_⊆_ : {ℓ : Level} → (S T : Set ℓ) → Set ℓ
_⊆_ {ℓ} = PartialIso ℓ

id : ∀ {ℓ : Level} → (S : Set ℓ) → PartialIso ℓ S S
id {ℓ} S = record
  { partialIso = P.id , inj₂
  , (λ s → refl (inj₂ s))
  , (λ s t eq → inj₂-inj {A = ↑ ℓ ⊤} s (subst (λ x → inj₂ t ≡ inj₂ x) (refl s) eq))
  }

_K∘_ : {ℓ : Level} {A B C : Set ℓ} → (B → (↑ ℓ ⊤) ⊎ C) → (A → (↑ ℓ ⊤) ⊎ B) → (A → (↑ ℓ ⊤) ⊎ C)
_K∘_ f g a with g a
_K∘_ f g a | inj₁ _ = inj₁ (lift tt)
_K∘_ f g a | inj₂ b = f b

_∘_ : ∀ {ℓ : Level} {S T U : Set ℓ} → PartialIso ℓ T U → PartialIso ℓ S T → PartialIso ℓ S U
_∘_ {ℓ} {S} {T} {U} f g =
    record
    { partialIso
    = (λ s → f.to (g.to s))
    , g.from K∘ f.from
    , f-t
    , t-f
    }
  where
    module f = PartialIso f
    module g = PartialIso g
    f-t : (s : S) → (g.from K∘ f.from) (f.to (g.to s)) ≡ inj₂ s
    f-t s with (f.from (f.to (g.to s))) 
    f-t s | inj₁ x = {!!}
    f-t s | inj₂ y = {!!}
    t-f : {!!}
    t-f = {!!}
