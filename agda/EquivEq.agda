-- Uses NAD's "equality" repo: http://www.cse.chalmers.se/~nad/listings/equality/README.html

{-# OPTIONS --without-K #-}

open import Equality

module EquivEq {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude
open Derived-definitions-and-properties eq
open import Equivalence eq as Equiv
open import Equality.Decision-procedures eq using (module Fin)


lemma : ∀ {A B : Set} → Decidable-equality A → ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → (A ≃ B)
lemma decA ⊤⊎A≃⊤⊎B = record
  { to = {!!}
  ; is-equivalence = {!!}
  }
  where
  open _≃_ ⊤⊎A≃⊤⊎B using (to; from)

gcbp : ∀ {A B A' B' : Set} → ((A ⊎ A') ≃ (B ⊎ B')) → (A ≃ B) → (A' ≃ B')
gcbp {A} {B} {A'} {B'} A⊎A'≃B⊎B' A'≃B' = record
  { to = λ a → back-and-forth (inj₂ a)
  ; is-equivalence = {!!} -- this part is nontrivial too!
  }
  where
    back-and-forth : A ⊎ A' → B'
    back-and-forth a with (_≃_.to A⊎A'≃B⊎B' a)
    ... | inj₂ b  = b
    ... | b'      = back-and-forth (_≃_.from A⊎A'≃B⊎B' b')
    -- and it is REALLY non-obvious that this terminates!  need to
    -- build some sort of data structure that makes it more
    -- evident... like with mergesort.  Hopefully that would also lead
    -- to a more perspicuous explanation of the proof.

Fin≃→≡ : ∀ {n₁ n₂ : ℕ} → (Fin n₁ ≃ Fin n₂) → (n₁ ≡ n₂)
Fin≃→≡ {zero}   {zero}   e = refl 0
Fin≃→≡ {zero}   {suc n₂} e with (_≃_.from e (inj₁ tt))
... | ()
Fin≃→≡ {suc n₁} {zero}   e with (_≃_.to   e (inj₁ tt))
... | ()
Fin≃→≡ {suc n₁} {suc n₂} e = cong suc (Fin≃→≡ (gcbp e Equiv.id))
  -- hehe, indeed, it is really not obvious that the above terminates,
  -- even aside from the termination of gcbp itself, since there is a
  -- call to 'gcbp' in the recursive position.

