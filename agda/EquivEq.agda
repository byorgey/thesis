-- Uses NAD's "equality" repo: http://www.cse.chalmers.se/~nad/listings/equality/README.html

{-# OPTIONS --without-K #-}

open import Equality

module EquivEq {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Prelude
open Derived-definitions-and-properties eq
open import Equivalence eq as Equiv
open import Preimage eq
open import Equality.Decision-procedures eq using (module Fin)

⊎-disjoint : ∀ {A B : Set} {P : Set} {x : A} {y : B} → (inj₁ x ≡ inj₂ y) → P
⊎-disjoint {A} {B} {P} eq = subst (λ X → X) (cong wit eq) tt
  where
    wit : (A ⊎ B) → Set
    wit (inj₁ _) = ⊤
    wit (inj₂ _) = P

inj₂-inj : ∀ {A B : Set} {b b' : B} → B → (inj₂ b ≡ inj₂ b') → (b ≡ b')
inj₂-inj {A} {B} def = cong proj
  where
    proj : A ⊎ B → B
    proj (inj₁ _) = def
    proj (inj₂ x) = x

-- Proving this special case might be more straightforward then GCBP
-- in all its generality.
--
-- Or... maybe not.  It's certainly tedious.
lemma : ∀ {A B : Set} → ((⊤ ⊎ A) ≃ (⊤ ⊎ B)) → (A ≃ B)
lemma {A} {B} ⊤⊎A≃⊤⊎B = record
  { to = A→B
  ; is-equivalence = λ b → (B→A b , A→B∘B→A b) , preimgPf b
  }
  where
    open _≃_ ⊤⊎A≃⊤⊎B using (to; from; injective; right-inverse-of; left-inverse-of)
    A→B : A → B
    A→B a with inspect (to (inj₂ a))
    A→B a | inj₂ b  with-≡ _  = b
    A→B a | inj₁ tt with-≡ eq₁ with inspect (to (inj₁ tt))
    ...     | inj₂ b  with-≡ _   = b
    ...     | inj₁ tt with-≡ eq₂ = ⊎-disjoint (injective (trans eq₂ (sym eq₁)))

    B→A : B → A
    B→A b with inspect (from (inj₂ b))
    B→A b | inj₂ a  with-≡ _  = a
    B→A b | inj₁ tt with-≡ eq₁ with inspect (from (inj₁ tt))
    ...     | inj₂ a  with-≡ _   = a
    ...     | inj₁ tt with-≡ eq₂ = ⊎-disjoint (_≃_.injective (inverse ⊤⊎A≃⊤⊎B) (trans eq₂ (sym eq₁)))

    -- ugh!!!  And that's only *one* direction...  Would need to come
    -- up with a much nicer theory & way of organizing these things...
    -- (for example, A→B and B→A are entirely symmetric but that
    -- doesn't go into their definitions so we don't get to exploit
    -- it).
    A→B∘B→A : (b : B) → A→B (B→A b) ≡ b
    A→B∘B→A b with inspect (from (inj₂ b))
    A→B∘B→A b | inj₂ a with-≡ _ with inspect (to (inj₂ a))
    A→B∘B→A b | inj₂ a with-≡ _ | inj₁ tt with-≡ _ with inspect (to (inj₁ tt))
    A→B∘B→A b | inj₂ a with-≡ _   | inj₁ tt with-≡ eq₁ | inj₁ tt with-≡ eq₂ = ⊎-disjoint (injective (trans eq₂ (sym eq₁)))
    A→B∘B→A b | inj₂ a with-≡ eq₃ | inj₁ tt with-≡ eq₂ | inj₂ _  with-≡ _
      = ⊎-disjoint
          (trans (sym (subst (λ x → to x ≡ inj₁ tt) (sym eq₃) eq₂))
           (right-inverse-of (inj₂ b)))
    A→B∘B→A b | inj₂ a with-≡ eq₁ | inj₂ b' with-≡ eq₂
      = inj₂-inj b (trans (sym eq₂) (subst (λ x → to x ≡ inj₂ b) eq₁ (right-inverse-of (inj₂ b))))
    A→B∘B→A b | inj₁ tt with-≡ _ with inspect (from (inj₁ tt))
    A→B∘B→A b | inj₁ tt with-≡ eq₁ | inj₁ tt with-≡ eq₂ = ⊎-disjoint (_≃_.injective (inverse ⊤⊎A≃⊤⊎B) (trans eq₂ (sym eq₁)))
    A→B∘B→A b | inj₁ tt with-≡ eq₁ | inj₂ a  with-≡ eq₂ with inspect (to (inj₂ a))
    A→B∘B→A b | inj₁ tt with-≡ eq₁ | inj₂ a  with-≡ eq₂ | inj₂ y  with-≡ eq₃
      = ⊎-disjoint
          (trans (sym (right-inverse-of (inj₁ tt)))
           (subst (λ x → to x ≡ inj₂ y) (sym eq₂) eq₃))
    A→B∘B→A b | inj₁ tt with-≡ eq₁ | inj₂ a  with-≡ eq₂ | inj₁ tt with-≡ eq₃ with inspect (to (inj₁ tt))
    A→B∘B→A b | inj₁ tt with-≡ eq₁ | inj₂ a with-≡ eq₂ | inj₁ tt with-≡ eq₃ | inj₁ tt with-≡ eq₄
      = ⊎-disjoint
          (trans (sym (left-inverse-of (inj₁ tt)))
           (subst (λ x → from x ≡ inj₂ a) (sym eq₄) eq₂))
    A→B∘B→A b | inj₁ tt with-≡ eq₁ | inj₂ a with-≡ eq₂ | inj₁ tt with-≡ eq₃ | inj₂ y  with-≡ eq₄
      = inj₂-inj b
          (sym
           (trans (sym (right-inverse-of (inj₂ b)))
            (subst (λ x → to x ≡ inj₂ y) (sym eq₁) eq₄)))

    preimgPf : (b : B) → (b⁻¹ : A→B ⁻¹ b) → ((B→A b , A→B∘B→A b) ≡ b⁻¹)
    preimgPf b b⁻¹ with inspect (from (inj₂ b))
    preimgPf b (a' , a'≡) | inj₂ a with-≡ eq₁ = {!!}
    preimgPf b b⁻¹ | inj₁ tt with-≡ eq₁ = {!!}

gcbp : ∀ {A B A' B' : Set} → ((A ⊎ A') ≃ (B ⊎ B')) → (A ≃ B) → (A' ≃ B')
gcbp {A} {B} {A'} {B'} A⊎A'≃B⊎B' A≃B = record
  { to = λ a → back-and-forth (inj₂ a)
  ; is-equivalence = {!!} -- this part is nontrivial too!
  }
  where
    back-and-forth : A ⊎ A' → B'
    back-and-forth a with (_≃_.to A⊎A'≃B⊎B' a)
    ... | inj₂ b' = b'
    ... | inj₁ b  = back-and-forth (inj₁ (_≃_.from A≃B b))
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

data PChain : Set → Set → Set₁ where
  Node : ∀ {A} → PChain A A
  Link : ∀ {A A' B' B} → PChain A A' → (A' ≃ B') → PChain B' B → PChain A B
  -- Need a type of "sublink" as well, which handles subsets?

-- Need the fact that the sets are *finite*! Otherwise the
-- back-and-forth really might not terminate!
-- back-and-forth : ∀ {A B A' B' : Set} → ((A ⊎ A') ≃ (B ⊎ B')) → (A ≃ B) → A' → Chain A' B'
-- back-and-forth A⊎A'≃B⊎B' A≃B a' = {!!}
