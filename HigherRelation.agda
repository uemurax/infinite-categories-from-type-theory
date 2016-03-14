module HigherRelation where

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Product
open import Data.Vec
open import Data.Fin hiding (_+_)
open import Data.Unit
open import Level
  using (Lift)
  renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality

module Util where
  -- Prod (X₁, ..., Xₙ) ≃ X₁ × ... × Xₙ
  Prod : ∀ {i n} (A : Vec (Set i) n) → Set i
  Prod [] = Lift ⊤
  Prod (A ∷ As) = A × Prod As

  -- drop-at k (x₀, ..., xₖ, ..., xₙ) =
  -- (x₀, ..., xₖ₋₁, xₖ₊₁, ..., xₙ)
  drop-at : ∀ {i n} {A : Set i} → Fin (suc n) →
              Vec A (suc n) → Vec A n
  drop-at zero (x ∷ xs) = xs
  drop-at {n = zero} (suc ())
  drop-at {n = suc n} (suc k) (x ∷ xs) = x ∷ drop-at k xs

  -- drop-at1 k (x₀ : X₀, ..., xₖ : Xₖ, ..., xₙ : Xₙ) =
  -- (x₀ : X₀, ..., xₖ₋₁ : Xₖ₋₁, xₖ₊₁ : Xₖ₊₁, ..., xₙ : Xₙ)
  drop-at1 : ∀ {i n} {A : Vec (Set i) (suc n)} →
               (k : Fin (suc n)) → Prod A → Prod (drop-at k A)
  drop-at1 {A = x ∷ A} zero (proj₁ , proj₂) = proj₂
  drop-at1 {n = zero} {x ∷ A} (suc ())
  drop-at1 {n = suc n} {x ∷ A} (suc k) (proj₁ , proj₂) =
           (proj₁ , drop-at1 k proj₂)

module HR i where
  open Util

  mutual
    A : ℕ → ℕ → Set (lsuc i)
    A zero n = Vec (Set i) (suc n)
    A (suc m) n = Σ (A m (suc n)) (B m n)

    B : ∀ m n → A m (suc n) → Set (lsuc i)
    B m zero a = σA a → Set i
    B m (suc n) a =
      (i : Fin (3 + m + n)) →
      B m n (dA (subst (λ l → Fin (2 + l)) (sym (+-suc m n)) i) a)

    σA : ∀ {m n} → A m n → Set i
    σA {zero} a = Prod a
    σA {suc m} (a , b) = Σ (σA a) (σB {m} b)

    σB : ∀ {m n} {a : A m (suc n)} (b : B m n a) → σA a → Set i
    σB {n = zero} b x = b x
    σB {m = m} {n = suc n} b x =
      (i : Fin (3 + m + n)) →
      σB {n = n} (b i) (dσA {m} (subst (λ l → Fin (2 + l))
         (sym (+-suc m n)) i) x)

    dA : ∀ {m n} (k : Fin (2 + m + n)) → A m (suc n) → A m n
    dA {zero} k a = drop-at k a
    dA {suc m} k (a , b) =
      dA (subst (λ l → Fin (2 + l)) (sym (+-suc m _)) k) a , b k

    dσA : ∀ {m n} {a : A m (suc n)} (k : Fin (2 + m + n)) →
            σA a → σA (dA k a)
    dσA {zero} k x = drop-at1 k x
    dσA {suc m} {n} k (a , b) =
      dσA {m} {suc n} (subst (λ l → Fin (2 + l))
          (sym (+-suc m n)) k) a , b k

  HRel : ℕ → Set (lsuc i)
  HRel n = A n 0

open HR public
  using (HRel)

HRel₀ = HRel lzero

module test where
  open Util

  -- HRel₀ 0 ≃ Set₀
  hrel-0 : HRel₀ 0 ≡ Vec Set 1
  hrel-0 = refl

  hrel-0-example : HRel₀ 0
  hrel-0-example = ℕ ∷ []

  -- HRel₀ 1 ≃ Σ (A B : Set₀) A → B → Set₀
  hrel-1 : HRel₀ 1 ≡ Σ (Vec Set 2) (λ a → Prod a → Set)
  hrel-1 = refl

  hrel-1-example : HRel₀ 1
  hrel-1-example = (ℕ ∷ ℕ ∷ [] , λ { (m , n , _) → m ≡ n })

  -- HRel₀ 2 ≃
  --   Σ (A B C : Set₀)
  --     Σ (P : B → C → Set₀ , Q : A → C → Set₀ , R : A → B → Set₀)
  --       Π (a : A , b : B , c : C) P b c → Q a c → R a b → Set₀
  hrel-2 : HRel₀ 2 ≡
           Σ (Σ (Vec Set 3)
                (λ a → (i : Fin 3) → Prod (drop-at i a) → Set))
             (λ { (A₀ , A₁) →
               Σ (Prod A₀)
                 (λ x → (i : Fin 3) → A₁ i (drop-at1 i x)) → Set })
  hrel-2 = refl

  hrel-2-example : HRel₀ 2
  hrel-2-example =
    ((ℕ ∷ ℕ ∷ ℕ ∷ [] ,
      λ { zero → λ { (m , n , _) → m ≡ n }
          ; (suc zero) → λ { (m , n , _) → m ≡ n }
          ; (suc (suc zero)) → λ { (m , n , _) → m ≡ n }
          ; (suc (suc (suc ()))) }) ,
     (λ { (_ , f) →
       trans (f (suc (suc zero))) (f zero) ≡ f (suc zero) }))
