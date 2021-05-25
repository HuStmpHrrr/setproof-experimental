------------------------------------------------------------------------
-- Simple quotient type example formalized in Agda
--
-- TODO: add example that requires UIP
-- (Currently all proof works without UIP.
--  See after commenting out PSet/UIP-W/UIP-B and PSet case of id-num)
--
-- Author: Jason Hu and Clare Jang
------------------------------------------------------------------------
{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

data Person : Set where
  W B  : Person                 -- William and Bill
  Eq   : W ≡ B                  -- William and Bill are the same
  PSet : isSet Person           -- Person is a set

module PersonProps where
  UIP-W : (eq : W ≡ W) → eq ≡ refl
  UIP-W eq = PSet W W eq refl

  UIP-B : (eq : B ≡ B) → eq ≡ refl
  UIP-B eq = PSet B B eq refl

id-num : Person → ℕ
id-num W                     = 0
id-num B                     = 0
id-num (Eq i)                = 0
id-num (PSet x y eq eq′ i j) = isSetℕ (id-num x) (id-num y) (λ k → id-num (eq k)) (λ k → id-num (eq′ k)) i j

data Phone : Person → Set where
  IP : Phone W
  SS : Phone B

price : ∀ {p} → Phone p → ℕ
price {.W} IP = 0
price {.B} SS = 1

IP-is-0 : price (subst Phone Eq IP) ≡ 0
IP-is-0 = gen Eq IP
  where gen : ∀ {x y} → (eq : x ≡ y) (p : Phone x) → price (subst Phone eq p) ≡ price p
        gen {x} = J {x = x}
                    (λ p₁ eq → (p : Phone x) → price (subst Phone eq p) ≡ price p)
                    (λ ph → cong price (substRefl {B = Phone} ph))

SS-is-1 : price (subst Phone (sym Eq) SS) ≡ 1
SS-is-1 = gen (sym Eq) SS
  where gen : ∀ {x y} → (eq : x ≡ y) (p : Phone x) → price (subst Phone eq p) ≡ price p
        gen {x} = J {x = x}
                    (λ p₁ eq → (p : Phone x) → price (subst Phone eq p) ≡ price p)
                    (λ ph → cong price (substRefl {B = Phone} ph))

-- None of the following can be proved as
-- both IP and SS are William's, i.e, Bill's phones.

B′s-Phone≠0 : ¬ ((ph : Phone B) → price ph ≡ 0)
B′s-Phone≠0 P = snotz (refl ∙ P SS)

B′s-Phone≠1 : ¬ ((ph : Phone B) → price ph ≡ 1)
B′s-Phone≠1 P = snotz (sym (P (subst Phone Eq IP)) ∙ IP-is-0)

W′s-Phone≠0 : ¬ ((ph : Phone W) → price ph ≡ 0)
W′s-Phone≠0 P = snotz (sym ((sym (P (subst Phone (sym Eq) SS))) ∙ SS-is-1))

W′s-Phone≠1 : ¬ ((ph : Phone W) → price ph ≡ 1)
W′s-Phone≠1 P = snotz (sym (refl ∙ P IP))
