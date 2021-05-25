------------------------------------------------------------------------
-- Simple quotient type example formalized in Agda
--
-- Author: Jason Hu and Clare Jang
------------------------------------------------------------------------
{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

import Cubical.Data.Nat as Nat
import Cubical.Data.Unit as ⊤
import Cubical.Data.Empty as ⊥
import Cubical.Data.Sigma as Sigma

open Nat using (ℕ; zero; suc; isSetℕ; snotz)
open ⊤ using (Unit; tt)
open ⊥ using (⊥)
open Sigma using (Σ; fst; snd)

data Person : Set where
  W B  : Person                 -- William and Bill
  Eq   : W ≡ B                  -- William and Bill are the same

module PersonProps where

  isContrPerson : isContr Person
  isContrPerson = W , helper
    where helper : (y : Person) → W ≡ y
          helper W        = refl
          helper B        = Eq
          helper (Eq i) j = Eq (i ∧ j)

  isSetPerson : isSet Person
  isSetPerson = isProp→isSet (isContr→isProp isContrPerson)

  UIP-W : (eq : W ≡ W) → eq ≡ refl
  UIP-W eq = isSetPerson W W eq refl

  UIP-B : (eq : B ≡ B) → eq ≡ refl
  UIP-B eq = isSetPerson B B eq refl

id-num : Person → ℕ
id-num W      = 0
id-num B      = 0
id-num (Eq i) = 0

data Phone : Person → Set where
  IP : Phone W
  SS : Phone B

module PhoneElim where

  module _ {ℓ}
           (M : ∀ {p} → Phone p → Set ℓ)
           (MIP : M IP)
           (MSS : M SS) where

    elim : ∀ {p} (ph : Phone p) → M ph
    elim IP = MIP
    elim SS = MSS

  module _ {ℓ} {A : Set ℓ} (a₀ a₁ : A) where

    case : ∀ {p} → Phone p → A
    case IP = a₀
    case SS = a₁

    subst-case-invar : ∀ {x y} (eq : x ≡ y) (ph : Phone x) → case (subst Phone eq ph) ≡ case ph
    subst-case-invar {x} = J {x = x}
                             (λ ph′ eq → (ph : Phone x) → case (subst Phone eq ph) ≡ case ph)
                             λ ph → cong case (substRefl {B = Phone} ph)

-- price : ∀ {p} → Phone p → ℕ
-- price {.W} IP = 0
-- price {.B} SS = 1
price : {p : Person} → Phone p → ℕ
price = PhoneElim.case 0 1

IP-is-0 : price (subst Phone Eq IP) ≡ 0
IP-is-0 = PhoneElim.subst-case-invar 0 1 Eq IP

SS-is-1 : price (subst Phone (sym Eq) SS) ≡ 1
SS-is-1 = PhoneElim.subst-case-invar 0 1 (sym Eq) SS

-- None of the following can be proved as
-- both IP and SS are William's, i.e, Bill's phones.

B′s-Phone≠0 : ¬ ((ph : Phone B) → price ph ≡ 0)
B′s-Phone≠0 P = snotz (refl ∙ P SS)

B′s-Phone≠1 : ¬ ((ph : Phone B) → price ph ≡ 1)
B′s-Phone≠1 P = snotz (sym (P (subst Phone Eq IP)) ∙ IP-is-0)

W′s-Phone≠0 : ¬ ((ph : Phone B) → price ph ≡ 1)
W′s-Phone≠0 P = snotz (sym (P (subst Phone Eq IP)) ∙ IP-is-0)

W′s-Phone≠1 : ¬ ((ph : Phone W) → price ph ≡ 1)
W′s-Phone≠1 P = snotz (sym (refl ∙ P IP))

IP≠SS : (eq : W ≡ B) → ¬ (PathP (λ i → Phone (eq i)) IP SS)
IP≠SS eq pth = transp (λ i → PhoneElim.case Unit ⊥ (pth i)) i0 tt

DecPhone : ∀ {x y} (eq : x ≡ y) (ph : Phone x) (ph′ : Phone y) → Dec (PathP (λ i → Phone (eq i)) ph ph′)
DecPhone eq IP IP = yes (subst (λ eq → PathP (λ i → Phone (eq i)) IP IP) (sym (PersonProps.UIP-W eq)) refl)
DecPhone eq IP SS = no (IP≠SS eq)
DecPhone eq SS IP = no λ eq′ → IP≠SS (sym eq) λ i → eq′ (~ i)
DecPhone eq SS SS = yes (subst (λ eq → PathP (λ i → Phone (eq i)) SS SS) (sym (PersonProps.UIP-B eq)) refl)

isSetPhone : ∀ {p} → isSet (Phone p)
isSetPhone = Discrete→isSet (DecPhone refl)

DecΣPhone : Discrete (Σ _ Phone)
DecΣPhone (.W , IP) (.W , IP) = yes refl
DecΣPhone (.W , IP) (.B , SS) = no λ p → let (p₁ , p₂) = Sigma.PathPΣ p in IP≠SS p₁ p₂
DecΣPhone (.B , SS) (.W , IP) = no λ p → let (p₁ , p₂) = Sigma.PathPΣ p in IP≠SS (sym p₁) (λ i → p₂ (~ i))
DecΣPhone (.B , SS) (.B , SS) = yes refl

isSetΣPhone : isSet (Σ _ Phone)
isSetΣPhone = Discrete→isSet DecΣPhone
