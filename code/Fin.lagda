We have to roll our own version of Fin, the usual one, because the
uniqueness of maps Fin n → A would not hold otherwise.

\begin{code}
{-# OPTIONS --without-K --rewriting #-}

module Fin where

open import Universes
open import lib.Basics
open import lib.types.Nat

data Fin : ℕ →  𝓤₀ ̇ where
  Z : {n : ℕ} → Fin (S n)
  S : {n : ℕ} → Fin n → Fin (S n)

data FinMapDom (A : 𝓤₀ ̇) : ℕ → 𝓤₀ ̇ where
  dom-Z : FinMapDom A 0
  dom-S : {n : ℕ} → (a : A) → (d : FinMapDom A n) → FinMapDom A (S n)

Fin-map : ∀{n A} → FinMapDom A n → Fin n → A
Fin-map (dom-S a d) Z      = a
Fin-map (dom-S a d) (S x)  = Fin-map d x

mk-FinMapDom : ∀{n A} → (Fin n → A) → FinMapDom A n
mk-FinMapDom {O}    h = dom-Z
mk-FinMapDom {S n}  h = dom-S (h Z) (mk-FinMapDom (h ∘ S))

Fin-map-unique : ∀{n A} → (h : Fin n → A) → h == Fin-map (mk-FinMapDom h)
Fin-map-unique = FunextNonDep.λ=-nondep ∘ lem
  where
    lem : ∀{n A} → (h : Fin n → A) → h ∼ Fin-map (mk-FinMapDom h)
    lem h Z      = idp
    lem h (S x)  = lem (h ∘ S) x

FinMapDom-map : ∀{n A B} → (f : A → B) → FinMapDom A n → FinMapDom B n
FinMapDom-map f dom-Z        = dom-Z
FinMapDom-map f (dom-S a d)  = dom-S (f a) (FinMapDom-map f d)

Fin-map-∘ : ∀{n A B} (f : A → B) (d : FinMapDom A n) →
            f ∘ Fin-map d == Fin-map (FinMapDom-map f d)
Fin-map-∘ f d = FunextNonDep.λ=-nondep (lem f d)
  where
    lem :  ∀{n A B} (f : A → B) (d : FinMapDom A n) →
           f ∘ Fin-map d ∼ Fin-map (FinMapDom-map f d)
    lem f (dom-S a d) Z = idp
    lem f (dom-S a d) (S x) = lem f d x

\end{code}
