In this module, we define the very basic concept of signatures
and terms. These are in category theoretic jargon polynomial functors
and free monads, and in type-theoretic terms container and W-types.

\begin{code}
{-# OPTIONS --without-K --rewriting #-}

module Terms where

open import Universes
open import lib.Basics renaming (_⊔_ to +)

record Signature (𝓤 𝓥) : (𝓤 ⊔ 𝓥) ⁺ ̇ where
  field
    sym  : 𝓤 ̇
    ar   : sym → 𝓥 ̇
open Signature public

⟦_⟧ : ∀ {𝓤 𝓥 𝓦} → (P : Signature 𝓤 𝓥) → 𝓦 ̇ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
⟦ P ⟧ X = Σ (sym P) λ s → ar P s → X

⟪_⟫ : ∀ {𝓤 𝓥 𝓦} (S : Signature 𝓤 𝓥) {X : 𝓦 ̇} {𝓣} → (Q : X → 𝓣 ̇) → (⟦ S ⟧ X → 𝓥 ⊔ 𝓣 ̇)
⟪ P ⟫ Q (s , α) = (x : ar P s) → Q (α x)

data Term {𝓤 𝓥 𝓦} (P : Signature 𝓤 𝓥) (V : 𝓦 ̇) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ where
  var   : V → Term P V
  node  : (s : sym P) (α : ar P s → Term P V) → Term P V

module TermElim {𝓤 𝓥 𝓦} {P : Signature 𝓤 𝓥} {V : 𝓦 ̇} {𝓣} {Q : Term P V → 𝓣 ̇}
  (var*   : (v : V) → Q (var v))
  (node*  : (s : sym P) (α : ar P s → Term P V) (γ : (x : ar P s) → Q (α x)) → Q (node s α))
  where

  f : Π (Term P V) Q
  f (var v)     = var* v
  f (node s α)  = node* s α (λ x → f (α x))

Term-elim = TermElim.f

module TermRec {𝓤 𝓥 𝓦} {P : Signature 𝓤 𝓥} {V : 𝓦 ̇} {𝓣} {X : 𝓣 ̇}
  (var*   : V → X)
  (node*  : (s : sym P) → (ar P s → X) → X)
  where

  f : Term P V →  X
  f = Term-elim var* (λ s _ γ → node* s γ)

Term-rec = TermRec.f

Term-map : ∀ {𝓤 𝓥 𝓦 𝓦'} {Σ : Signature 𝓤 𝓥} {V : 𝓦 ̇} {U : 𝓦' ̇} → (V → U) → Term Σ V → Term Σ U
Term-map f = Term-rec (var ∘ f) node

Term-lift : ∀ {𝓤 𝓥 𝓦 𝓦'} {Σ : Signature 𝓤 𝓥} {V : 𝓦 ̇} (P : V → 𝓦' ̇) → Term Σ V → 𝓥 ⊔ 𝓦' ̇
Term-lift {_} {𝓥} {Σ = Σ} P
  = Term-rec (λ x → _↑ {_} {𝓥} (P x)) (λ s α → ∀ (k : ar Σ s) → α k)

data TermP {𝓤 𝓥 𝓦 𝓣} (Σ : Signature 𝓤 𝓥) {X : 𝓦 ̇} (P : X → 𝓣 ̇) :
     Term Σ X → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇ where
  var-case   : {x : X} → P x                                                  → TermP Σ P (var x)
  node-case  : (s : sym Σ) (α : ar Σ s → Term Σ X) → (∀ x → TermP Σ P (α x))  → TermP Σ P (node s α)

module TermPRec {𝓤 𝓥 𝓦} {Σ : Signature 𝓤 𝓥} {X : 𝓦 ̇} {𝓣 𝓣'} {P : X → 𝓣 ̇} {U : Term Σ X → 𝓣' ̇}
  (var-case*   : ∀ {x} → P x → U (var x))
  (node-case*  : ∀ s α → (∀ x → U (α x)) → U (node s α))
  where

  f : ∀ {t : Term Σ X} → TermP Σ P t → U t
  f (var-case px) = var-case* px
  f (node-case s α p) = node-case* s α λ x → f (p x)

TermP-rec = TermPRec.f

\end{code}
