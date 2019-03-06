We generate the free algebra for an algebraic theory as a HIT,
or rather a 1-truncated HIT or quotient inductive type (QIT).

\begin{code}
{-# OPTIONS --without-K --rewriting #-}

module FreeAlgebra where

open import Universes
open import lib.Basics renaming (_⊔_ to _⊎_) hiding (Σ)
import lib.Basics as B
open import lib.NType2
open import Terms
open import AlgebraicTheories
\end{code}

\begin{code}
module _ where
  postulate -- HIT type
    FreeAlgebra : ∀ {𝓤 𝓥 𝓦} (T : AlgTheory 𝓤 𝓥 𝓦) (X : 𝓦 ̇) → 𝓦 ̇

  module _ {𝓤 𝓥 𝓦} {T : AlgTheory 𝓤 𝓥 𝓦} where
    open AlgTheory T renaming (sig to Σ)

    module _ {X : 𝓦 ̇} where
      postulate -- HIT 0-constructor
        leaf'  : X → FreeAlgebra T X
        node'  : (s : sym Σ) (α : ar Σ s → FreeAlgebra T X) → FreeAlgebra T X

      -- TODO: For now we need to postulate the set quotient here if we don't
      -- want to repeat the free extension of node'
      postulate
        quot   : is-set (FreeAlgebra T X)
\end{code}

\begin{code}
    module _ (X : 𝓦 ̇) where
      FreePreAlgebra : PreAlgebra T
      FreePreAlgebra = record
        { carrier  = FreeAlgebra T X
        ; carrier-set = quot
        ; algebra  = node'
        }

      isOpen : OpenPreAlgebra T X
      isOpen = record { pre-algebra = FreePreAlgebra ; inj = leaf' }

    module _ {X : 𝓦 ̇} where
      algebra* : Term Σ (FreeAlgebra T X) → FreeAlgebra T X
      algebra* = PreAlgebra.algebra* (FreePreAlgebra X)

      postulate -- HIT 1 and 2-constructors
        eq     : ∀ {t u} → eqs t u → algebra* t == algebra* u

    module _ (X : 𝓦 ̇) where
      FreeAlg : OpenAlgebra T X
      FreeAlg = record
        { open-pre-algebra  = isOpen X
        ; is-algebra        = record { resp-eq = eq }
        }
\end{code}

First, we establish the iteration scheme for free algebras.
This allows the construction of a map into any other T-algebras.
\begin{code}
  module FreeAlgebraIter {𝓤 𝓥 𝓦} {T : AlgTheory 𝓤 𝓥 𝓦} (X : 𝓦 ̇) (𝓐 : OpenAlgebra T X) where
    open OpenAlgebra 𝓐 renaming (carrier to A; algebra to a)
    postulate -- HIT computation and β for 0-constructor
      f : FreeAlgebra T X → A
      leaf-β : ∀ x   → f (leaf' x)    ↦ inj x
      node-β : ∀ s α → f (node' s α)  ↦ a s (f ∘ α)
    {-# REWRITE leaf-β #-}
    {-# REWRITE node-β #-}

  FreeAlgebra-iter = FreeAlgebraIter.f
\end{code}

Next, we provide an induction scheme for the free algebra.
We do not define a general elimination schemes, but restrict it
to induction, that is, we can only prove propositions but cannot eliminate
free algebras into arbitrary sets.
\begin{code}
  module FreeAlgebraInd {𝓤 𝓥 𝓦} {T : AlgTheory 𝓤 𝓥 𝓦} {X : 𝓦 ̇}
                        {𝓣} (Ind : OpenInductiveProp T (FreeAlg X) 𝓣) where
    open OpenInductiveProp Ind renaming (predicate to P)

    postulate -- HIT induction
      f : Π (FreeAlgebra T X) P
       -- Not really useful because we eliminate into a proposition.
      leaf-β : ∀ x    → f (leaf' x)    ↦ base x
      node-β : ∀ s α  → f (node' s α)  ↦ ind s α (f ∘ α)
    {-# REWRITE leaf-β #-}
    {-# REWRITE node-β #-}

  FreeAlgebra-ind = FreeAlgebraInd.f

\end{code}

We prove now that FreeAlgebra is indeed free.
For this the above induction scheme suffices, as the iteration requires an
algebra to be a set.
\begin{code}
module _ {𝓤 𝓥 𝓦} {T : AlgTheory 𝓤 𝓥 𝓦} where
\end{code}

First, we construct the initial homomorphism by iteration.
\begin{code}

  open AlgTheory T renaming (sig to Σ)

  ε : 𝓦 ̇
  ε = ⊥ ↑

  InitialAlgebra : Algebra T
  InitialAlgebra = algebra T (FreeAlg ε)

  mkOpen : (𝓐 : Algebra T) → OpenAlgebra T ε
  mkOpen 𝓐 = record
    { open-pre-algebra = record
      { pre-algebra = 𝓐⁻
      ; inj = λ x → ⊥-elim (x ↧)
      }
    ; is-algebra = 𝓐-is-algebra
    }
    where
      open Algebra 𝓐
        renaming (pre-algebra to 𝓐⁻; is-algebra to 𝓐-is-algebra; carrier to A; algebra to a)

  InitialAlgebra-iter : (𝓐 : Algebra T) → FreeAlgebra T (⊥ ↑) → Algebra.carrier 𝓐
  InitialAlgebra-iter 𝓐 = FreeAlgebra-iter ε (mkOpen 𝓐)

  InitialHom : (𝓐 : Algebra T) → Homomorphism InitialAlgebra 𝓐
  InitialHom 𝓐 = record
    { map = FreeAlgebra-iter ε 𝓐'
    ; resp-ops = resp
    }
    where
      open Algebra 𝓐
        renaming (carrier to A; algebra to a)

      𝓐' : OpenAlgebra T ε
      𝓐' = mkOpen 𝓐

      open OpenAlgebra (FreeAlg {T = T} (⊥ ↑)) renaming (carrier to Ω; algebra to ω)

      resp : (s : sym Σ) (α : ar Σ s → Ω) →
             FreeAlgebra-iter ε 𝓐' (ω s α) == a s (FreeAlgebra-iter ε 𝓐' ∘ α)
      resp s α = idp
\end{code}

And then we prove that it is the unique homomorphism.
Note that the following needs functional extensionality (here via univalence).
For finitary signatures this is, however, not needed because then one only
needs induction on lists.
\begin{code}
  FreeAlg-Initial : IsInitial InitialAlgebra
  FreeAlg-Initial = record
    { !→ = InitialHom
    ; !-unique = FunextNonDep.λ=-nondep ∘ unique
    }
    where
      unique : {𝓑 : Algebra T} (H : Homomorphism InitialAlgebra 𝓑) →
               Homomorphism.map H ∼ InitialAlgebra-iter 𝓑
      unique {𝓑} H = FreeAlgebra-ind Ind
        where
          open Homomorphism H renaming (map to h)
          open Algebra 𝓑
            renaming (carrier to B; algebra to b; resp-eq to b-resp-eq;
              carrier-set to B-is-set)
          open OpenAlgebra (FreeAlg {T = T} ε)
            renaming (carrier to T*; algebra to ω; algebra* to ω*)

          b* : T* → B
          b* = InitialAlgebra-iter 𝓑

          P = λ x → h x == b* x

          ind : (s : sym Σ)
                (α : ar Σ s → T*) →
                ((x : ar Σ s) → h (α x) == InitialAlgebra-iter 𝓑 (α x)) →
                h (ω s α) == InitialAlgebra-iter 𝓑 (ω s α)
          ind s α P =
            h (ω s α)                       =⟨ idp ⟩
            h (node' s α)                   =⟨ resp-ops s α ⟩
            b s (h ∘ α)                     =⟨ ap (b s) (FunextNonDep.λ=-nondep P) ⟩
            InitialAlgebra-iter 𝓑 (ω s α)  =∎

          PE = pre-ind P ind

          open PreInductive PE

          P-is-prop : ∀ x → is-prop (P x)
          P-is-prop x = has-level-apply B-is-set (h x) (b* x)

          ind-resp-eq : ∀{t u} (r : eqs t u)
            → (pt : TermP Σ P t) (pu : TermP Σ P u)
            → ind* pt == ind* pu [ P ↓ resp-eq r ]
          ind-resp-eq {t} {u} t=u pt pu =
            prop-has-all-paths-↓ {{ P-is-prop (ω* u) }}

          Ind : OpenInductiveProp T (FreeAlg ε) 𝓦
          Ind = record
                { open-pre-inductive = record
                  { pre-inductive = PE
                  ; base = λ x → ⊥-elim {𝓦} {λ y → P (inj (y ↥))} (x ↧)
                  }
                ; is-inductive = record
                  { predicate-set = λ x → prop-is-set (P-is-prop x)
                  ; ind-resp-eq = ind-resp-eq
                  }
                }

\end{code}
