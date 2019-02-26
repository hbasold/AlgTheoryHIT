We generate the free algebra for an algebraic theory as a HIT,
or rather a 1-truncated HIT or quotient inductive type (QIT).

\begin{code}
{-# OPTIONS --without-K --rewriting #-}

module FreeAlgebra where

open import Universes
open import lib.Basics renaming (_⊔_ to +)
open import lib.NType2
open import Terms
open import AlgebraicTheories
\end{code}

\begin{code}
module _ where
  postulate -- HIT type
    FreeAlgebra : ∀ {𝓤} (T : AlgTheory 𝓤₀ 𝓤₀ 𝓤) → 𝓤 ̇

  module _ {𝓤} {T : AlgTheory 𝓤₀ 𝓤₀ 𝓤} where
    open AlgTheory T

    postulate -- HIT 0-constructor
      node'  : (s : sym sig) (α : ar sig s → FreeAlgebra T) → FreeAlgebra T

    FreePreAlgebra : PreAlgebra T
    FreePreAlgebra = record
      { carrier      = FreeAlgebra T
      ; algebra  = node'
      }

    algebra* : Term sig (FreeAlgebra T) → FreeAlgebra T
    algebra* = PreAlgebra.algebra* FreePreAlgebra

    postulate -- HIT 1 and 2-constructors
      eq     : ∀ {t u} → eqs t u → algebra* t == algebra* u
      quot   : is-set (FreeAlgebra T)

    FreeAlg : Algebra T
    FreeAlg = record
      { pre-algebra = FreePreAlgebra
      ; carrier-set  = quot
      ; resp-eq = eq
      }
\end{code}

First, we establish the iteration scheme for free algebras.
This allows the construction of a map into any other T-algebras.
\begin{code}
  module FreeAlgebraIter {𝓤} {T : AlgTheory 𝓤₀ 𝓤₀ 𝓤} (A : Algebra T) where
    open AlgTheory T
    open Algebra A
      renaming (carrier to X; algebra to β)

    postulate -- HIT computation and β for 0-constructor
      f : FreeAlgebra T → X
      node-β : ∀ s α → f (node' s α) ↦ β s (f ∘ α)
    {-# REWRITE node-β #-}

  FreeAlgebra-iter = FreeAlgebraIter.f
\end{code}

Next, we provide an induction scheme for the free algebra.
We do not define a general elimination schemes, but restrict it
to induction, that is, we can only prove propositions but cannot eliminate
free algebras into arbitrary sets.
\begin{code}
  module FreeAlgebraInd {𝓤} {T : AlgTheory 𝓤₀ 𝓤₀ 𝓤} {𝓥} (Ind : InductiveProp T FreeAlg 𝓥)  where
    open AlgTheory T
    open InductiveProp Ind renaming (predicate to P)

    postulate -- HIT induction
      f : Π (FreeAlgebra T) P
       -- Not really useful because we eliminate into a proposition.
      node-β : ∀ s α → f (node' s α) ↦ ind s α (f ∘ α)
    {-# REWRITE node-β #-}

  FreeAlgebra-ind = FreeAlgebraInd.f

\end{code}

We prove now that FreeAlgebra is indeed free.
For this the above induction scheme suffices, as the iteration requires an
algebra to be a set.
\begin{code}
module _ {𝓤} {T : AlgTheory 𝓤₀ 𝓤₀ 𝓤} where
\end{code}

First, we construct the homomorphism by iteration.
\begin{code}
  FreeHom : ∀ (𝓐 : Algebra T) → Homomorphism FreeAlg 𝓐
  FreeHom 𝓐 = record
    { map = FreeAlgebra-iter 𝓐
    ; resp-ops = resp
    }
    where
      open AlgTheory T
      open Algebra 𝓐 renaming (carrier to A; algebra to a)
      open Algebra (FreeAlg {T = T}) renaming (carrier to Ω; algebra to ω)

      resp : (s : sym sig) (α : ar sig s → Ω) →
             FreeAlgebra-iter 𝓐 (ω s α) == a s (FreeAlgebra-iter 𝓐 ∘ α)
      resp s α = idp
\end{code}

And then we prove that it is the unique homomorphism.
Note that the following needs functional extensionality (here via univalence).
For finitary signatures this is, however, not needed because then one only
needs induction on lists.
\begin{code}
  FreeAlg-Initial : IsInitial FreeAlg
  FreeAlg-Initial = record
    { !→ = FreeHom
    ; !-unique = FunextNonDep.λ=-nondep ∘ unique
    }
    where
      unique : {𝓑 : Algebra T} (H : Homomorphism FreeAlg 𝓑) →
               Homomorphism.map H ∼ FreeAlgebra-iter 𝓑
      unique {𝓑} H = FreeAlgebra-ind (ind-hyp PE P-is-prop)
        where
          open AlgTheory T
          open Homomorphism H renaming (map to h)
          open Algebra 𝓑
            renaming (carrier to B; algebra to b; resp-eq to b-resp-eq;
              carrier-set to B-is-set)
          open Algebra (FreeAlg {T = T})
            renaming (carrier to T*; algebra to ω)

          b* : T* → B
          b* = FreeAlgebra-iter 𝓑

          P = λ x → h x == b* x

          ind : (s : sym sig)
                (α : ar sig s → T*) →
                ((x : ar sig s) → h (α x) == FreeAlgebra-iter 𝓑 (α x)) →
                h (ω s α) == FreeAlgebra-iter 𝓑 (ω s α)
          ind s α P =
            h (ω s α)                    =⟨ idp ⟩
            h (node' s α)                =⟨ resp-ops s α ⟩
            b s (h ∘ α)                  =⟨ ap (b s) (FunextNonDep.λ=-nondep P) ⟩
            FreeAlgebra-iter 𝓑 (ω s α)  =∎

          PE = pre-ind P ind

          P-is-prop : ∀ x → is-prop (P x)
          P-is-prop x = has-level-apply B-is-set (h x) (FreeAlgebra-iter 𝓑 x)
\end{code}
