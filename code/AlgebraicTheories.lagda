\AgdaHide{
\begin{code}
{-# OPTIONS --without-K --rewriting #-}
\end{code}
}

\begin{code}
module AlgebraicTheories where

open import Universes
open import lib.Basics renaming (_⊔_ to _⊎_) hiding (Σ)
import lib.Basics as B
open import lib.types.Coproduct
open import lib.types.Sigma
open import Terms
\end{code}

An algebraic theory is given by a signature and a set of equations between
terms over that signature.
With an algebraic signature we not only fix the universe level of the
underlying signature but also of algebras for that signature.
This prevents the universe handling from spiraling out of control:
eqs would have to have type ∀ {𝓦} {X : 𝓦 ̇} → Rel (Term sig X) _
and AlgTheory would be in the total universe Uω.
\begin{code}
record AlgTheory (𝓤 𝓥 𝓦) : (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇ where
  field
    sig  : Signature 𝓤 𝓥
    eqs  : ∀ {X : 𝓦 ̇} → Rel (Term sig X) lzero
    -- The following is an internalisation of parametricity. However, we
    -- don't need it for now.
    -- eqs-nat : ∀ {𝓦 𝓦'} {X : 𝓦 ̇} {Y : 𝓦' ̇} (f : X → Y) →
    --           ∀ {t u} → eqs t u → eqs (Term-map f t) (Term-map f u)
\end{code}

Equations can also be represented as a pair of natural transformations
from some functor, which determines the number of equations and the
free variables, to the set of free terms.
\begin{code}
_⟶_ : ∀ 𝓤 𝓣 → (𝓤 ⊔ 𝓣) ⁺ ̇
𝓤 ⟶ 𝓣 = 𝓤 ̇ → 𝓣 ̇

_⇒_ : ∀ {𝓤 𝓥} → 𝓤 ⟶ 𝓥 → 𝓤 ⟶ 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ̇
F ⇒ G = ∀ {X} → F X → G X

IsNat : ∀ {𝓤 𝓥}
        {F : 𝓤 ⟶ 𝓥} (F₁ : ∀ {X Y} → (X → Y) → (F X → F Y))
        {G : 𝓤 ⟶ 𝓥} (G₁ : ∀ {X Y} → (X → Y) → (G X → G Y)) →
        (F ⇒ G) →  𝓤 ⁺ ⊔ 𝓥 ̇
IsNat F₁ G₁ α = ∀ {X Y} (f : X → Y) → α ∘ F₁ f ∼ G₁ f ∘ α

Nat-to-Rel : ∀ {𝓤 𝓥 𝓦} {Σ : Signature 𝓤 𝓥}
             (F : 𝓦 ⟶ (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (l r : F ⇒ Term Σ) →
             ∀ {X : 𝓦 ̇} → Rel (Term Σ X) (𝓤 ⊔ 𝓥 ⊔ 𝓦)
Nat-to-Rel F l r {X} t u = B.Σ (F X) λ x → (l x == t) × (r x == u)

Nat-to-NatRel : ∀ {𝓤 𝓥 𝓦} {Σ : Signature 𝓤 𝓥}
                {F : 𝓦 ⟶ (𝓤 ⊔ 𝓥 ⊔ 𝓦)}
                (F₁ : ∀ {X Y} → (X → Y) → (F X → F Y))
                (l r : F ⇒ Term Σ) (l-nat : IsNat F₁ Term-map l) (r-nat : IsNat F₁ Term-map r)
                {X Y} (f : X → Y) →
                ∀ t u → Nat-to-Rel F l r t u → Nat-to-Rel F l r (Term-map f t) (Term-map f u)
Nat-to-NatRel F₁ l r l-nat r-nat f t u (x , p , q)
  = (F₁ f x , l-nat f x ∙ ap (Term-map f) p , r-nat f x ∙ ap (Term-map f) q )
\end{code}

Given an algebraic theory, we can define algebras and induction schemes for
algebras of that theory.
\begin{code}
module _ {𝓤 𝓥 𝓦} (T : AlgTheory 𝓤 𝓥 𝓦) where
  open AlgTheory T renaming (sig to Σ)
  open Signature Σ renaming (sym to |Σ|)

\end{code}

Algebras are given in two steps: First, we define pre-algebras that do not have
to fulfil the equations of the theory, but only are an algebra for the functor
induced by the signature Σ.
An actual algebra for T is then a pre-algebra that fulfils also the equations.
The reason for splitting the definition is that the pre-algebra has to be turned
into a map from the terms over Σ into the pre-algebra by using freeness, as the
equations can involve complex terms, cf. AlgTheory.
\begin{code}
  record PreAlgebra : (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇ where
    field
      carrier      : 𝓦 ̇
      algebra  : (s : |Σ|) (α : ar Σ s → carrier) → carrier

    algebra* : Term Σ carrier → carrier
    algebra* = Term-rec (λ x → x) algebra

\end{code}

\begin{code}
  record Algebra : (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇ where
    field
      pre-algebra  : PreAlgebra
    open PreAlgebra pre-algebra public
    field
      carrier-set  : is-set carrier
      resp-eq      : ∀ {t u : Term Σ carrier} →
                     eqs t u → algebra* t == algebra* u

\end{code}

For an arbitrary algebra, we can formulate the structure induction hypotheses.
This is basically what Hermida and Jacobs do to obtain general induction schemes
via liftings.
\begin{code}
  module _ (𝓐 : PreAlgebra) where
    open PreAlgebra 𝓐 renaming (carrier to A; algebra to a)

    IndHyp : ∀ {𝓣} (P : A → 𝓣 ̇) (s : |Σ|) (α : ar Σ s → A) → (𝓥 ⊔ 𝓣) ̇
    IndHyp P s α = ⟪ Σ ⟫ P (s , α)

\end{code}

Again, we split the formulation of inductive propositions, which are predicates
over an algebra 𝓐 that can potentially be proven by induction, if 𝓐 supports
induction.
The first part just formulates the usual definition of induction for free structures.
The second part requires then that the predicate is a proposition in the sense of
HoTT.
This requirement is fairly strong, but for now I don't know how to require for a
predicate the preservation of the identities of an algebraic theory.
\begin{code}
  record PreInductive (𝓐 : PreAlgebra) (𝓣) : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇ where
    constructor pre-ind
    open PreAlgebra 𝓐 renaming (carrier to A; algebra to a)
    field
      predicate  : A → 𝓣 ̇
      ind    : (s : |Σ|) (α : ar Σ s → A) → IndHyp 𝓐 predicate s α → predicate (a s α)

    predicate* : Term Σ A → 𝓣 ̇
    predicate* = predicate ∘ algebra*

    ind* : ∀ {t : Term Σ A} → TermP Σ predicate t → predicate* t
    ind* = TermP-rec (idf _) λ s α γ → ind s (algebra* ∘ α) γ

  record InductiveProp  (𝓐 : Algebra) (𝓣) : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇ where
    constructor ind-hyp
    open Algebra 𝓐 renaming (carrier to X; algebra to a)
    field
      pre-inductive : PreInductive pre-algebra 𝓣
    open PreInductive pre-inductive public
    -- field
    --   predicate-prop : ∀ x → is-prop (predicate x)
    field
      ind-resp-eq : ∀{t u} (r : eqs t u)
        → (pt : TermP Σ predicate t) (pu : TermP Σ predicate u)
        → ind* pt == ind* pu [ predicate ↓ resp-eq r ]
\end{code}


We can also consider open T-algebras A over a set X of variables.
These are algebras that additionally have an injection X → A.
\begin{code}
  record IsOpenPreAlgebra  (𝓐 : PreAlgebra) (X : 𝓦 ̇) : (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇ where
    open PreAlgebra 𝓐
    field
      inj : X → carrier

    inj* : Term Σ X → carrier
    inj* = Term-rec inj algebra

    eval : ⟦ Σ ⟧ (X ⊎ carrier) → carrier
    eval (s , α) = algebra s (Coprod-rec inj (idf _) ∘ α)

    eval* : Term Σ (X ⊎ carrier) → carrier
    eval* = Term-rec (Coprod-rec inj (idf _)) algebra

  record OpenAlgebra  (X : 𝓦 ̇) : (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇ where
    field
      alg : Algebra
    open Algebra alg public
    field
      is-open : IsOpenPreAlgebra pre-algebra X
    open IsOpenPreAlgebra is-open public
    field
      inj-resp-eq : ∀ {t u : Term Σ (X ⊎ carrier)} → eqs t u → eval* t == eval* u
\end{code}

Open algebras may also come with an induction principle.
\begin{code}
  record PreOpenInductive (𝓐 : PreAlgebra) (𝓣) (X : 𝓦 ̇)
         : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇ where
    open PreAlgebra 𝓐 renaming (carrier to A; algebra to a)
    field
      pre-inductive : PreInductive 𝓐 𝓣
      is-open : IsOpenPreAlgebra 𝓐 X
    open PreInductive pre-inductive public
    open IsOpenPreAlgebra is-open

    -- predicate* : Term Σ X → 𝓣 ̇
    -- predicate* = predicate ∘ algebra* ∘ Term-map inj

    -- ind* : (∀ x → predicate (inj x)) → ∀ (t : Term Σ X) → predicate* t
    -- ind* p = Term-elim p λ s α → ind s (algebra* ∘ Term-map inj ∘ α)

  record OpenInductiveProp  (𝓐 : Algebra) (𝓣) (X : 𝓦 ̇) : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇ where
    constructor ind-hyp
    open Algebra 𝓐 renaming (carrier to A; algebra to a)
    field
      pre-open-inductive : PreOpenInductive pre-algebra 𝓣 X
    open PreOpenInductive pre-open-inductive public
    field
      predicate-prop : ∀ x → is-prop (predicate x)
\end{code}

Finally, we can also define homomorphisms and isomorphisms of algebras, initial algebras,
and show that the identity is always a homomorphism.
\begin{code}
module _ {𝓤 𝓥 𝓦} {T : AlgTheory 𝓤 𝓥 𝓦} where
  open AlgTheory T renaming (sig to Σ)
  open Signature Σ renaming (sym to |Σ|)

  record Homomorphism (𝓐 : Algebra T) (𝓑 : Algebra T) : (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇ where
    open Algebra 𝓐 renaming (carrier to A; algebra to a)
    open Algebra 𝓑 renaming (carrier to Y; algebra to b)
    field
      map       : A → Y
      resp-ops  : ∀ (s : |Σ|) (α : ar Σ s → A) → map (a s α) == b s (map ∘ α)

  id-hom : ∀ (𝓐 : Algebra T) → Homomorphism 𝓐 𝓐
  id-hom 𝓐 = record { map = idf (Algebra.carrier 𝓐) ; resp-ops = λ s α → idp }

  record _≅_ (𝓐 : Algebra T) (𝓑 : Algebra T) : (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇ where
    field
      from  : Homomorphism 𝓐 𝓑
      to    : Homomorphism 𝓑 𝓐
      inv₁  : Homomorphism.map from ∘ Homomorphism.map to == idf _
      inv₂  : Homomorphism.map to ∘ Homomorphism.map from == idf _

  record IsInitial (𝓐 : Algebra T) : (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇ where
    field
      !→ : (𝓑 : Algebra T) → Homomorphism 𝓐 𝓑
      !-unique : {𝓑 : Algebra T} (h : Homomorphism 𝓐 𝓑) →
                 Homomorphism.map h == Homomorphism.map (!→ 𝓑)


    -- TODO: Define FreeAlgebras as initial among open algebras.
\end{code}
