{-# OPTIONS --postfix-projections #-}

module Semilattice where

  open import Function.Base using (id; _∘_)
  open import Level using (0ℓ)
  open import Relation.Binary using (Rel; REL; Reflexive; Transitive)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  record RelGr : Set₁ where
    field
      Carrier : Set
      rel : Rel Carrier 0ℓ

  record Semilattice : Set₁ where
    infixr 6 _∧_
    field
      relGr : RelGr
    open RelGr relGr public renaming (rel to infix 4 _≤_)
    field
      refl : Reflexive _≤_
      trans : Transitive _≤_
      ⊤ : Carrier
      _∧_ : (x y : Carrier) → Carrier
      ⊤≥ : ∀ {x} → x ≤ ⊤
      prl : ∀ {x y} → x ∧ y ≤ x
      prr : ∀ {x y} → x ∧ y ≤ y
      ∧≥ : ∀ {x y z} → z ≤ x → z ≤ y → z ≤ x ∧ y

  record Mor {I J : Set} (R : Rel I 0ℓ) (S : Rel J 0ℓ) : Set where
    field
      act : I → J
      pres : ∀ {A B} → R A B → S (act A) (act B)
  open Mor public

  record RelGrMor (R S : RelGr) : Set where
    open RelGr
    field mor : Mor (R .rel) (S .rel)
  open RelGrMor public

  record SemilatticeMor (R S : Semilattice) : Set where
    open Semilattice
    field mor : Mor (R ._≤_) (S ._≤_)
  open SemilatticeMor public

  U : Semilattice → RelGr
  U = Semilattice.relGr

  module WithStuff (relGr : RelGr) where
    open RelGr relGr renaming (Carrier to I; rel to G)

    infixr 6 _t∧_
    infix 4 _⊢_ _nd⊢_

    data Ty : Set where
      ι : (X : I) → Ty
      t⊤ : Ty
      _t∧_ : (A B : Ty) → Ty

    variable
      A B C : Ty
      X Y Z : I

    data _⊢_ : (A B : Ty) → Set where
      init : A ⊢ A
      cut : A ⊢ B → B ⊢ C → A ⊢ C
      fI : (f : G X Y) → ι X ⊢ ι Y
      ⊤I : A ⊢ t⊤
      ∧E1 : B t∧ C ⊢ B
      ∧E2 : B t∧ C ⊢ C
      ∧I : A ⊢ B → A ⊢ C → A ⊢ B t∧ C

    data _nd⊢_ : (A B : Ty) → Set where
      var : A nd⊢ A
      fI : (f : G X Y) → A nd⊢ ι X → A nd⊢ ι Y
      ⊤I : A nd⊢ t⊤
      ∧E1 : A nd⊢ B t∧ C → A nd⊢ B
      ∧E2 : A nd⊢ B t∧ C → A nd⊢ C
      ∧I : A nd⊢ B → A nd⊢ C → A nd⊢ B t∧ C

    cut-intro-nd : A nd⊢ B → A ⊢ B
    cut-intro-nd var = init
    cut-intro-nd (fI f d) = cut (cut-intro-nd d) (fI f)
    cut-intro-nd ⊤I = ⊤I
    cut-intro-nd (∧E1 d) = cut (cut-intro-nd d) ∧E1
    cut-intro-nd (∧E2 d) = cut (cut-intro-nd d) ∧E2
    cut-intro-nd (∧I d e) = ∧I (cut-intro-nd d) (cut-intro-nd e)

    subst : A nd⊢ B → B nd⊢ C → A nd⊢ C
    subst AB var = AB
    subst AB (fI f BC) = fI f (subst AB BC)
    subst AB ⊤I = ⊤I
    subst AB (∧E1 B∧) = ∧E1 (subst AB B∧)
    subst AB (∧E2 B∧) = ∧E2 (subst AB B∧)
    subst AB (∧I BC BD) = ∧I (subst AB BC) (subst AB BD)

    cut-elim-nd : A ⊢ B → A nd⊢ B
    cut-elim-nd init = var
    cut-elim-nd (cut d e) = subst (cut-elim-nd d) (cut-elim-nd e)
    cut-elim-nd (fI f) = fI f var
    cut-elim-nd ⊤I = ⊤I
    cut-elim-nd ∧E1 = ∧E1 var
    cut-elim-nd ∧E2 = ∧E2 var
    cut-elim-nd (∧I d e) = ∧I (cut-elim-nd d) (cut-elim-nd e)

    ⊢-semilattice : Semilattice
    ⊢-semilattice .Semilattice.relGr .RelGr.Carrier = Ty
    ⊢-semilattice .Semilattice.relGr .RelGr.rel = _nd⊢_
    ⊢-semilattice .Semilattice.refl = var
    ⊢-semilattice .Semilattice.trans = subst
    ⊢-semilattice .Semilattice.⊤ = t⊤
    ⊢-semilattice .Semilattice._∧_ = _t∧_
    ⊢-semilattice .Semilattice.⊤≥ = ⊤I
    ⊢-semilattice .Semilattice.prl = ∧E1 var
    ⊢-semilattice .Semilattice.prr = ∧E2 var
    ⊢-semilattice .Semilattice.∧≥ = ∧I

  module _ {G P} where

    open WithStuff
    open RelGr G
    open Semilattice P

    ⟦_⟧Ty : Ty G → (RelGr.Carrier G → Semilattice.Carrier P) →
            Semilattice.Carrier P
    ⟦ ι X ⟧Ty f = f X
    ⟦ t⊤ ⟧Ty f = ⊤
    ⟦ A t∧ B ⟧Ty f = ⟦ A ⟧Ty f ∧ ⟦ B ⟧Ty f

    rl : RelGrMor G (U P) → SemilatticeMor (⊢-semilattice G) P
    rl f .mor .act A = ⟦ A ⟧Ty (f .mor .act)
    rl f .mor .pres = go ∘ cut-intro-nd _
      where
      go : _⊢_ G A B → rl f .mor .act A ≤ rl f .mor .act B
      go init = refl
      go (cut d e) = trans (go d) (go e)
      go (fI g) = f .mor .pres g
      go ⊤I = ⊤≥
      go ∧E1 = prl
      go ∧E2 = prr
      go (∧I d e) = ∧≥ (go d) (go e)

    lr : SemilatticeMor (⊢-semilattice G) P → RelGrMor G (U P)
    lr f .mor .act = f .mor .act ∘ ι
    lr f .mor .pres GAB = f .mor .pres (fI GAB var)

  {-
           F
       ↗--------↘
  RelGr    ⊥     Semilattice
       ↖--------↙
           U

  Mor (F X) Y
  -----------
  Mor X (U Y)
  -}
