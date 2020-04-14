{-# OPTIONS --postfix-projections #-}

module Poset where

  open import Function.Base using (id; _∘_)
  open import Level using (0ℓ)
  open import Relation.Binary using (Rel; REL; Reflexive; Transitive)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  record RelGr : Set₁ where
    field
      Carrier : Set
      rel : Rel Carrier 0ℓ

  record Poset : Set₁ where
    field
      relGr : RelGr
    open RelGr relGr public
    field
      refl : Reflexive rel
      trans : Transitive rel

  record Mor {I J : Set} (R : Rel I 0ℓ) (S : Rel J 0ℓ) : Set where
    field
      act : I → J
      pres : ∀ {A B} → R A B → S (act A) (act B)
  open Mor public

  record RelGrMor (R S : RelGr) : Set where
    open RelGr
    field mor : Mor (R .rel) (S .rel)
  open RelGrMor public

  record PosetMor (R S : Poset) : Set where
    open Poset
    field mor : Mor (R .rel) (S .rel)
  open PosetMor public

  U : Poset → RelGr
  U = Poset.relGr

  module WithStuff (relGr : RelGr) where
    open RelGr relGr renaming (Carrier to I; rel to G)

    data _⊢_ : I → I → Set where
      const : {A B : I} → G A B
                        → -----
                          A ⊢ B
      init : {A : I} → -----
                       A ⊢ A
      cut : {A B C : I} → A ⊢ B  →  B ⊢ C
                        → ---------------
                               A ⊢ C

    module _ {A B C D E} (ab : G A B) (ac : G A C) (da : G D A) (be : G B E) (dc : G D C) where
      test : D ⊢ E
      test = cut (cut (const da) (const ab)) (const be)

    ⊢-poset : Poset
    ⊢-poset .Poset.relGr .RelGr.Carrier = I
    ⊢-poset .Poset.relGr .RelGr.rel = _⊢_
    ⊢-poset .Poset.refl = init
    ⊢-poset .Poset.trans = cut

  module _ {G P} where

    open WithStuff using (const; init; cut; ⊢-poset)
    open RelGr G
    open Poset P

    rl : RelGrMor G (U P) → PosetMor (⊢-poset G) P
    rl f .mor .act = f .mor .act
    rl f .mor .pres (const GAB) = f .mor .pres GAB
    rl f .mor .pres init = refl
    rl f .mor .pres (cut A⊢B B⊢C) = trans (rl f .mor .pres A⊢B) (rl f .mor .pres B⊢C)

    lr : PosetMor (⊢-poset G) P → RelGrMor G (U P)
    lr f .mor .act = f .mor .act
    lr f .mor .pres GAB = f .mor .pres (const GAB)

  {-
           F
       ↗--------↘
  RelGr    ⊥     Poset
       ↖--------↙
           U

  Mor (F X) Y
  -----------
  Mor X (U Y)
  -}
