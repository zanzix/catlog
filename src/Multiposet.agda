{-# OPTIONS --postfix-projections #-}
module Multiposet where

  open import Data.List as L
  open import Data.List.Properties
  open import Data.List.Relation.Binary.Pointwise as Pw
  open import Data.List.Relation.Ternary.Interleaving.Propositional as In
  open import Function.Base as F using (_$_)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡ hiding ([_])

  record MultiGraph o ℓ : Set (suc (o ⊔ ℓ)) where
    field
      Obj : Set o
      Hom : List Obj → Obj → Set ℓ

  record MultiPoset o ℓ : Set (suc (o ⊔ ℓ)) where
    field
      Obj : Set o
      Hom : List Obj → Obj → Set ℓ
      id : ∀ {x} → Hom [ x ] x
      _∘_ : ∀ {xss ys z} →
            Pointwise Hom xss ys → Hom ys z → Hom (concat xss) z

  module _ {a} {A : Set a} where

    Insert : A → List A → List A → Set a
    Insert x ys xys = Interleaving [ x ] ys xys

    insert : ∀ {x : A} {ys xys} →
             Insert x ys xys → List A → List A
    insert {ys = ys} (consˡ i) xs = xs ++ ys
    insert {ys = y ∷ ys} (consʳ i) xs = y ∷ insert i xs

    insert′ : ∀ {x : A} {ys xys} →
              Insert x ys xys → List A → List (List A)
    insert′ {ys = ys} (consˡ i) xs = xs ∷ L.map [_] ys
    insert′ {ys = y ∷ ys} (consʳ i) xs = [ y ] ∷ insert′ i xs

    join-pure : (xs : List A) → concat (L.map [_] xs) ≡ xs
    join-pure [] = ≡.refl
    join-pure (x ∷ xs) = cong (x ∷_) (join-pure xs)

    concat-insert′ : ∀ {x : A} {ys xys} (i : Insert x ys xys) xs →
                     concat (insert′ i xs) ≡ insert i xs
    concat-insert′ (consˡ i) xs = cong (xs ++_) (join-pure _)
    concat-insert′ (consʳ i) xs = cong (_ ∷_) (concat-insert′ i xs)

  record MultiPoset′ o ℓ : Set (suc (o ⊔ ℓ)) where
    field
      Obj : Set o
      Hom : List Obj → Obj → Set ℓ
      id : ∀ {x} → Hom [ x ] x
      comp : ∀ {xs y ys yys z} → (i : Insert y ys yys) →
             Hom xs y → Hom yys z → Hom (insert i xs) z

  module _ {o ℓ : Level} where

    open MultiPoset
    open MultiPoset′

    MultiPoset→MultiPoset′ : MultiPoset o ℓ → MultiPoset′ o ℓ
    MultiPoset→MultiPoset′ P .Obj = P .Obj
    MultiPoset→MultiPoset′ P .Hom = P .Hom
    MultiPoset→MultiPoset′ P .id = P .id
    MultiPoset→MultiPoset′ P .comp i f g =
      subst (λ xs → P .Hom xs _) (concat-insert′ i _) (P ._∘_ (foo i f) g)
      where

      foo : ∀ {y : P .Obj} {ys yys xs : List (P .Obj)}
            (i : Insert y ys yys) (f : P .Hom xs y) →
            Pointwise (P .Hom) (insert′ i xs) yys
      foo (consˡ i) f = f ∷ go i
        where
        go : ∀ {ys ys′} →
             Interleaving [] ys ys′ → Pointwise (P .Hom) (L.map [_] ys) ys′
        go [] = []
        go (consʳ i) = P .id ∷ go i
      foo (consʳ i) f = P .id ∷ foo i f

  module _
    {a b r} {A : Set a} {B : Set b} (R : A → B → Set r)
    where

    data Append : (xs : List A) (ys zs : List B) → Set r where
      [] : ∀ {ys} → Append [] ys ys
      _∷_ : ∀ {x z xs ys zs} →
            R x z → Append xs ys zs → Append (x ∷ xs) ys (z ∷ zs)

    data Concat : (xss : List (List A)) (ys : List B) → Set (b ⊔ r) where
      [] : Concat [] []
      _∷_ : ∀ {xs ys xsys xss} →
            Append xs ys xsys → Concat xss ys → Concat (xs ∷ xss) xsys

  pattern cons as = ≡.refl ∷ as

  module _
    {a b r} {A : Set a} {B : Set b} {R : A → B → Set r}
    where

    Append-[] : ∀ {xs ys} → Append R xs [] ys → Pointwise R xs ys
    Append-[] [] = []
    Append-[] (a ∷ as) = a ∷ Append-[] as

  module WithMultiGraph {o ℓ} (G : MultiGraph o ℓ) where

    open MultiGraph

    infix 6 _⊗_

    data Ty : Set o where
      ι : G .Obj → Ty
      I : Ty
      _⊗_ : (A B : Ty) → Ty

    infix 4 _sc⊢_

    data _sc⊢_ : List Ty → Ty → Set (o ⊔ ℓ) where
      init : ∀ {X} → [ ι X ] sc⊢ ι X
      graph : ∀ {Γs Γ Xs Y} → G .Hom Xs Y → Concat _≡_ Γs Γ →
              Pointwise (λ Γ X → Γ sc⊢ ι X) Γs Xs → Γ sc⊢ ι Y
      IL : ∀ {Γ,I,Δ Γ,Δ A} → Insert I Γ,Δ Γ,I,Δ → Γ,Δ sc⊢ A → Γ,I,Δ sc⊢ A
      IR : [] sc⊢ I
      ⊗L : ∀ {Γ,A⊗B,Δ Γ,Δ A B C} (i : Insert (A ⊗ B) Γ,Δ Γ,A⊗B,Δ) →
           insert i (A ∷ B ∷ []) sc⊢ C → Γ,A⊗B,Δ sc⊢ C
      ⊗R : ∀ {Γ Δ Γ,Δ A B} → Append _≡_ Γ Δ Γ,Δ →
           Γ sc⊢ A → Δ sc⊢ B → Γ,Δ sc⊢ A ⊗ B

    init* : ∀ {A} → [ A ] sc⊢ A
    init* {ι x} = init
    init* {I} = IL (consˡ []) IR
    init* {A ⊗ B} = ⊗L (consˡ []) (⊗R (cons []) init* init*)

    multicut : ∀ {Ψs Ψ As B} → Concat _≡_ Ψs Ψ →
               Pointwise _sc⊢_ Ψs As → As sc⊢ B → Ψ sc⊢ B
    multicut c ds (graph f c′ es) = graph f ? {!multicut c!}
      -- let foo = Pw.map {!!} ds in
      -- graph f {!foo!}
    multicut c ds (IL i e) = {!!}
    multicut c ds IR = {!!}
    multicut c ds (⊗L i e) = {!!}
    multicut c ds (⊗R as e f) = {!!}
    multicut (as ∷ []) (d ∷ []) init rewrite Pointwise-≡⇒≡ (Append-[] as) = d
