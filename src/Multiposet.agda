{-# OPTIONS --postfix-projections #-}
module Multiposet where

  open import Data.List as L
  open import Data.List.Properties
  open import Data.List.Relation.Binary.Pointwise
  open import Data.List.Relation.Ternary.Interleaving.Propositional as In
  open import Function.Base as F using (_$_)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡ hiding ([_])

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
