{-# OPTIONS --postfix-projections #-}

module CategoryWithProducts where

  open import Data.Product as × using (_,_)
  import Function.Base as F
  open import Level
  open import Relation.Binary hiding (_⇒_)
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; inspect)

  open import Categories.Category
  open import Categories.Category.Cartesian
  open import Categories.Category.Construction.Graphs
    hiding (refl; trans; sym)
  open import Categories.Functor hiding (id)
  open import Categories.Object.Terminal
  open import Categories.Object.Product
  open import Categories.NaturalTransformation
    using (NaturalTransformation; NTHelper; ntHelper)
  open import Categories.NaturalTransformation.NaturalIsomorphism as NI
    using (NaturalIsomorphism; NIHelper; niHelper)
  open import Categories.Category.Instance.One
  open import Categories.Category.Product as ×ᶜ renaming (Product to _×ᶜ_)
    renaming (_⁂_ to _⁂F_)
  import Categories.Object.Product.Morphisms as ×Mor

  private
    variable
      o ℓ e o′ ℓ′ e′ : Level

  record CartesianCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
    field
      category : Category o ℓ e
      cartesian : Cartesian category
    open Category category public
    open Cartesian cartesian public

    module _ where
      open Functor
      open Equiv

      ⊤F : Functor One0 category
      ⊤F .F₀ _ = ⊤
      ⊤F .F₁ _ = id
      ⊤F .identity = refl
      ⊤F .homomorphism = sym identity²
      ⊤F .F-resp-≈ _ = refl

      ×F : Functor (category ×ᶜ category) category
      ×F .F₀ (x , y) = x × y
      ×F .F₁ (f , g) = f ⁂ g
      ×F .identity = unique (trans identityʳ (sym identityˡ))
                            (trans identityʳ (sym identityˡ))
      ×F .homomorphism = sym ⁂∘⁂
      ×F .F-resp-≈ (ff , gg) = ⁂-cong₂ ff gg

  record CartesianFunctor (C : CartesianCategory o ℓ e)
                          (D : CartesianCategory o′ ℓ′ e′)
                          : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    open CartesianCategory using (category)
    field
      functor : Functor (C .category) (D .category)
    open Functor functor public
    open CartesianCategory D hiding (category)
    open Equiv
    private
      module C = CartesianCategory C
      module CE = C.Equiv
    field
      ⊤-iso : NaturalIsomorphism (functor ∘F C.⊤F) ⊤F
      ×-iso : NaturalIsomorphism (functor ∘F C.×F) (×F ∘F (functor ⁂F functor))

  module _ where
    open Graph
    open CartesianCategory

    forget : CartesianCategory o ℓ e → Graph o ℓ e
    forget C .Obj = C .Obj
    forget C ._⇒_ = C ._⇒_
    forget C ._≈_ = C ._≈_
    forget C .equiv = C .equiv

  module NaturalDeduction {o ℓ e} (graph : Graph o ℓ e) where
    open Graph graph
    open Equiv

    infixr 6 _t∧_
    infix 4 _⊢_

    data Ty : Set o where
      ι : (X : Obj) → Ty
      t⊤ : Ty
      _t∧_ : (A B : Ty) → Ty

    private
      variable
        X Y Z : Obj
        A B C D : Ty

    data _⊢_ : (A B : Ty) → Set (o ⊔ ℓ) where
      var : A ⊢ A
      fI : (f : X ⇒ Y) → A ⊢ ι X → A ⊢ ι Y
      ⊤I : A ⊢ t⊤
      ∧E1 : A ⊢ B t∧ C → A ⊢ B
      ∧E2 : A ⊢ B t∧ C → A ⊢ C
      ∧I : A ⊢ B → A ⊢ C → A ⊢ B t∧ C

    private
      variable
        M M′ N N′ O O′ : _ ⊢ _

    data [_⊢_]_≡_ : (A B : Ty) → Rel (A ⊢ B) (o ⊔ ℓ ⊔ e) where
      ≡-refl : [ A ⊢ B ] M ≡ M
      ≡-trans : [ A ⊢ B ] M ≡ N → [ A ⊢ B ] N ≡ O → [ A ⊢ B ] M ≡ O
      ≡-sym : [ A ⊢ B ] M ≡ N → [ A ⊢ B ] N ≡ M

      fI-cong : ∀ {f f′} → f ≈ f′ → [ D ⊢ ι X ] M ≡ M′ →
                [ D ⊢ ι Y ] fI f M ≡ fI f′ M′
      ∧E1-cong : [ D ⊢ A t∧ B ] M ≡ M′ → [ D ⊢ A ] ∧E1 M ≡ ∧E1 M′
      ∧E2-cong : [ D ⊢ A t∧ B ] M ≡ M′ → [ D ⊢ B ] ∧E2 M ≡ ∧E2 M′
      ∧I-cong : [ D ⊢ A ] M ≡ M′ → [ D ⊢ B ] N ≡ N′ →
                [ D ⊢ A t∧ B ] ∧I M N ≡ ∧I M′ N′

      ∧β1 : [ D ⊢ A ] ∧E1 (∧I M N) ≡ M
      ∧β2 : [ D ⊢ B ] ∧E2 (∧I M N) ≡ N
      ∧η : [ D ⊢ A t∧ B ] M ≡ ∧I (∧E1 M) (∧E2 M)
      ⊤η : [ D ⊢ t⊤ ] M ≡ ⊤I

    subst : A ⊢ B → B ⊢ C → A ⊢ C
    subst M var = M
    subst M (fI f N) = fI f (subst M N)
    subst M ⊤I = ⊤I
    subst M (∧E1 N) = ∧E1 (subst M N)
    subst M (∧E2 N) = ∧E2 (subst M N)
    subst M (∧I N O) = ∧I (subst M N) (subst M O)

    subst-congˡ : [ A ⊢ B ] M ≡ M′ → (N : B ⊢ C) →
                  [ A ⊢ C ] subst M N ≡ subst M′ N
    subst-congˡ MM var = MM
    subst-congˡ MM (fI f N) = fI-cong refl (subst-congˡ MM N)
    subst-congˡ MM ⊤I = ≡-refl
    subst-congˡ MM (∧E1 N) = ∧E1-cong (subst-congˡ MM N)
    subst-congˡ MM (∧E2 N) = ∧E2-cong (subst-congˡ MM N)
    subst-congˡ MM (∧I N O) = ∧I-cong (subst-congˡ MM N) (subst-congˡ MM O)

    subst-congʳ : (M : A ⊢ B) → [ B ⊢ C ] N ≡ N′ →
                  [ A ⊢ C ] subst M N ≡ subst M N′
    subst-congʳ M ≡-refl = ≡-refl
    subst-congʳ M (≡-trans NN OO) = ≡-trans (subst-congʳ M NN) (subst-congʳ M OO)
    subst-congʳ M (≡-sym NN) = ≡-sym (subst-congʳ M NN)
    subst-congʳ M (fI-cong ff NN) = fI-cong ff (subst-congʳ M NN)
    subst-congʳ M (∧E1-cong NN) = ∧E1-cong (subst-congʳ M NN)
    subst-congʳ M (∧E2-cong NN) = ∧E2-cong (subst-congʳ M NN)
    subst-congʳ M (∧I-cong NN OO) = ∧I-cong (subst-congʳ M NN) (subst-congʳ M OO)
    subst-congʳ M ∧β1 = ∧β1
    subst-congʳ M ∧β2 = ∧β2
    subst-congʳ M ∧η = ∧η
    subst-congʳ M ⊤η = ⊤η

    subst-cong : [ A ⊢ B ] M ≡ M′ → [ B ⊢ C ] N ≡ N′ →
                 [ A ⊢ C ] subst M N ≡ subst M′ N′
    subst-cong MM NN = ≡-trans (subst-congˡ MM _) (subst-congʳ _ NN)

    subst-assoc : (M : A ⊢ B) (N : B ⊢ C) (O : C ⊢ D) →
      [ A ⊢ D ] subst (subst M N) O ≡ subst M (subst N O)
    subst-assoc M N var = ≡-refl
    subst-assoc M N (fI f O) = fI-cong refl (subst-assoc M N O)
    subst-assoc M N ⊤I = ≡-refl
    subst-assoc M N (∧E1 O) = ∧E1-cong (subst-assoc M N O)
    subst-assoc M N (∧E2 O) = ∧E2-cong (subst-assoc M N O)
    subst-assoc M N (∧I O P) = ∧I-cong (subst-assoc M N O) (subst-assoc M N P)

    subst-identityˡ : ∀ M → [ A ⊢ B ] subst var M ≡ M
    subst-identityˡ var = ≡-refl
    subst-identityˡ (fI f M) = fI-cong refl (subst-identityˡ M)
    subst-identityˡ ⊤I = ≡-refl
    subst-identityˡ (∧E1 M) = ∧E1-cong (subst-identityˡ M)
    subst-identityˡ (∧E2 M) = ∧E2-cong (subst-identityˡ M)
    subst-identityˡ (∧I M N) = ∧I-cong (subst-identityˡ M) (subst-identityˡ N)

    module _ where
      open CartesianCategory
      open Category
      open IsEquivalence
      open Cartesian
      open Terminal
      open BinaryProducts
      open Product

      ⊢-cartesianCategory : CartesianCategory o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
      ⊢-cartesianCategory .category .Obj = Ty
      ⊢-cartesianCategory .category ._⇒_ = _⊢_
      ⊢-cartesianCategory .category ._≈_ = [ _ ⊢ _ ]_≡_
      ⊢-cartesianCategory .category .id = var
      ⊢-cartesianCategory .category ._∘_ = F.flip subst
      ⊢-cartesianCategory .category .assoc {f = M} {N} {O} = ≡-sym (subst-assoc M N O)
      ⊢-cartesianCategory .category .sym-assoc {f = M} {N} {O} = subst-assoc M N O
      ⊢-cartesianCategory .category .identityˡ = ≡-refl
      ⊢-cartesianCategory .category .identityʳ = subst-identityˡ _
      ⊢-cartesianCategory .category .identity² = ≡-refl
      ⊢-cartesianCategory .category .equiv .refl = ≡-refl
      ⊢-cartesianCategory .category .equiv .sym = ≡-sym
      ⊢-cartesianCategory .category .equiv .trans = ≡-trans
      ⊢-cartesianCategory .category .∘-resp-≈ = F.flip subst-cong
      ⊢-cartesianCategory .cartesian .terminal .⊤ = t⊤
      ⊢-cartesianCategory .cartesian .terminal .! = ⊤I
      ⊢-cartesianCategory .cartesian .terminal .!-unique M = ≡-sym ⊤η
      ⊢-cartesianCategory .cartesian .products .BinaryProducts.product {A} {B} .A×B = A t∧ B
      ⊢-cartesianCategory .cartesian .products .BinaryProducts.product .π₁ = ∧E1 var
      ⊢-cartesianCategory .cartesian .products .BinaryProducts.product .π₂ = ∧E2 var
      ⊢-cartesianCategory .cartesian .products .BinaryProducts.product .Product.⟨_,_⟩ = ∧I
      ⊢-cartesianCategory .cartesian .products .BinaryProducts.product .project₁ = ∧β1
      ⊢-cartesianCategory .cartesian .products .BinaryProducts.product .project₂ = ∧β2
      ⊢-cartesianCategory .cartesian .products .BinaryProducts.product .unique MN MO =
        ≡-sym (≡-trans ∧η (∧I-cong MN MO))

  module _ {G : Graph o ℓ e} {C : CartesianCategory o ℓ e} where

    open NaturalDeduction G
    open Graph G
    open GraphMorphism
    open CartesianCategory C
    open CartesianFunctor
    open Functor
    open NaturalIsomorphism
    open NaturalTransformation
    open module CE = Category.Equiv category

    ⟦_⟧Ty : Ty → (Graph.Obj G → CartesianCategory.Obj C) →
            CartesianCategory.Obj C
    ⟦ ι X ⟧Ty f = f X
    ⟦ t⊤ ⟧Ty f = ⊤
    ⟦ A t∧ B ⟧Ty f = ⟦ A ⟧Ty f × ⟦ B ⟧Ty f

    ⟦_⟧Tm : ∀ {A B} → A ⊢ B →
            ∀ {f₀} (f₁ : ∀ {A B} → Graph._⇒_ G A B → category [ f₀ A , f₀ B ]) →
            category [ ⟦ A ⟧Ty f₀ , ⟦ B ⟧Ty f₀ ]
    ⟦ var ⟧Tm f₁ = id
    ⟦ fI g d ⟧Tm f₁ = f₁ g ∘ ⟦ d ⟧Tm f₁
    ⟦ ⊤I ⟧Tm f₁ = !
    ⟦ ∧E1 d ⟧Tm f₁ = π₁ ∘ ⟦ d ⟧Tm f₁
    ⟦ ∧E2 d ⟧Tm f₁ = π₂ ∘ ⟦ d ⟧Tm f₁
    ⟦ ∧I d e ⟧Tm f₁ = ⟨ ⟦ d ⟧Tm f₁ , ⟦ e ⟧Tm f₁ ⟩

    ⟦_⟧Tm≈ : ∀ {A B d e} → [ A ⊢ B ] d ≡ e →
             ∀ {f₀ : Graph.Obj G → CartesianCategory.Obj C}
             {f₁ : ∀ {A B} → Graph._⇒_ G A B → category [ f₀ A , f₀ B ]} →
             (∀ {A B f f′} → Graph._≈_ G f f′ → category [ f₁ f ≈ f₁ {A} {B} f′ ]) →
             category [ ⟦ d ⟧Tm f₁ ≈ ⟦ e ⟧Tm f₁ ]
    ⟦ ≡-refl ⟧Tm≈ f₁≈ = refl
    ⟦ ≡-trans dd ee ⟧Tm≈ f₁≈ = trans (⟦ dd ⟧Tm≈ f₁≈) (⟦ ee ⟧Tm≈ f₁≈)
    ⟦ ≡-sym dd ⟧Tm≈ f₁≈ = sym (⟦ dd ⟧Tm≈ f₁≈)
    ⟦ fI-cong ff dd ⟧Tm≈ f₁≈ = ∘-resp-≈ (f₁≈ ff) (⟦ dd ⟧Tm≈ f₁≈)
    ⟦ ∧E1-cong dd ⟧Tm≈ f₁≈ = ∘-resp-≈ʳ (⟦ dd ⟧Tm≈ f₁≈)
    ⟦ ∧E2-cong dd ⟧Tm≈ f₁≈ = ∘-resp-≈ʳ (⟦ dd ⟧Tm≈ f₁≈)
    ⟦ ∧I-cong dd ee ⟧Tm≈ f₁≈ = ⟨⟩-cong₂ (⟦ dd ⟧Tm≈ f₁≈) (⟦ ee ⟧Tm≈ f₁≈)
    ⟦ ∧β1 ⟧Tm≈ f₁≈ = project₁
    ⟦ ∧β2 ⟧Tm≈ f₁≈ = project₂
    ⟦ ∧η ⟧Tm≈ f₁≈ = sym (unique refl refl)
    ⟦ ⊤η ⟧Tm≈ f₁≈ = sym (!-unique _)

    rl : GraphMorphism G (forget C) → CartesianFunctor ⊢-cartesianCategory C
    rl f .functor .F₀ A = ⟦ A ⟧Ty (f .M₀)
    rl f .functor .F₁ d = ⟦ d ⟧Tm (f .M₁)
    rl f .functor .identity = refl
    rl f .functor .homomorphism = {!!}
    rl f .functor .F-resp-≈ dd = ⟦ dd ⟧Tm≈ (f .M-resp-≈)
    rl f .⊤-iso = niHelper record
      { η = λ _ → id
      ; η⁻¹ = λ _ → id
      ; commute = λ _ → refl
      ; iso = λ _ → record { isoˡ = identity² ; isoʳ = identity² }
      }
    rl f .×-iso = niHelper record
      { η = λ _ → id
      ; η⁻¹ = λ _ → id
      ; commute = λ (d , e) → trans identityˡ (trans {!lemma d!} (sym identityʳ))
      ; iso = {!!}
      }
      where
      lemma : ∀ {A B C} (d : A ⊢ B) →
              Category._≈_ category
                           (rl f .functor .F₁ d ∘ π₁)
                           (rl f .functor .F₁ (subst (∧E1 {C = C} var) d))
      lemma var = trans identityˡ (sym identityʳ)
      lemma (fI f d) = trans assoc (∘-resp-≈ʳ (lemma d))
      lemma ⊤I = sym (!-unique _)
      lemma (∧E1 d) = trans assoc (∘-resp-≈ʳ (lemma d))
      lemma (∧E2 d) = trans assoc (∘-resp-≈ʳ (lemma d))
      lemma (∧I d e) = {!⟨⟩-cong₂!}
