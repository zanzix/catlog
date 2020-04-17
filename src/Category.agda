{-# OPTIONS --postfix-projections #-}

module Category where

  import Function.Base as F
  open import Level
  open import Relation.Binary hiding (_⇒_)

  open import Categories.Category
  open import Categories.Functor hiding (id)

  private
    variable
      o ℓ e : Level

  record Graph o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
    infix  4 _≈_ _⇒_

    field
      Obj : Set o
      _⇒_ : Rel Obj ℓ
      _≈_ : ∀ {A B} → Rel (A ⇒ B) e

    [_]_⇒_ = _⇒_
    [_]_≈_ = _≈_

  record GraphMor (R S : Graph o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
    open Graph
    field
      act0 : R .Obj → S .Obj
      act1 : ∀ {A B} → [ R ] A ⇒ B → [ S ] act0 A ⇒ act0 B
      resp : ∀ {A B} {f g : [ R ] A ⇒ B} → [ R ] f ≈ g → [ S ] act1 f ≈ act1 g
  open GraphMor public

  module _ where
    open Graph
    open Category

    forget : Category o ℓ e → Graph o ℓ e
    forget C .Obj = C .Obj
    forget C ._⇒_ = C ._⇒_
    forget C ._≈_ = C ._≈_

  module Ordinary (graph : Graph o ℓ e) where
    open Graph graph

    private
      variable
        A B C D : Obj

    data _⊢_ : Rel Obj (o ⊔ ℓ) where
      const : A ⇒ B
            → -----
              A ⊢ B
      init : -----
             A ⊢ A
      cut : A ⊢ B  →  B ⊢ C
          → ---------------
                 A ⊢ C

    data [_⊢_]_≡_ : (A B : Obj) → Rel (A ⊢ B) (o ⊔ ℓ ⊔ e) where
      ≡-refl : ∀ {ϕ} → [ A ⊢ B ] ϕ ≡ ϕ
      ≡-trans : ∀ {ϕ ψ χ} → [ A ⊢ B ] ϕ ≡ ψ → [ A ⊢ B ] ψ ≡ χ → [ A ⊢ B ] ϕ ≡ χ
      ≡-sym : ∀ {ϕ ψ} → [ A ⊢ B ] ϕ ≡ ψ → [ A ⊢ B ] ψ ≡ ϕ

      const-cong : ∀ {e f} → e ≈ f → [ A ⊢ B ] const e ≡ const f
      cut-cong : ∀ {ϕ₁ ϕ₂ ψ₁ ψ₂} → [ A ⊢ B ] ϕ₁ ≡ ψ₁ → [ B ⊢ C ] ϕ₂ ≡ ψ₂ →
                 [ A ⊢ C ] cut ϕ₁ ϕ₂ ≡ cut ψ₁ ψ₂

      init-cut : ∀ {ϕ} → [ A ⊢ B ] cut init ϕ ≡ ϕ
      cut-init : ∀ {ϕ} → [ A ⊢ B ] cut ϕ init ≡ ϕ
      cut-cut : ∀ {ϕ ψ χ} → [ A ⊢ D ] cut {B = B} (cut ϕ ψ) χ ≡ cut {B = C} ϕ (cut ψ χ)

    open IsEquivalence

    ⊢-category : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
    ⊢-category .Category.Obj = Obj
    ⊢-category .Category._⇒_ = _⊢_
    ⊢-category .Category._≈_ = [ _ ⊢ _ ]_≡_
    ⊢-category .Category.id = init
    ⊢-category .Category._∘_ = F.flip cut
    ⊢-category .Category.assoc = ≡-sym cut-cut
    ⊢-category .Category.sym-assoc = cut-cut
    ⊢-category .Category.identityˡ = cut-init
    ⊢-category .Category.identityʳ = init-cut
    ⊢-category .Category.identity² = init-cut
    ⊢-category .Category.equiv .refl = ≡-refl
    ⊢-category .Category.equiv .sym = ≡-sym
    ⊢-category .Category.equiv .trans = ≡-trans
    ⊢-category .Category.∘-resp-≈ = F.flip cut-cong

  module _ {G : Graph o ℓ e} {C : Category o ℓ e} where

    open Ordinary G
    open Graph G
    open Category C

    open Functor
    open IsEquivalence

    rl-F₁ : ∀ (F : GraphMor G (forget C)) {A B} → A ⊢ B → C [ F .act0 A , F .act0 B ]
    rl-F₁ F (const e) = F .act1 e
    rl-F₁ F init = id
    rl-F₁ F (cut f g) = rl-F₁ F g ∘ rl-F₁ F f

    rl-lemma : ∀ (F : GraphMor G (forget C)) {A B} {f g : ⊢-category [ A , B ]} →
               ⊢-category [ f ≈ g ] → C [ rl-F₁ F f ≈ rl-F₁ F g ]
    rl-lemma F ≡-refl = equiv .refl
    rl-lemma F (≡-trans fg gh) = equiv .trans (rl-lemma F fg) (rl-lemma F gh)
    rl-lemma F (≡-sym fg) = equiv .sym (rl-lemma F fg)
    rl-lemma F (const-cong ee) = F .resp ee
    rl-lemma F (cut-cong ff gg) = ∘-resp-≈ (rl-lemma F gg) (rl-lemma F ff)
    rl-lemma F init-cut = identityʳ
    rl-lemma F cut-init = identityˡ
    rl-lemma F cut-cut = equiv .sym assoc

    rl : GraphMor G (forget C) → Functor ⊢-category C
    rl F .F₀ = F .act0
    rl F .F₁ = rl-F₁ F
    rl F .identity = equiv .refl
    rl F .homomorphism = equiv .refl
    rl F .F-resp-≈ fg = rl-lemma F fg

    lr : Functor ⊢-category C → GraphMor G (forget C)
    lr F .act0 = F .F₀
    lr F .act1 e = F .F₁ (const e)
    lr F .resp fg = F .F-resp-≈ (const-cong fg)

  module CutFree (graph : Graph o ℓ e) where
    open Graph graph

    private
      variable
        A B C D X : Obj

    data _⊩_ : Rel Obj (o ⊔ ℓ) where
      id : A ⊩ A
      comp : X ⊩ A → (f : A ⇒ B) → X ⊩ B

    open Ordinary graph

    cut-intro : A ⊩ B → A ⊢ B
    cut-intro id = init
    cut-intro (comp d f) = cut (cut-intro d) (const f)

    -- This is a version of list append (see also, Data.Star._◅◅_).
    cut-admit : A ⊩ B → B ⊩ C → A ⊩ C
    cut-admit d id = d
    cut-admit d (comp e f) = comp (cut-admit d e) f

    cut-elim : A ⊢ B → A ⊩ B
    cut-elim (const f) = comp id f
    cut-elim init = id
    cut-elim (cut d e) = cut-admit (cut-elim d) (cut-elim e)
