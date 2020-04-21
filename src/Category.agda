{-# OPTIONS --postfix-projections #-}

module Category where

  open import Data.Bool
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
      equiv     : ∀ {A B} → IsEquivalence (_≈_ {A} {B})

    module Equiv {A B : Obj} = IsEquivalence (equiv {A} {B})

    [_]_⇒_ = _⇒_
    [_]_≈_ = _≈_

  record GraphMor (R S : Graph o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
    open Graph
    field
      act0 : R .Obj → S .Obj
      act1 : ∀ {A B} → [ R ] A ⇒ B → [ S ] act0 A ⇒ act0 B
      resp : ∀ {A B} {f g : [ R ] A ⇒ B} → [ R ] f ≈ g → [ S ] act1 f ≈ act1 g
  open GraphMor public

  GRAPH : (o ℓ e : Level) → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) {!!}
  GRAPH o ℓ e .Category.Obj = Graph o ℓ e
  GRAPH o ℓ e .Category._⇒_ = GraphMor
  GRAPH o ℓ e .Category._≈_ = {!!}
  GRAPH o ℓ e .Category.id .act0 = F.id
  GRAPH o ℓ e .Category.id .act1 = F.id
  GRAPH o ℓ e .Category.id .resp = F.id
  GRAPH o ℓ e .Category._∘_ f g .act0 = f .act0 F.∘ g .act0
  GRAPH o ℓ e .Category._∘_ f g .act1 = f .act1 F.∘ g .act1
  GRAPH o ℓ e .Category._∘_ f g .resp = f .resp F.∘ g .resp
  GRAPH o ℓ e .Category.assoc = {!!}
  GRAPH o ℓ e .Category.sym-assoc = {!!}
  GRAPH o ℓ e .Category.identityˡ = {!!}
  GRAPH o ℓ e .Category.identityʳ = {!!}
  GRAPH o ℓ e .Category.identity² = {!!}
  GRAPH o ℓ e .Category.equiv = {!!}
  GRAPH o ℓ e .Category.∘-resp-≈ = {!!}

  module _ where
    open Graph
    open Category

    forget : Category o ℓ e → Graph o ℓ e
    forget C .Obj = C .Obj
    forget C ._⇒_ = C ._⇒_
    forget C ._≈_ = C ._≈_
    forget C .equiv = C .equiv

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
    open Graph G hiding (equiv)
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
        b : Bool

    data _cf⊢_ : Rel Obj (o ⊔ ℓ) where
      id : A cf⊢ A
      comp : X cf⊢ A → (f : A ⇒ B) → X cf⊢ B

    open Ordinary graph

    cut-intro : A cf⊢ B → A ⊢ B
    cut-intro id = init
    cut-intro (comp d f) = cut (cut-intro d) (const f)

    -- This is a version of list append (see also, Data.Star._◅◅_).
    cut-admit : A cf⊢ B → B cf⊢ C → A cf⊢ C
    cut-admit d id = d
    cut-admit d (comp e f) = comp (cut-admit d e) f

    cut-elim : A ⊢ B → A cf⊢ B
    cut-elim (const f) = comp id f
    cut-elim init = id
    cut-elim (cut d e) = cut-admit (cut-elim d) (cut-elim e)

    data [_]_c⊢_ : Bool → Rel Obj (o ⊔ ℓ) where
      cut : [ b ] A c⊢ B → [ b ] B c⊢ C → [ true ] A c⊢ C
      id : [ b ] A c⊢ A
      comp : [ b ] X c⊢ A → (f : A ⇒ B) → [ b ] X c⊢ B

    cut-admit′ : [ false ] A c⊢ B → [ false ] B c⊢ C → [ false ] A c⊢ C
    cut-admit′ d id = d
    cut-admit′ d (comp e f) = comp (cut-admit′ d e) f

    cut-elim′ : [ b ] A c⊢ B → [ false ] A c⊢ B
    cut-elim′ (cut d e) = cut-admit′ (cut-elim′ d) (cut-elim′ e)
    cut-elim′ id = id
    cut-elim′ (comp d f) = comp (cut-elim′ d) f

    infix 4 _c≈_

    data _c≈_ : (d d′ : [ false ] A c⊢ B) → Set e where
      id : id c≈ id {A = A}
      comp : ∀ {d d′ : [ false ] X c⊢ A} {f f′ : A ⇒ B}
             (dd : d c≈ d′) (ff : f ≈ f′) → comp d f c≈ comp d′ f′

    c≈-refl : ∀ {d : [ false ] A c⊢ B} → d c≈ d
    c≈-refl {d = id} = id
    c≈-refl {d = comp d f} = comp c≈-refl Equiv.refl

    c≈-sym : ∀ {d e : [ false ] A c⊢ B} → d c≈ e → e c≈ d
    c≈-sym id = id
    c≈-sym (comp dd ff) = comp (c≈-sym dd) (Equiv.sym ff)

    c≈-trans : ∀ {d e f : [ false ] A c⊢ B} → d c≈ e → e c≈ f → d c≈ f
    c≈-trans id id = id
    c≈-trans (comp de gg) (comp ef hh) =
      comp (c≈-trans de ef) (Equiv.trans gg hh)

    identity : (d : [ false ] A c⊢ B) → cut-admit′ id d c≈ d
    identity id = id
    identity (comp d f) = comp (identity d) Equiv.refl

    assoc : (d : [ false ] A c⊢ B) (e : [ false ] B c⊢ C) (f : [ false ] C c⊢ D)
            → cut-admit′ d (cut-admit′ e f) c≈ cut-admit′ (cut-admit′ d e) f
    assoc d e id = c≈-refl
    assoc d e (comp f g) = comp (assoc d e f) Equiv.refl

    c⊢-category : Category o (o ⊔ ℓ) e
    c⊢-category .Category.Obj = Obj
    c⊢-category .Category._⇒_ = [ false ]_c⊢_
    c⊢-category .Category._≈_ = _c≈_
    c⊢-category .Category.id = id
    c⊢-category .Category._∘_ = F.flip cut-admit′
    c⊢-category .Category.assoc {f = d} {e} {f} = assoc d e f
    c⊢-category .Category.sym-assoc {f = d} {e} {f} = c≈-sym (assoc d e f)
    c⊢-category .Category.identityˡ = c≈-refl
    c⊢-category .Category.identityʳ {f = d} = identity d
    c⊢-category .Category.identity² = c≈-refl
    c⊢-category .Category.equiv =
      record { refl = c≈-refl ; sym = c≈-sym ; trans = c≈-trans }
    c⊢-category .Category.∘-resp-≈ id ee = ee
    c⊢-category .Category.∘-resp-≈ (comp dd ff) ee =
      comp (c⊢-category .Category.∘-resp-≈ dd ee) ff
