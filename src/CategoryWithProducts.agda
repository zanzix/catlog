{-# OPTIONS --postfix-projections #-}

module CategoryWithProducts where

  import Function.Base as F
  open import Level renaming (suc to sucℓ)
  open import Relation.Binary hiding (_⇒_)
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; inspect)

  open import Data.Fin using (Fin; zero; suc; #_)
  open import Data.List as L hiding ([_])
  open import Data.List.Membership.Propositional as ∈
  open import Data.List.Membership.Propositional.Properties as ∈P
  open import Data.List.Relation.Unary.All as All
  open import Data.List.Relation.Unary.Any as Any
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product as ×
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Vec as V using (Vec; []; _∷_; toList)

  open import Categories.Category
  open import Categories.Category.Cartesian
  open import Categories.Functor hiding (id)
  open import Categories.Object.Terminal
  open import Categories.Object.Product

  private
    variable
      o ℓ e : Level

  record Graph o ℓ e : Set (sucℓ (o ⊔ ℓ ⊔ e)) where
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

  module _ where
    open Graph
    open Category

    forget : Category o ℓ e → Graph o ℓ e
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
                [ D ⊢ ι Y ] fI f M ≡ fI f M′
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
      open Category
      open IsEquivalence
      open Cartesian
      open Terminal
      open BinaryProducts
      open Product

      ⊢-category : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
      ⊢-category .Obj = Ty
      ⊢-category ._⇒_ = _⊢_
      ⊢-category ._≈_ = [ _ ⊢ _ ]_≡_
      ⊢-category .id = var
      ⊢-category ._∘_ = F.flip subst
      ⊢-category .assoc {f = M} {N} {O} = ≡-sym (subst-assoc M N O)
      ⊢-category .sym-assoc {f = M} {N} {O} = subst-assoc M N O
      ⊢-category .identityˡ = ≡-refl
      ⊢-category .identityʳ = subst-identityˡ _
      ⊢-category .identity² = ≡-refl
      ⊢-category .equiv .refl = ≡-refl
      ⊢-category .equiv .sym = ≡-sym
      ⊢-category .equiv .trans = ≡-trans
      ⊢-category .∘-resp-≈ = F.flip subst-cong

      ⊢-cartesian : Cartesian ⊢-category
      ⊢-cartesian .terminal .⊤ = t⊤
      ⊢-cartesian .terminal .! = ⊤I
      ⊢-cartesian .terminal .!-unique M = ≡-sym ⊤η
      ⊢-cartesian .products .BinaryProducts.product {A} {B} .A×B = A t∧ B
      ⊢-cartesian .products .BinaryProducts.product .π₁ = ∧E1 var
      ⊢-cartesian .products .BinaryProducts.product .π₂ = ∧E2 var
      ⊢-cartesian .products .BinaryProducts.product .Product.⟨_,_⟩ = ∧I
      ⊢-cartesian .products .BinaryProducts.product .project₁ = ∧β1
      ⊢-cartesian .products .BinaryProducts.product .project₂ = ∧β2
      ⊢-cartesian .products .BinaryProducts.product .unique MN MO =
        ≡-sym (≡-trans ∧η (∧I-cong MN MO))

{-
  module SequentCalculus (graph : Graph) where
    open Graph graph renaming (Carrier to Obj; rel to G)
    open Cutful graph

    infix 4 _sc⊢_

    data _sc⊢_ : (A B : Ty) → Set where
      init : ι X sc⊢ ι X
      fR : (f : G X Y) → A sc⊢ ι X → A sc⊢ ι Y
      ⊤R : A sc⊢ t⊤
      ∧L1 : A sc⊢ C → A t∧ B sc⊢ C
      ∧L2 : B sc⊢ C → A t∧ B sc⊢ C
      ∧R : A sc⊢ B → A sc⊢ C → A sc⊢ B t∧ C

    init* : A sc⊢ A
    init* {ι X} = init
    init* {t⊤} = ⊤R
    init* {A t∧ B} = ∧R (∧L1 init*) (∧L2 init*)

    cut-admitˡ : A sc⊢ B → B sc⊢ C → A sc⊢ C
    cut-admitˡ init e = e
    cut-admitˡ (fR f d) e = go f d e
      where
      go : G X Y → A sc⊢ ι X → ι Y sc⊢ C → A sc⊢ C
      go f d init = fR f d
      go f d (fR g e) = fR g (go f d e)
      go f d ⊤R = ⊤R
      go f d (∧R el er) = ∧R (go f d el) (go f d er)
    cut-admitˡ ⊤R e = go e
      where
      go : t⊤ sc⊢ C → A sc⊢ C
      go (fR f e) = fR f (go e)
      go ⊤R = ⊤R
      go (∧R el er) = ∧R (go el) (go er)
    cut-admitˡ (∧L1 d) e = ∧L1 (cut-admitˡ d e)
    cut-admitˡ (∧L2 d) e = ∧L2 (cut-admitˡ d e)
    cut-admitˡ (∧R dl dr) e = go dl dr e
      where
      go : A sc⊢ B → A sc⊢ C → B t∧ C sc⊢ D → A sc⊢ D
      go dl dr (fR f e) = fR f (go dl dr e)
      go dl dr ⊤R = ⊤R
      go dl dr (∧L1 e) = cut-admitˡ dl e  -- PRINCIPAL
      go dl dr (∧L2 e) = cut-admitˡ dr e  -- PRINCIPAL
      go dl dr (∧R el er) = ∧R (go dl dr el) (go dl dr er)

    cut-admitʳ : A sc⊢ B → B sc⊢ C → A sc⊢ C
    cut-admitʳ d init = d
    cut-admitʳ d (fR f e) = fR f (cut-admitʳ d e)
    cut-admitʳ d ⊤R = ⊤R
    cut-admitʳ d (∧L1 e) = go d e
      where
      go : A sc⊢ B t∧ C → B sc⊢ D → A sc⊢ D
      go (∧L1 d) e = ∧L1 (go d e)
      go (∧L2 d) e = ∧L2 (go d e)
      go (∧R dl dr) e = cut-admitʳ dl e  -- PRINCIPAL
    cut-admitʳ d (∧L2 e) = go d e
      where
      go : A sc⊢ B t∧ C → C sc⊢ D → A sc⊢ D
      go (∧L1 d) e = ∧L1 (go d e)
      go (∧L2 d) e = ∧L2 (go d e)
      go (∧R dl dr) e = cut-admitʳ dr e  -- PRINCIPAL
    cut-admitʳ d (∧R el er) = ∧R (cut-admitʳ d el) (cut-admitʳ d er)

    cut-elim-sc : A ⊢ B → A sc⊢ B
    cut-elim-sc init = init*
    cut-elim-sc (cut d e) = cut-admitʳ (cut-elim-sc d) (cut-elim-sc e)
    cut-elim-sc (fI f) = fR f init
    cut-elim-sc ⊤I = ⊤R
    cut-elim-sc ∧E1 = ∧L1 init*
    cut-elim-sc ∧E2 = ∧L2 init*
    cut-elim-sc (∧I d e) = ∧R (cut-elim-sc d) (cut-elim-sc e)

  data Polarity : Set where
    +ve -ve : Polarity

  negate : Polarity → Polarity
  negate +ve = -ve
  negate -ve = +ve

  module SequentCalculus2 (graph : Graph) where
    open Graph graph renaming (Carrier to Obj; rel to G)

    module DescStuff (arities : List ℕ) where

      Conn : ℕ → Set
      Conn = _∈ arities

      data Ty : Set where
        ι : Obj → Ty
        conn : ∀ {n} (c : Conn n) (As : Fin n → Ty) → Ty

      private
        left′ right′ :
          ∀ {n} → Polarity → List (Fin n) → List (List (Fin n))
        left′ +ve hyps = hyps ∷ []
        left′ -ve hyps = L.map (_∷ []) hyps
        right′ = left′ ∘ negate

      record Connective {n} (c : Conn n) : Set where
        field
          polarity : Polarity
          hyps : List (Fin n)

        left right : List (List (Fin n))
        left = left′ polarity hyps
        right = right′ polarity hyps

    record Desc : Set₁ where
      field
        arities : List ℕ
      open DescStuff arities public
      field
        conns : ∀ {n} (c : Conn n) → Connective c
      open module Conns {n} (c : Conn n) = Connective (conns c) public

    {-
    A ⊢ B   A ⊢ C         A   ⊢ C          B   ⊢ C
    ------------- ∧R    --------- ∧L1    --------- ∧L2
      A ⊢ B ∧ C         A ∧ B ⊢ C        A ∧ B ⊢ C

    Γ ⊢ A   Γ, B ⊢ C       Γ, A ⊢ B
    ---------------- →L    --------- →R
      Γ, A → B ⊢ C         Γ ⊢ A → B


     A ⊢ A   A, B ⊢ B
     ---------------- →L
     A → B, A ⊢ B
     ------------- →R
     A → B ⊢ A → B
    -}

    module WithDesc (D : Desc) where
      open Desc D

      infix 4 _sc⊢_

      variable
        X Y : Obj
        A B C : Ty
        n : ℕ
        As Bs Cs : Fin n → Ty
        c : Conn n

      data _sc⊢_ : (A B : Ty) → Set where
        init : ι X sc⊢ ι X
        fR : (f : G X Y) → A sc⊢ ι X → A sc⊢ ι Y
        ruleL : ∀ {hs} (l-rule : hs ∈ left c)
                (ds : ∀ {h} → h ∈ hs → As h sc⊢ B) → conn c As sc⊢ B
        ruleR : ∀ {hs} (r-rule : hs ∈ right c)
                (ds : ∀ {h} → h ∈ hs → A sc⊢ Bs h) → A sc⊢ conn c Bs

      init* : A sc⊢ A
      init* {ι X} = init
      init* {conn c As} with polarity c | inspect polarity c
      ... | +ve | [ q ] =
        ruleL hs∈lss λ h∈hs → ruleR ([h]∈rss h∈hs) λ { (here ≡.refl) → init* }
        where
        hs∈lss : hyps c ∈ left c
        hs∈lss rewrite q = here ≡.refl

        [h]∈rss : ∀ {h} → h ∈ hyps c → h ∷ [] ∈ right c
        [h]∈rss h∈hs rewrite q = ∈-map⁺ _ h∈hs
      ... | -ve | [ q ] =
        ruleR hs∈rss λ h∈hs → ruleL ([h]∈lss h∈hs) λ { (here ≡.refl) → init* }
        where
        hs∈rss : hyps c ∈ right c
        hs∈rss rewrite q = here ≡.refl

        [h]∈lss : ∀ {h} → h ∈ hyps c → h ∷ [] ∈ left c
        [h]∈lss h∈hs rewrite q = ∈-map⁺ _ h∈hs

      cut-admitʳ : A sc⊢ B → B sc⊢ C → A sc⊢ C
      cut-admitʳ d init = d
      cut-admitʳ d (fR f e) = fR f (cut-admitʳ d e)
      cut-admitʳ d (ruleL {c = c} {hs = ls} l-rule es) = go d es
        where
        go : A sc⊢ conn c Bs → (∀ {p} → p ∈ ls → Bs p sc⊢ C) → A sc⊢ C
        go (ruleL l-rule′ ds) es = ruleL l-rule′ (λ h∈hs → go (ds h∈hs) es)
        go (ruleR {hs = rs} r-rule ds) es =
          let h , h∈ls , h∈rs = stuff l-rule r-rule in
          cut-admitʳ (ds h∈rs) (es h∈ls)
          where
          stuff : ls ∈ left c → rs ∈ right c → ∃ \ h → h ∈ ls × h ∈ rs
          stuff l-rule r-rule with polarity c
          stuff (here ≡.refl) r-rule | +ve =
            ×.map id (λ { (h∈hs , ≡.refl) → h∈hs , here ≡.refl })
                  (∈-map⁻ _ r-rule)
          stuff l-rule (here ≡.refl) | -ve =
            ×.map id (λ { (h∈hs , ≡.refl) → here ≡.refl , h∈hs })
                  (∈-map⁻ _ l-rule)
      cut-admitʳ d (ruleR r-rule ds) = ruleR r-rule (λ z → cut-admitʳ d (ds z))

    module _ where
      open Desc
      open Connective

      desc : Desc
      desc .arities = 0 ∷ 2 ∷ []
      desc .conns (here ≡.refl) .polarity = -ve
      desc .conns (here ≡.refl) .hyps = []
      desc .conns (there (here ≡.refl)) .polarity = -ve
      desc .conns (there (here ≡.refl)) .hyps = allFin _

    module _ where
      open Desc desc
      open WithDesc desc

      infix 6 _t∧_

      t⊤ : Ty
      t⊤ = conn (here ≡.refl) λ()
      _t∧_ : (A B : Ty) → Ty
      A t∧ B = conn (there (here ≡.refl)) (V.lookup (A ∷ B ∷ []))

      ⊤R : A sc⊢ t⊤
      ⊤R = ruleR (here ≡.refl) λ()
      ∧L1 : A sc⊢ C → A t∧ B sc⊢ C
      ∧L1 d = ruleL (here ≡.refl) λ { (here ≡.refl) → d }
      ∧L2 : B sc⊢ C → A t∧ B sc⊢ C
      ∧L2 d = ruleL (there (here ≡.refl)) λ { (here ≡.refl) → d }
      ∧R : A sc⊢ B → A sc⊢ C → A sc⊢ B t∧ C
      ∧R d e = ruleR (here ≡.refl) λ where
        (here ≡.refl) → d
        (there (here ≡.refl)) → e

      example : A t∧ B sc⊢ B t∧ A
      example = ∧R (∧L2 init*) (∧L1 init*)

  module _ {G P} where

    open Cutful
    open NaturalDeduction
    open Graph G
    open Semilattice P

    ⟦_⟧Ty : Ty G → (Graph.Carrier G → Semilattice.Carrier P) →
            Semilattice.Carrier P
    ⟦ ι X ⟧Ty f = f X
    ⟦ t⊤ ⟧Ty f = ⊤
    ⟦ A t∧ B ⟧Ty f = ⟦ A ⟧Ty f ∧ ⟦ B ⟧Ty f

    rl : GraphMor G (U P) → SemilatticeMor (⊢-semilattice G) P
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

    lr : SemilatticeMor (⊢-semilattice G) P → GraphMor G (U P)
    lr f .mor .act = f .mor .act ∘ ι
    lr f .mor .pres GAB = f .mor .pres (fI GAB var)

  {-
           F
       ↗--------↘
  Graph    ⊥     Semilattice
       ↖--------↙
           U

  Mor (F X) Y
  -----------
  Mor X (U Y)
  -}
-}
