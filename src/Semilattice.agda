{-# OPTIONS --postfix-projections #-}

module Semilattice where

  open import Function.Base using (id; _∘_; case_of_)
  open import Level using (0ℓ)
  open import Relation.Binary using (Rel; REL; Reflexive; Transitive)
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; inspect; [_])

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

  module Cutful (relGr : RelGr) where
    open RelGr relGr renaming (Carrier to I; rel to G)

    infixr 6 _t∧_
    infix 4 _⊢_

    data Ty : Set where
      ι : (X : I) → Ty
      t⊤ : Ty
      _t∧_ : (A B : Ty) → Ty

    variable
      A B C D : Ty
      X Y Z : I

    data _⊢_ : (A B : Ty) → Set where
      init : A ⊢ A
      cut : A ⊢ B → B ⊢ C → A ⊢ C
      fI : (f : G X Y) → ι X ⊢ ι Y
      ⊤I : A ⊢ t⊤
      ∧E1 : B t∧ C ⊢ B
      ∧E2 : B t∧ C ⊢ C
      ∧I : A ⊢ B → A ⊢ C → A ⊢ B t∧ C

  module NaturalDeduction (relGr : RelGr) where
    open RelGr relGr renaming (Carrier to I; rel to G)
    open Cutful relGr

    infix 4 _nd⊢_

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

  module SequentCalculus (relGr : RelGr) where
    open RelGr relGr renaming (Carrier to I; rel to G)
    open Cutful relGr

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

  module SequentCalculus2 (relGr : RelGr) where
    open RelGr relGr renaming (Carrier to I; rel to G)

    module DescStuff (arities : List ℕ) where

      Conn : ℕ → Set
      Conn = _∈ arities

      data Ty : Set where
        ι : I → Ty
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
        X Y : I
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
