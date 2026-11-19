{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Weak double extension set theory is inconsistent: supplement.
--
-- Three conclusions added to the paper after publication.  This file
-- imports nothing.  Part 1 (Sections 0–2) and the statements in Part 3
-- (Section 4) are the whole trusted part.  Sections 0–1 are those of
-- DESTInconsistency.agda at release commit 0a3b50c, verbatim; Section 2
-- adds the ordinal formula of that file, verbatim, and the definitions
-- the three statements need.  The theorems are
--   kisielewicz-strict : (M : Set) (E : Rel M) (L : M → Set) → ... →
--                        CompL M E L → DNE → ⊥
--   irregular-ordinals : (M : Set) (E : Rel M) → Comp M E → RegExt M E →
--                        DNE → (c : Side) → Σ M λ a → ... × ¬ Regular E a
--   me-localized       : (M : Set) (E : Rel M) → Comp M E → MEone M E →
--                        SingAx M E → PureME M E → DNE → ⊥
-- DNE (double-negation elimination) is classical logic, as an explicit
-- hypothesis.  irregular-ordinals does not assume ME.  REG is not used.
-- Lemma numbers in the comments are those of the revised paper: 1 exclusive
-- or, 2 rigidity, 3 flip, 4 singletons, 5 ordinals, 6 initial segments,
-- 7 comparability.
--
-- Check (in any directory containing just this file):
--   agda --safe --no-libraries Supplement.agda
------------------------------------------------------------------------
module Supplement where

------------------------------------------------------------------------
-- PART 1.  Trusted definitions: Sections 0–2.  Sections 0–1 are those of
-- DESTInconsistency.agda, verbatim.

------------------------------------------------------------------------
-- 0. Logic

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infix 0 _↔_
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl e = e

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

DNE : Set₁
DNE = (P : Set) → ¬ ¬ P → P

case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x

------------------------------------------------------------------------
-- 1. The theory

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Fin : ℕ → Set where
  fz : {n : ℕ} → Fin (suc n)
  fs : {n : ℕ} → Fin n → Fin (suc n)

-- The two membership relations.
data Side : Set where
  ∈ ε : Side

-- A pair of opposite sides.
data Opp : Side → Side → Set where
  ∈ε : Opp ∈ ε
  ε∈ : Opp ε ∈

Rel : Set → Set₁
Rel M = Side → M → M → Set          -- E ∈ x y : x ∈ y;  E ε x y : x ε y

-- First-order formulas with ONE membership symbol (Holmes's "uniform",
-- i.e. ε-free, formulas).  Variables are de Bruijn indices.
infix  6 _∈̇_ _≐_
infix  5 ¬̇_
infixr 4 _∧̇_
infixr 3 _∨̇_
infixr 2 _⇒̇_
data Fm (n : ℕ) : Set where
  _∈̇_ _≐_      : Fin n → Fin n → Fm n
  ¬̇_           : Fm n → Fm n
  _∧̇_ _∨̇_ _⇒̇_ : Fm n → Fm n → Fm n
  ⋀_ ⋁_        : Fm (suc n) → Fm n          -- ∀ and ∃

infixr 5 _∷_
_∷_ : {A : Set} {n : ℕ} → A → (Fin n → A) → Fin (suc n) → A
(x ∷ ρ) fz     = x
(x ∷ ρ) (fs i) = ρ i

[] : {A : Set} → Fin zero → A
[] ()

-- Sat E s φ ρ: φ read with its membership symbol as E s.
-- Sat E ∈ φ is Holmes's φ, Sat E ε φ is his dual φ*.
Sat : {M : Set} → Rel M → Side → {n : ℕ} → Fm n → (Fin n → M) → Set
Sat E s (i ∈̇ j) ρ = E s (ρ i) (ρ j)
Sat E s (i ≐ j) ρ = ρ i ≡ ρ j
Sat E s (¬̇ φ)   ρ = ¬ Sat E s φ ρ
Sat E s (φ ∧̇ ψ) ρ = Sat E s φ ρ × Sat E s ψ ρ
Sat E s (φ ∨̇ ψ) ρ = Sat E s φ ρ ⊎ Sat E s ψ ρ
Sat E s (φ ⇒̇ ψ) ρ = Sat E s φ ρ → Sat E s ψ ρ
Sat {M} E s (⋀ φ) ρ = (x : M) → Sat E s φ (x ∷ ρ)
Sat {M} E s (⋁ φ) ρ = Σ M λ x → Sat E s φ (x ∷ ρ)

Regular : {M : Set} → Rel M → M → Set
Regular {M} E a = (x : M) → E ∈ x a ↔ E ε x a

-- COMP.  Variable 0 of φ is the comprehension variable and ρ assigns the
-- parameters, all regular:  x ε A ↔ φ(x, ρ)  and  x ∈ A ↔ φ*(x, ρ).
Comp : (M : Set) → Rel M → Set
Comp M E = {k : ℕ} (φ : Fm (suc k)) (ρ : Fin k → M) → ((i : Fin k) → Regular E (ρ i)) →
           Σ M λ A → ((x : M) → E ε x A ↔ Sat E ∈ φ (x ∷ ρ))
                   × ((x : M) → E ∈ x A ↔ Sat E ε φ (x ∷ ρ))

-- DEST⁻ = ME + COMP.
record DEST⁻ (M : Set) (E : Rel M) : Set where
  field
    ME   : (a b : M) → ((x : M) → E ∈ x a ↔ E ε x b) → a ≡ b
    COMP : Comp M E

-- DEST adds REG: an object partially contained in an object all of whose
-- members (in either sense) are regular is regular.
record DEST (M : Set) (E : Rel M) : Set where
  field
    core : DEST⁻ M E
    REG  : (a b : M) →
           (((x : M) → E ∈ x a → E ∈ x b) ⊎ ((x : M) → E ε x a → E ε x b)) →
           ((y : M) → E ∈ y b ⊎ E ε y b → Regular E y) → Regular E a

-- P (with parameters ρ) is asymmetric from side c to side b:
--  (i)   every c-P object is a b-P object;
--  (ii)  no b-P object has a b-member that b-belongs to itself;
--  (iii) some W with b-face {x | P^c x} and c-face {x | P^b x} is a b-P object.
Asymmetric : {M : Set} → Rel M → {k : ℕ} → Fm (suc k) → (Fin k → M) → Side → Side → Set
Asymmetric {M} E P ρ b c =
    ((x : M) → Sat E c P (x ∷ ρ) → Sat E b P (x ∷ ρ))
  × ((x y : M) → Sat E b P (x ∷ ρ) → E b y x → ¬ E b y y)
  × (Σ M λ W → ((x : M) → E b x W ↔ Sat E c P (x ∷ ρ))
             × ((x : M) → E c x W ↔ Sat E b P (x ∷ ρ))
             × Sat E b P (W ∷ ρ))

------------------------------------------------------------------------
-- 2. Supplement definitions

-- The ordinal formula ord, (O1)–(O6): Section 2 of DESTInconsistency.agda.
infix 1 _⇔̇_
_⇔̇_ : {n : ℕ} → Fm n → Fm n → Fm n
φ ⇔̇ ψ = (φ ⇒̇ ψ) ∧̇ (ψ ⇒̇ φ)

-- y has a singleton:  ∃h ∀v (v ∈ h ↔ v = y)
sing-f : {n : ℕ} → Fin n → Fm n
sing-f i = ⋁ (⋀ ((fz ∈̇ fs fz) ⇔̇ (fz ≐ fs (fs i))))

-- a is transitive:  ∀y ∀z (z ∈ y → y ∈ a → z ∈ a)
trans-f : {n : ℕ} → Fin n → Fm n
trans-f i = ⋀ (⋀ ((fz ∈̇ fs fz) ⇒̇ (fs fz ∈̇ fs (fs i)) ⇒̇ (fz ∈̇ fs (fs i))))

-- ∀y ∀z (y ∈ a → z ∈ a → y ∈ z ∨ y = z ∨ z ∈ y)
tri-f : {n : ℕ} → Fin n → Fm n
tri-f i = ⋀ (⋀ ((fs fz ∈̇ fs (fs i)) ⇒̇ (fz ∈̇ fs (fs i)) ⇒̇
               (fs fz ∈̇ fz) ∨̇ (fs fz ≐ fz) ∨̇ (fz ∈̇ fs fz)))

-- ∀C ∀x (x ∈ a → x ∉ C → ∃z ((z = x ∨ z ∈ x) ∧ z ∉ C ∧ ∀w (w ∈ z → w ∈ C)))
wf-f : {n : ℕ} → Fin n → Fm n
wf-f i = ⋀ (⋀ ((fz ∈̇ fs (fs i)) ⇒̇ ¬̇ (fz ∈̇ fs fz) ⇒̇
           ⋁ (((fz ≐ fs fz) ∨̇ (fz ∈̇ fs fz)) ∧̇ ¬̇ (fz ∈̇ fs (fs fz)) ∧̇
              ⋀ ((fz ∈̇ fs fz) ⇒̇ (fz ∈̇ fs (fs (fs fz)))))))

-- a is an ordinal: transitive, members transitive, members not
-- self-membered, members have singletons, trichotomous, well-founded.
ord-f : {n : ℕ} → Fin n → Fm n
ord-f i = trans-f i
       ∧̇ ⋀ ((fz ∈̇ fs i) ⇒̇ trans-f fz)
       ∧̇ ⋀ ((fz ∈̇ fs i) ⇒̇ ¬̇ (fz ∈̇ fz))
       ∧̇ ⋀ ((fz ∈̇ fs i) ⇒̇ sing-f fz)
       ∧̇ tri-f i
       ∧̇ wf-f i

-- COMP with parameters from a class L; Comp M E is CompL M E (Regular E).
CompL : (M : Set) → Rel M → (M → Set) → Set
CompL M E L = {k : ℕ} (φ : Fm (suc k)) (ρ : Fin k → M) → ((i : Fin k) → L (ρ i)) →
              Σ M λ A → ((x : M) → E ε x A ↔ Sat E ∈ φ (x ∷ ρ))
                      × ((x : M) → E ∈ x A ↔ Sat E ε φ (x ∷ ρ))

-- Two regular objects with the same ∈-face are equal.
RegExt : (M : Set) → Rel M → Set
RegExt M E = (a b : M) → Regular E a → Regular E b →
             ((x : M) → E ∈ x a ↔ E ∈ x b) → a ≡ b

-- ME in the case where one of the two objects is regular.
MEone : (M : Set) → Rel M → Set
MEone M E = (a b : M) → Regular E a ⊎ Regular E b →
            ((x : M) → E ∈ x a ↔ E ε x b) → a ≡ b

-- Second claim of the singleton lemma: an object with singletons on both sides is regular.
SingAx : (M : Set) → Rel M → Set
SingAx M E = (y : M) → (Σ M λ h → (v : M) → E ∈ v h ↔ v ≡ y) →
                       (Σ M λ h → (v : M) → E ε v h ↔ v ≡ y) → Regular E y

-- ME in the case where every ∈-member of the first object is regular.
PureME : (M : Set) → Rel M → Set
PureME M E = (p q : M) → ((y : M) → E ∈ y p → Regular E y) →
             ((x : M) → E ∈ x p ↔ E ε x q) → p ≡ q

------------------------------------------------------------------------
-- PART 2.  Proofs: Section 3, checked by Agda and not trusted.

------------------------------------------------------------------------
-- 3. The proofs

-- 3.1 Logic and formulas.

↔-refl : {A : Set} → A ↔ A
↔-refl = (λ a → a) , (λ a → a)

↔-sym : {A B : Set} → (A ↔ B) → (B ↔ A)
↔-sym (f , g) = g , f

↔-trans : {A B C : Set} → (A ↔ B) → (B ↔ C) → (A ↔ C)
↔-trans (f , g) (h , k) = (λ a → h (f a)) , (λ c → g (k c))

-- Exclusive or.
Xor : Set → Set → Set
Xor X Y = X × ¬ Y ⊎ ¬ X × Y

xor-cong : {X X′ Y Y′ : Set} → (X ↔ X′) → (Y ↔ Y′) → Xor X Y ↔ Xor X′ Y′
xor-cong (f , g) (h , k) =
    (λ { (inl (x , ny)) → inl (f x , λ y → ny (k y))
       ; (inr (nx , y)) → inr ((λ x → nx (g x)) , h y) })
  , (λ { (inl (x , ny)) → inl (g x , λ y → ny (h y))
       ; (inr (nx , y)) → inr ((λ x → nx (f x)) , k y) })

-- Every member of b, on either side, is regular.
Pure : {M : Set} → Rel M → M → Set
Pure {M} E b = (y : M) → E ∈ y b ⊎ E ε y b → Regular E y

xor-f : {n : ℕ} → Fm n → Fm n → Fm n
xor-f φ ψ = φ ∧̇ ¬̇ ψ ∨̇ ¬̇ φ ∧̇ ψ

-- ord with clause (O4) "y has a singleton" replaced by sg(y).  ord-of sing-f
-- is ord-f; kisielewicz-strict uses ord-of sing2-f.
ord-of : ({n : ℕ} → Fin n → Fm n) → {n : ℕ} → Fin n → Fm n
ord-of sg i = trans-f i
           ∧̇ ⋀ ((fz ∈̇ fs i) ⇒̇ trans-f fz)
           ∧̇ ⋀ ((fz ∈̇ fs i) ⇒̇ ¬̇ (fz ∈̇ fz))
           ∧̇ ⋀ ((fz ∈̇ fs i) ⇒̇ sg fz)
           ∧̇ tri-f i
           ∧̇ wf-f i

-- Renaming of variables, for the arbitrary formulas of the flip and the
-- diagonal (DESTInconsistency.agda, Sections 2 and 3.1).
lift : {m n : ℕ} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
lift f fz     = fz
lift f (fs i) = fs (f i)

ren : {m n : ℕ} → (Fin m → Fin n) → Fm m → Fm n
ren f (i ∈̇ j) = f i ∈̇ f j
ren f (i ≐ j) = f i ≐ f j
ren f (¬̇ φ)   = ¬̇ ren f φ
ren f (φ ∧̇ ψ) = ren f φ ∧̇ ren f ψ
ren f (φ ∨̇ ψ) = ren f φ ∨̇ ren f ψ
ren f (φ ⇒̇ ψ) = ren f φ ⇒̇ ren f ψ
ren f (⋀ φ)   = ⋀ ren (lift f) φ
ren f (⋁ φ)   = ⋁ ren (lift f) φ

opp : {s c : Side} → Opp s c → Opp c s
opp ∈ε = ε∈
opp ε∈ = ∈ε

-- Renaming does what it should.
module _ {M : Set} (E : Rel M) (s : Side) where

  lift-ok : {m n : ℕ} (f : Fin m → Fin n) (ρ : Fin n → M) (σ : Fin m → M) →
            ((i : Fin m) → ρ (f i) ≡ σ i) → (x : M) (i : Fin (suc m)) → (x ∷ ρ) (lift f i) ≡ (x ∷ σ) i
  lift-ok f ρ σ h x fz     = refl
  lift-ok f ρ σ h x (fs i) = h i

  sat-ren : {m n : ℕ} (f : Fin m → Fin n) (φ : Fm m) (ρ : Fin n → M) (σ : Fin m → M) →
            ((i : Fin m) → ρ (f i) ≡ σ i) → Sat E s (ren f φ) ρ ↔ Sat E s φ σ
  sat-ren f (i ∈̇ j) ρ σ h =
      (λ a → subst (λ v → E s v (σ j)) (h i) (subst (E s (ρ (f i))) (h j) a))
    , (λ a → subst (λ v → E s v (ρ (f j))) (sym (h i)) (subst (E s (σ i)) (sym (h j)) a))
  sat-ren f (i ≐ j) ρ σ h =
      (λ e → trans (sym (h i)) (trans e (h j))) , (λ e → trans (h i) (trans e (sym (h j))))
  sat-ren f (¬̇ φ) ρ σ h =
    let r = sat-ren f φ ρ σ h in (λ n a → n (snd r a)) , (λ n a → n (fst r a))
  sat-ren f (φ ∧̇ ψ) ρ σ h =
    let r = sat-ren f φ ρ σ h ; q = sat-ren f ψ ρ σ h in
      (λ { (a , b) → fst r a , fst q b }) , (λ { (a , b) → snd r a , snd q b })
  sat-ren f (φ ∨̇ ψ) ρ σ h =
    let r = sat-ren f φ ρ σ h ; q = sat-ren f ψ ρ σ h in
      (λ { (inl a) → inl (fst r a) ; (inr b) → inr (fst q b) })
    , (λ { (inl a) → inl (snd r a) ; (inr b) → inr (snd q b) })
  sat-ren f (φ ⇒̇ ψ) ρ σ h =
    let r = sat-ren f φ ρ σ h ; q = sat-ren f ψ ρ σ h in
      (λ g a → fst q (g (snd r a))) , (λ g a → snd q (g (fst r a)))
  sat-ren f (⋀ φ) ρ σ h =
      (λ g x → fst (sat-ren (lift f) φ (x ∷ ρ) (x ∷ σ) (lift-ok f ρ σ h x)) (g x))
    , (λ g x → snd (sat-ren (lift f) φ (x ∷ ρ) (x ∷ σ) (lift-ok f ρ σ h x)) (g x))
  sat-ren f (⋁ φ) ρ σ h =
      (λ { (x , a) → x , fst (sat-ren (lift f) φ (x ∷ ρ) (x ∷ σ) (lift-ok f ρ σ h x)) a })
    , (λ { (x , a) → x , snd (sat-ren (lift f) φ (x ∷ ρ) (x ∷ σ) (lift-ok f ρ σ h x)) a })

-- 3.2 What comprehension gives, for parameters from a class L.

module Basic (M : Set) (E : Rel M) (L : M → Set) (COMP : CompL M E L) where

  Reg : M → Set
  Reg = Regular E

  move : {r x : M} (s t : Side) → Reg r → E s x r → E t x r
  move ∈ ∈ _ h = h
  move ε ε _ h = h
  move ∈ ε rr h = fst (rr _) h
  move ε ∈ rr h = snd (rr _) h

  reg-of : {s c : Side} → Opp s c → {a : M} → ((x : M) → E s x a ↔ E c x a) → Reg a
  reg-of ∈ε h = h
  reg-of ε∈ h x = snd (h x) , fst (h x)

  -- A regular object whose s-members are regular has regular members.
  pure-of : (s : Side) {z : M} → Reg z → ((y : M) → E s y z → Reg y) → Pure E z
  pure-of s rz h y (inl a) = h y (move ∈ s rz a)
  pure-of s rz h y (inr a) = h y (move ε s rz a)

  -- COMP for a pair of opposite sides.
  comp : {s c : Side} → Opp s c → {k : ℕ} (φ : Fm (suc k)) (ρ : Fin k → M) →
         ((i : Fin k) → L (ρ i)) →
         Σ M λ A → ((x : M) → E s x A ↔ Sat E c φ (x ∷ ρ))
                 × ((x : M) → E c x A ↔ Sat E s φ (x ∷ ρ))
  comp ∈ε φ ρ r = fst (COMP φ ρ r) , snd (snd (COMP φ ρ r)) , fst (snd (COMP φ ρ r))
  comp ε∈ φ ρ r = fst (COMP φ ρ r) , fst (snd (COMP φ ρ r)) , snd (snd (COMP φ ρ r))

  -- The universal object V.
  U : M
  U = fst (comp ∈ε (fz ≐ fz) [] (λ ()))

  full : (s : Side) (x : M) → E s x U
  full ∈ x = snd (fst (snd (comp ∈ε (fz ≐ fz) [] (λ ()))) x) refl
  full ε x = snd (snd (snd (comp ∈ε (fz ≐ fz) [] (λ ()))) x) refl

  U-reg : Reg U
  U-reg x = (λ _ → full ε x) , (λ _ → full ∈ x)

-- 3.3 The exclusive-or lemma (Lemma 1) and the flip (Lemma 3).  No ME.

-- If A ∈_b A ↔ (A ∈_c A ⊕ Θ^c) and A ∈_c A ↔ (A ∈_b A ⊕ Θ^b), then Θ^b
-- and ¬Θ^c do not both hold.
xor-core : {Ab Ac Θb Θc : Set} → (Ab ↔ Xor Ac Θc) → (Ac ↔ Xor Ab Θb) → ¬ (Θb × ¬ Θc)
xor-core {Ab} {Ac} {Θb} {Θc} hb hc (θb , nθc) = no-b (snd hb (inl (yes-c , nθc)))
  where
  b→c : Ab → Ac
  b→c x = case fst hb x of λ { (inl (y , _)) → y ; (inr (_ , θ)) → ⊥-elim (nθc θ) }
  c→nb : Ac → ¬ Ab
  c→nb y = case fst hc y of λ { (inl (_ , nθ)) → ⊥-elim (nθ θb) ; (inr (nx , _)) → nx }
  no-b : ¬ Ab
  no-b x = c→nb (b→c x) x
  yes-c : Ac
  yes-c = snd hc (inr (no-b , θb))

-- The flip for a uniform sentence σ with parameters in L: by Lemma 1 for
-- A := {z | z ∈ z ⊕ σ}, σ^b and ¬σ^c do not both hold; with DNE, σ^b → σ^c.
module Flip (M : Set) (E : Rel M) (L : M → Set) (COMP : CompL M E L) {k : ℕ} (σ : Fm k)
            (ρ : Fin k → M) (lρ : (i : Fin k) → L (ρ i)) where
  open Basic M E L COMP

  no-split : {b c : Side} → Opp b c → ¬ (Sat E b σ ρ × ¬ Sat E c σ ρ)
  no-split {b} {c} o = xor-core (↔-trans (fst (snd A₀) A) (at c)) (↔-trans (snd (snd A₀) A) (at b))
    where
    A₀ = comp o (xor-f (fz ∈̇ fz) (ren fs σ)) ρ lρ
    A = fst A₀
    at : (t : Side) → Sat E t (xor-f (fz ∈̇ fz) (ren fs σ)) (A ∷ ρ) ↔ Xor (E t A A) (Sat E t σ ρ)
    at t = xor-cong ↔-refl (sat-ren E t fs σ (A ∷ ρ) ρ (λ i → refl))

  dne-flip : DNE → {b c : Side} → Opp b c → Sat E b σ ρ → Sat E c σ ρ
  dne-flip dne o h = dne _ (λ n → no-split o (h , n))

-- 3.4 The diagonal (Theorem 1).  No ME, no DNE.  Steps 1–5 of the paper's
--     proof, for any A whose faces are those of the diagonal object; the
--     object itself is built in DiagonalV (parameter V, as in the paper) and
--     in Kisielewicz.DiagonalG (V eliminated by ME).

module Diagonal (M : Set) (E : Rel M) (U : M) (full : (s : Side) (x : M) → E s x U)
                {k : ℕ} (P : Fm (suc k)) (ρ : Fin k → M) where

  -- P on side t, as a property of objects.
  Pt : Side → M → Set
  Pt t x = Sat E t P (x ∷ ρ)

  -- Θ(z) = ∃u (P(u) ∧ u ∉ z),  Φ(z) = z = V ∨ P(z) ∨ (V ∈ z ∧ (z ∈ z ⊕ Θ(z))).
  Θ : Side → M → Set
  Θ t z = Σ M λ u → Pt t u × ¬ E t u z

  Φ : Side → M → Set
  Φ t z = z ≡ U ⊎ Pt t z ⊎ E t U z × Xor (E t z z) (Θ t z)

  contradiction : {b c : Side} (A : M) → ((z : M) → E b z A ↔ Φ c z) →
                  ((z : M) → E c z A ↔ Φ b z) → ¬ Asymmetric E P ρ b c
  contradiction {b} {c} A Ab Ac (rich , irr , W , Wb , Wc , PW) = xor-core eqb eqc (θb , nθc)
    where
    -- Step 1.
    U-not : ¬ Pt b U
    U-not pu = irr U U pu (full b U) (full b U)
    W-not : ¬ Pt c W
    W-not pc = irr W W PW (snd (Wb W) pc) (snd (Wb W) pc)

    -- Steps 2 and 3.  On side b, A omits the P-object W; on side c it
    -- contains every P-object.
    omits : ¬ E b W A
    omits h = case fst (Ab W) h of λ
      { (inl e) → U-not (subst (Pt b) e PW)
      ; (inr (inl pc)) → W-not pc
      ; (inr (inr (UW , _))) → U-not (fst (Wc U) UW) }
    θb : Θ b A
    θb = W , PW , omits
    nθc : ¬ Θ c A
    nθc (u , pu , nu) = nu (snd (Ac u) (inr (inl (rich u pu))))

    -- Step 4.  At z = A only the last disjunct can hold.
    A≢U : ¬ (A ≡ U)
    A≢U e = omits (subst (E b W) (sym e) (full b W))
    UAb : E b U A
    UAb = snd (Ab U) (inl refl)
    UAc : E c U A
    UAc = snd (Ac U) (inl refl)
    A-not : ¬ Pt b A
    A-not pa = irr A U pa UAb (full b U)

    -- Step 5.  So A satisfies the two equivalences of Lemma 1.
    eqb : E b A A ↔ Xor (E c A A) (Θ c A)
    eqb = (λ h → case fst (Ab A) h of λ
             { (inl e) → ⊥-elim (A≢U e)
             ; (inr (inl pc)) → ⊥-elim (A-not (rich A pc))
             ; (inr (inr (_ , x))) → x })
        , (λ x → snd (Ab A) (inr (inr (UAc , x))))
    eqc : E c A A ↔ Xor (E b A A) (Θ b A)
    eqc = (λ h → case fst (Ac A) h of λ
             { (inl e) → ⊥-elim (A≢U e)
             ; (inr (inl pb)) → ⊥-elim (A-not pb)
             ; (inr (inr (_ , x))) → x })
        , (λ x → snd (Ac A) (inr (inr (UAb , x))))

-- A := {z | Φ(z)}, with parameters V and those of P (Section 3 of the paper).
module DiagonalV (M : Set) (E : Rel M) (COMP : Comp M E) {k : ℕ} (P : Fm (suc k))
                 (ρ : Fin k → M) (rρ : (i : Fin k) → Regular E (ρ i)) {b c : Side} (o : Opp b c) where
  open Basic M E (Regular E) COMP
  open Diagonal M E U full P ρ

  -- In context [z ; V ; ρ].
  at-z : Fin (suc k) → Fin (suc (suc k))
  at-z fz     = fz
  at-z (fs i) = fs (fs i)

  at-u : Fin (suc k) → Fin (suc (suc (suc k)))
  at-u fz     = fz
  at-u (fs i) = fs (fs (fs i))

  θ-f : Fm (suc (suc k))
  θ-f = ⋁ (ren at-u P ∧̇ ¬̇ (fz ∈̇ fs fz))

  Φ-f : Fm (suc (suc k))
  Φ-f = (fz ≐ fs fz) ∨̇ ren at-z P ∨̇ (fs fz ∈̇ fz) ∧̇ xor-f (fz ∈̇ fz) θ-f

  P-z : (t : Side) (z : M) → Sat E t (ren at-z P) (z ∷ U ∷ ρ) ↔ Pt t z
  P-z t z = sat-ren E t at-z P (z ∷ U ∷ ρ) (z ∷ ρ) (λ { fz → refl ; (fs i) → refl })

  P-u : (t : Side) (u z : M) → Sat E t (ren at-u P) (u ∷ z ∷ U ∷ ρ) ↔ Pt t u
  P-u t u z = sat-ren E t at-u P (u ∷ z ∷ U ∷ ρ) (u ∷ ρ) (λ { fz → refl ; (fs i) → refl })

  θ-sat : (t : Side) (z : M) → Sat E t θ-f (z ∷ U ∷ ρ) ↔ Θ t z
  θ-sat t z = (λ { (u , pu , nu) → u , fst (P-u t u z) pu , nu })
            , (λ { (u , pu , nu) → u , snd (P-u t u z) pu , nu })

  Φ-sat : (t : Side) (z : M) → Sat E t Φ-f (z ∷ U ∷ ρ) ↔ Φ t z
  Φ-sat t z = to , from
    where
    to : Sat E t Φ-f (z ∷ U ∷ ρ) → Φ t z
    to (inl e) = inl e
    to (inr (inl p)) = inr (inl (fst (P-z t z) p))
    to (inr (inr (uz , x))) = inr (inr (uz , fst (xor-cong ↔-refl (θ-sat t z)) x))
    from : Φ t z → Sat E t Φ-f (z ∷ U ∷ ρ)
    from (inl e) = inl e
    from (inr (inl p)) = inr (inl (snd (P-z t z) p))
    from (inr (inr (uz , x))) = inr (inr (uz , snd (xor-cong ↔-refl (θ-sat t z)) x))

  A₀ = comp o Φ-f (U ∷ ρ) (λ { fz → U-reg ; (fs i) → rρ i })

  no-asym : ¬ Asymmetric E P ρ b c
  no-asym = contradiction (fst A₀) (λ z → ↔-trans (fst (snd A₀) z) (Φ-sat c z))
                                   (λ z → ↔-trans (snd (snd A₀) z) (Φ-sat b z))

-- 3.5 Sections 4–5 of the paper for the formula ord-of sg, whose clause
--     (O4) is any formula sg(y) about y.  Parameters come from a class L
--     containing the regular objects with regular members (rp); sg-ok says
--     that sg(y) is about y alone, and sg-rp that regular objects with
--     regular members satisfy it on both sides (Lemma 4, first claim).

module Asymmetry (M : Set) (E : Rel M) (L : M → Set) (COMP : CompL M E L)
                 (rp : (a : M) → Regular E a → Pure E a → L a)
                 (sg : {n : ℕ} → Fin n → Fm n)
                 (sg-ok : {n : ℕ} (s : Side) (ρ : Fin (suc n) → M) →
                          Sat E s (sg fz) ρ ↔ Sat E s (sg fz) (ρ fz ∷ []))
                 (sg-rp : {s c : Side} → Opp s c → {y : M} → Regular E y → Pure E y →
                          Sat E s (sg fz) (y ∷ []))
                 (X : RegExt M E)
                 (diag : {b c : Side} → Opp b c → ¬ Asymmetric E (ord-of sg fz) [] b c)
                 (dne : DNE) where
  open Basic M E L COMP

  -- sg(y) and ord(a), read on side s.
  S : Side → M → Set
  S s y = Sat E s (sg fz) (y ∷ [])

  Ord : Side → M → Set
  Ord s a = Sat E s (ord-of sg fz) (a ∷ [])

  -- The readings of (O1), (O5), (O6) (definitionally the clauses of Ord).
  Trans : Side → M → Set
  Trans s a = (y z : M) → E s z y → E s y a → E s z a

  Tri : Side → M → Set
  Tri s a = (y z : M) → E s y a → E s z a → E s y z ⊎ y ≡ z ⊎ E s z y

  WF : Side → M → Set
  WF s a = (k x : M) → E s x a → ¬ E s x k →
           Σ M λ z → (z ≡ x ⊎ E s z x) × ¬ E s z k × ((w : M) → E s w z → E s w k)

  o-tr : {s : Side} {a : M} → Ord s a → Trans s a
  o-tr (t , _) = t
  o-mt : {s : Side} {a : M} → Ord s a → (y : M) → E s y a → Trans s y
  o-mt (_ , m , _) = m
  o-irr : {s : Side} {a : M} → Ord s a → (y : M) → E s y a → ¬ E s y y
  o-irr (_ , _ , i , _) = i
  o-ms : {s : Side} {a : M} → Ord s a → (y : M) → E s y a → S s y
  o-ms {s} {a} (_ , _ , _ , m , _) y ya = fst (sg-ok s (y ∷ a ∷ [])) (m y ya)
  o-tri : {s : Side} {a : M} → Ord s a → Tri s a
  o-tri (_ , _ , _ , _ , t , _) = t
  o-wf : {s : Side} {a : M} → Ord s a → WF s a
  o-wf (_ , _ , _ , _ , _ , w) = w

  -- Lemma 5 (ordinals).

  down : {s : Side} {a x z : M} → Ord s a → E s x a → z ≡ x ⊎ E s z x → E s z a
  down _ xa (inl refl) = xa
  down oa xa (inr zx) = o-tr oa _ _ zx xa

  -- (1) The s-members of an s-ordinal are s-ordinals.
  member-ord : {s : Side} {a y : M} → Ord s a → E s y a → Ord s y
  member-ord {s} {a} {y} oa ya =
      o-mt oa y ya
    , (λ z zy → o-mt oa z (up zy))
    , (λ z zy → o-irr oa z (up zy))
    , (λ z zy → snd (sg-ok s (z ∷ y ∷ [])) (o-ms oa z (up zy)))
    , (λ z z′ zy z′y → o-tri oa z z′ (up zy) (up z′y))
    , (λ k x xy nxk → o-wf oa k x (up xy) nxk)
    where
    up : {z : M} → E s z y → E s z a
    up zy = o-tr oa _ _ zy ya

  -- (2)
  not-self : {s : Side} {a : M} → Ord s a → ¬ E s a a
  not-self oa aa = o-irr oa _ aa aa

  -- (3)
  self-wf : {s : Side} {x k : M} → Ord s x → ¬ E s x k →
            Σ M λ z → (z ≡ x ⊎ E s z x) × ¬ E s z k × ((w : M) → E s w z → E s w k)
  self-wf {s} {x} {k} ox nxk = dne _ λ none →
    none (x , inl refl , nxk , λ w wx → dne _ λ nwk →
      let (z , zw , nzk , zk) = o-wf ox k w wx nwk in
      none (z , inr (down ox wx zw) , nzk , zk))

  -- (4) A regular s-ordinal with regular members is a c-ordinal: the flip
  --     (Lemma 3) for the sentence ord(r), whose parameter r is in L.
  ord-flip : {s c : Side} → Opp s c → {r : M} → Reg r → Pure E r → Ord s r → Ord c r
  ord-flip o {r} rr pr = Flip.dne-flip M E L COMP (ord-of sg fz) (r ∷ []) (λ { fz → rp r rr pr }) dne o

  -- a and b have the same s-face.
  SameFace : Side → M → M → Set
  SameFace s a b = (x : M) → E s x a ↔ E s x b

  -- Lemma 6 (initial segments), without extensionality: a transitive γ
  -- whose s-face lies inside an s-ordinal α has the s-face of α or of an
  -- s-member of α.
  seg : {s : Side} {α γ : M} → Ord s α → Trans s γ → ((x : M) → E s x γ → E s x α) →
        SameFace s α γ ⊎ (Σ M λ z → E s z α × SameFace s z γ)
  seg {s} {α} {γ} oα tγ γα = dne _ λ no → no (inl (λ x → sub no x , γα x))
    where
    sub : ¬ (SameFace s α γ ⊎ (Σ M λ z → E s z α × SameFace s z γ)) →
          (x : M) → E s x α → E s x γ
    sub no x xα = dne _ λ nxγ →
      let (z , zx , nzγ , zγ) = o-wf oα γ x xα nxγ
          zα = down oα xα zx
          back : (y : M) → E s y γ → E s y z
          back y yγ = case o-tri oα y z (γα y yγ) zα of λ
            { (inl yz) → yz
            ; (inr (inl e)) → ⊥-elim (nzγ (subst (λ v → E s v γ) e yγ))
            ; (inr (inr zy)) → ⊥-elim (nzγ (tγ y z zy yγ)) }
      in no (inr (z , zα , λ y → zγ y , back y))

  -- RegExt for the s-face.
  rext : {s : Side} {a b : M} → Reg a → Reg b → SameFace s a b → a ≡ b
  rext {s} {a} {b} ra rb h =
    X a b ra rb (λ x → (λ xa → move s ∈ rb (fst (h x) (move ∈ s ra xa)))
                     , (λ xb → move s ∈ ra (snd (h x) (move ∈ s rb xb))))

  -- Lemma 7 (comparability), for regular s-ordinals with regular s-members:
  -- Lemma 6 for γ := {x | x ∈ α ∧ x ∈ β}, and γ is identified by RegExt.
  compare : {s c : Side} → Opp s c → {α β : M} → Reg α → Reg β →
            ((z : M) → E s z α → Reg z) → ((z : M) → E s z β → Reg z) →
            Ord s α → Ord s β → E s α β ⊎ α ≡ β ⊎ E s β α
  compare {s} {c} o {α} {β} rα rβ pα pβ oα oβ =
    cases (into oα rα pα (λ x h → fst (fst (g x) h))) (into oβ rβ pβ (λ x h → snd (fst (g x) h)))
    where
    γ₀ = comp o ((fz ∈̇ fs fz) ∧̇ (fz ∈̇ fs (fs fz))) (α ∷ β ∷ [])
              (λ { fz → rp α rα (pure-of s rα pα) ; (fs fz) → rp β rβ (pure-of s rβ pβ) })
    γ = fst γ₀
    g : (x : M) → E s x γ ↔ E s x α × E s x β
    g x = (λ h → let (a , b) = fst (fst (snd γ₀) x) h in move c s rα a , move c s rβ b)
        , (λ h → snd (fst (snd γ₀) x) (move s c rα (fst h) , move s c rβ (snd h)))
    rγ : Reg γ
    rγ = reg-of o (λ x → (λ h → snd (snd (snd γ₀) x) (fst (g x) h))
                       , (λ h → snd (g x) (fst (snd (snd γ₀) x) h)))
    tγ : Trans s γ
    tγ y z zy yγ = let (yα , yβ) = fst (g y) yγ in snd (g z) (o-tr oα y z zy yα , o-tr oβ y z zy yβ)
    into : {δ : M} → Ord s δ → Reg δ → ((z : M) → E s z δ → Reg z) →
           ((x : M) → E s x γ → E s x δ) → γ ≡ δ ⊎ E s γ δ
    into {δ} oδ rδ pδ γδ = case seg oδ tγ γδ of λ
      { (inl e) → inl (sym (rext rδ rγ e))
      ; (inr (z , zδ , e)) → inr (subst (λ v → E s v δ) (rext (pδ z zδ) rγ e) zδ) }
    cases : γ ≡ α ⊎ E s γ α → γ ≡ β ⊎ E s γ β → E s α β ⊎ α ≡ β ⊎ E s β α
    cases (inl a) (inl b) = inr (inl (trans (sym a) b))
    cases (inl a) (inr b) = inl (subst (λ v → E s v β) a b)
    cases (inr a) (inl b) = inr (inr (subst (λ v → E s v α) b a))
    cases (inr a) (inr b) = ⊥-elim (o-irr oα γ a (snd (g γ) (a , b)))

  -- Proposition 1: if every c-ordinal is regular, ord is asymmetric from c
  -- to b, with W := {x | ord(x)}.
  prop1 : {b c : Side} → Opp b c → ((x : M) → Ord c x → Reg x) → Asymmetric E (ord-of sg fz) [] b c
  prop1 {b} {c} o poor = rich , (λ x y ox → o-irr ox y) , w , wb , wc , w-ord
    where
    W = comp o (ord-of sg fz) [] (λ ())
    w = fst W
    wb : (x : M) → E b x w ↔ Ord c x
    wb = fst (snd W)
    wc : (x : M) → E c x w ↔ Ord b x
    wc = snd (snd W)
    -- The b-members of a c-ordinal are c-ordinals, since it is regular.
    below : (y : M) → Ord c y → (z : M) → E b z y → Ord c z
    below y oy z zy = member-ord oy (move b c (poor y oy) zy)
    pure-c : (y : M) → Ord c y → Pure E y
    pure-c y oy = pure-of b (poor y oy) (λ z zy → poor z (below y oy z zy))
    rich : (x : M) → Ord c x → Ord b x
    rich x ox = ord-flip (opp o) (poor x ox) (pure-c x ox) ox

    w-ord : Ord b w
    w-ord = (λ y z zy yw → snd (wb z) (below y (fst (wb y) yw) z zy))
          , (λ y yw → o-tr (rich y (fst (wb y) yw)))
          , (λ y yw → not-self (rich y (fst (wb y) yw)))
          , (λ y yw → let oy = fst (wb y) yw in
                        snd (sg-ok b (y ∷ w ∷ [])) (sg-rp o (poor y oy) (pure-c y oy)))
          , (λ y z yw zw → let oy = fst (wb y) yw ; oz = fst (wb z) zw in
                             compare o (poor y oy) (poor z oz)
                                     (λ u uy → poor u (below y oy u uy))
                                     (λ u uz → poor u (below z oz u uz))
                                     (rich y oy) (rich z oz))
          , (λ k x xw nxk → self-wf (rich x (fst (wb x) xw)) nxk)

  -- Each side has an irregular ordinal: otherwise Proposition 1 contradicts
  -- Theorem 1.
  irregular : {b c : Side} → Opp b c → Σ M λ a → Ord c a × ¬ Reg a
  irregular o = dne _ λ none → diag o (prop1 o (λ x ox → dne _ λ nx → none (x , ox , nx)))

  -- Proposition 2 and the refutation, from three uses of ME: ME when one
  -- object is regular (mo), the second claim of Lemma 4 for sg (sg-reg),
  -- and ME at p = q (pme).
  module Prop2 (mo : MEone M E)
               (sg-reg : {s c : Side} → Opp s c → {y : M} → S s y → S c y → Reg y)
               (pme : PureME M E) where

    -- Lemma 2 (rigidity): an object with the s-face of a regular g is g.
    same : (s : Side) {z g : M} → Reg g → SameFace s z g → z ≡ g
    same ∈ {z} {g} rg h = mo z g (inr rg) (λ x → ↔-trans (h x) (rg x))
    same ε {z} {g} rg h = sym (mo g z (inl rg) (λ x → ↔-trans (rg x) (↔-sym (h x))))

    -- Cut: an irregular s-ordinal p contains every regular s-ordinal t whose
    -- s-members are regular.
    cut : {s : Side} {p t : M} → Ord s p → ¬ Reg p →
          Reg t → Ord s t → ((y : M) → E s y t → Reg y) → E s t p
    cut {s} {p} {t} op np rt ot tpure = inside rt ot sub
      where
      -- By Lemma 6 and rigidity, a regular s-ordinal inside p is p or in p.
      inside : {z : M} → Reg z → Ord s z → ((x : M) → E s x z → E s x p) → E s z p
      inside rz oz zp = case seg op (o-tr oz) zp of λ
        { (inl e) → ⊥-elim (np (subst Reg (sym (same s rz e)) rz))
        ; (inr (y , yp , e)) → subst (λ v → E s v p) (same s rz e) yp }
      sub : (x : M) → E s x t → E s x p
      sub x xt = dne _ λ nxp →
        let (z , zx , nzp , zp) = o-wf ot p x xt nxp
            zt = down ot xt zx
        in nzp (inside (tpure z zt) (member-ord ot zt) zp)

    -- Descent: below an irregular s-ordinal there is one whose s-members are
    -- regular.  D := {x | sg(x)}, whose s-face is the class of x with sg^c(x).
    descent : {s c : Side} → Opp s c → {α : M} → Ord s α → ¬ Reg α →
              Σ M λ p → Ord s p × ¬ Reg p × ((y : M) → E s y p → Reg y)
    descent {s} {c} o {α} oα nα = dne _ λ none →
      let (x , xα , nx) = impure none
          (z , zx , nzD , zD) = o-wf oα D x xα
                                  (λ xD → nx (sg-reg o (o-ms oα x xα) (fst (fst (snd D₀) x) xD)))
          zα = down oα xα zx
          below : (y : M) → E s y z → Reg y
          below y yz = sg-reg o (o-ms oα y (o-tr oα z y yz zα)) (fst (fst (snd D₀) y) (zD y yz))
      in none ( z , member-ord oα zα
              , (λ rz → nzD (snd (fst (snd D₀) z) (sg-rp (opp o) rz (pure-of s rz below))))
              , below )
      where
      D₀ = comp o (sg fz) [] (λ ())
      D = fst D₀
      impure : ¬ (Σ M λ p → Ord s p × ¬ Reg p × ((y : M) → E s y p → Reg y)) →
               Σ M λ x → E s x α × ¬ Reg x
      impure none = dne _ λ nx → none (α , oα , nα , λ y yα → dne _ λ ny → nx (y , yα , ny))

    -- Conclusion: for p, q given by Descent, Cut gives F_∈(p) = F_ε(q), and
    -- ME at p = q makes p regular.
    both : {p q : M} → Ord ∈ p → ¬ Reg p → ((y : M) → E ∈ y p → Reg y) →
                        Ord ε q → ¬ Reg q → ((y : M) → E ε y q → Reg y) → ⊥
    both {p} {q} op np pp oq nq pq =
      np (subst (λ v → (x : M) → E ∈ x p ↔ E ε x v) (sym (pme p q pp face)) face)
      where
      px : (x : M) → E ∈ x p → Pure E x
      px x xp = pure-of ∈ (pp x xp) (λ y yx → pp y (o-tr op x y yx xp))
      qx : (x : M) → E ε x q → Pure E x
      qx x xq = pure-of ε (pq x xq) (λ y yx → pq y (o-tr oq x y yx xq))
      face : (x : M) → E ∈ x p ↔ E ε x q
      face x = (λ xp → cut oq nq (pp x xp) (ord-flip ∈ε (pp x xp) (px x xp) (member-ord op xp))
                           (λ y yx → pp y (o-tr op x y (move ε ∈ (pp x xp) yx) xp)))
             , (λ xq → cut op np (pq x xq) (ord-flip ε∈ (pq x xq) (qx x xq) (member-ord oq xq))
                           (λ y yx → pq y (o-tr oq x y (move ∈ ε (pq x xq) yx) xq)))

    refutation : ⊥
    refutation =
      let (a , oa , na) = irregular ε∈
          (a′ , oa′ , na′) = irregular ∈ε
          (p , op , np , pp) = descent ∈ε oa na
          (q , oq , nq , pq) = descent ε∈ oa′ na′
      in both op np pp oq nq pq

-- 3.6 Regular parameters and the ordinal formula ord (irregular-ordinals,
--     me-localized).

-- ME when one object is regular gives RegExt.
regext-of : {M : Set} {E : Rel M} → MEone M E → RegExt M E
regext-of mo a b ra rb h = mo a b (inl ra) (λ x → ↔-trans (h x) (rb x))

-- SingAx for either order of the sides.
sing-ax : {M : Set} {E : Rel M} → SingAx M E → {s c : Side} → Opp s c → {y : M} →
          Sat E s (sing-f fz) (y ∷ []) → Sat E c (sing-f fz) (y ∷ []) → Regular E y
sing-ax sa ∈ε hs hc = sa _ hs hc
sing-ax sa ε∈ hs hc = sa _ hc hs

module RegularParameters (M : Set) (E : Rel M) (COMP : Comp M E) (X : RegExt M E) (dne : DNE) where
  open Basic M E (Regular E) COMP

  -- Lemma 4, first claim: a regular object has singletons on both sides.
  sing-reg : {s c : Side} → Opp s c → {y : M} → Reg y → Pure E y → Sat E s (sing-f fz) (y ∷ [])
  sing-reg o {y} ry _ = fst h , fst (snd h)
    where h = comp o (fz ≐ fs fz) (y ∷ []) (λ { fz → ry })

  open Asymmetry M E (Regular E) COMP (λ a ra _ → ra) sing-f (λ s ρ → ↔-refl) sing-reg X
                 (λ o → DiagonalV.no-asym M E COMP (ord-f fz) [] (λ ()) o) dne public

-- 3.7 Kisielewicz's condition, read strictly (kisielewicz-strict).  Section
--     3.5 with two changes, so that every parameter is a regular object with
--     regular members: (O4) and D use "y has a singleton that has a
--     singleton", and the diagonal object has no parameter V.

-- y has a singleton that has a singleton:
--   ∃h (∀v (v ∈ h ↔ v = y) ∧ ∃t ∀w (w ∈ t ↔ w = h))
sing2-f : {n : ℕ} → Fin n → Fm n
sing2-f i = ⋁ ((⋀ ((fz ∈̇ fs fz) ⇔̇ (fz ≐ fs (fs i)))) ∧̇ sing-f fz)

module Kisielewicz (M : Set) (E : Rel M) (L : M → Set)
                   (rp : (a : M) → Regular E a → Pure E a → L a)
                   (ME : (a b : M) → ((x : M) → E ∈ x a ↔ E ε x b) → a ≡ b)
                   (COMP : CompL M E L) (dne : DNE) where
  open Basic M E L COMP

  me : {s c : Side} → Opp s c → (a b : M) → ((x : M) → E s x a ↔ E c x b) → a ≡ b
  me ∈ε a b h = ME a b h
  me ε∈ a b h = sym (ME b a (λ x → snd (h x) , fst (h x)))

  -- By ME, V is the only object whose t-face is everything.
  univ : (t : Side) {x : M} → ((y : M) → E t y x) → x ≡ U
  univ ∈ {x} h = me ∈ε x U (λ y → (λ _ → full ε y) , (λ _ → h y))
  univ ε {x} h = me ε∈ x U (λ y → (λ _ → full ∈ y) , (λ _ → h y))

  -- The diagonal object with V eliminated: z = V becomes ∀y (y ∈ z), and
  -- V ∈ z becomes ∃v (∀y (y ∈ v) ∧ v ∈ z).  Its parameters are those of P.
  module DiagonalG {k : ℕ} (P : Fm (suc k)) (ρ : Fin k → M) (lρ : (i : Fin k) → L (ρ i))
                   {b c : Side} (o : Opp b c) where
    open Diagonal M E U full P ρ

    -- In context [z ; ρ].
    at-u : Fin (suc k) → Fin (suc (suc k))
    at-u fz     = fz
    at-u (fs i) = fs (fs i)

    θ-f : Fm (suc k)
    θ-f = ⋁ (ren at-u P ∧̇ ¬̇ (fz ∈̇ fs fz))

    -- ∀y (y ∈ x_i)
    un-f : {n : ℕ} → Fin n → Fm n
    un-f i = ⋀ (fz ∈̇ fs i)

    Φ-f : Fm (suc k)
    Φ-f = un-f fz ∨̇ (P ∨̇ ((⋁ (un-f fz ∧̇ (fz ∈̇ fs fz))) ∧̇ xor-f (fz ∈̇ fz) θ-f))

    P-u : (t : Side) (u z : M) → Sat E t (ren at-u P) (u ∷ z ∷ ρ) ↔ Pt t u
    P-u t u z = sat-ren E t at-u P (u ∷ z ∷ ρ) (u ∷ ρ) (λ { fz → refl ; (fs i) → refl })

    θ-sat : (t : Side) (z : M) → Sat E t θ-f (z ∷ ρ) ↔ Θ t z
    θ-sat t z = (λ { (u , pu , nu) → u , fst (P-u t u z) pu , nu })
              , (λ { (u , pu , nu) → u , snd (P-u t u z) pu , nu })

    Φ-sat : (t : Side) (z : M) → Sat E t Φ-f (z ∷ ρ) ↔ Φ t z
    Φ-sat t z = to , from
      where
      to : Sat E t Φ-f (z ∷ ρ) → Φ t z
      to (inl un) = inl (univ t un)
      to (inr (inl p)) = inr (inl p)
      to (inr (inr ((v , unv , vz) , x))) =
        inr (inr (subst (λ w → E t w z) (univ t unv) vz , fst (xor-cong ↔-refl (θ-sat t z)) x))
      from : Φ t z → Sat E t Φ-f (z ∷ ρ)
      from (inl e) = inl (λ y → subst (E t y) (sym e) (full t y))
      from (inr (inl p)) = inr (inl p)
      from (inr (inr (uz , x))) = inr (inr ((U , full t , uz) , snd (xor-cong ↔-refl (θ-sat t z)) x))

    A₀ = comp o Φ-f ρ lρ

    no-asym : ¬ Asymmetric E P ρ b c
    no-asym = contradiction (fst A₀) (λ z → ↔-trans (fst (snd A₀) z) (Φ-sat c z))
                                     (λ z → ↔-trans (snd (snd A₀) z) (Φ-sat b z))

  -- Lemma 4 with "a singleton that has a singleton".  First claim: a regular
  -- object y with regular members has, on each side, a singleton h, which is
  -- regular with regular members, and h has a singleton t.
  sing2-rp : {s c : Side} → Opp s c → {y : M} → Reg y → Pure E y → Sat E s (sing2-f fz) (y ∷ [])
  sing2-rp {s} {c} o {y} ry py = fst H , fst (snd H) , fst T , fst (snd T)
    where
    H = comp o (fz ≐ fs fz) (y ∷ []) (λ { fz → rp y ry py })
    rh : Reg (fst H)
    rh = reg-of o (λ x → (λ a → snd (snd (snd H) x) (fst (fst (snd H) x) a))
                       , (λ a → snd (fst (snd H) x) (fst (snd (snd H) x) a)))
    ph : Pure E (fst H)
    ph = pure-of s rh (λ v a → subst Reg (sym (fst (fst (snd H) v) a)) ry)
    T = comp o (fz ≐ fs fz) (fst H ∷ []) (λ { fz → rp (fst H) rh ph })

  -- Second claim: an object y with such singletons on both sides is regular.
  -- ME identifies the two singletons h of y, then the two singletons t of h;
  -- t is regular and its one member h is regular, so t may be a parameter.
  sing2-reg : {s c : Side} → Opp s c → {y : M} →
              Sat E s (sing2-f fz) (y ∷ []) → Sat E c (sing2-f fz) (y ∷ []) → Reg y
  sing2-reg {s} {c} o {y} (h , hs , t , ts) (h′ , hc , t′ , tc) =
    reg-of o (λ x → snd (cy x) , fst (cy x))
    where
    e : h ≡ h′
    e = me o h h′ (λ x → (λ a → snd (hc x) (fst (hs x) a)) , (λ a → snd (hs x) (fst (hc x) a)))
    hc′ : (x : M) → (E c x h → x ≡ y) × (x ≡ y → E c x h)
    hc′ = subst (λ v → (x : M) → (E c x v → x ≡ y) × (x ≡ y → E c x v)) (sym e) hc
    rh : Reg h
    rh = reg-of o (λ x → (λ a → snd (hc′ x) (fst (hs x) a)) , (λ a → snd (hs x) (fst (hc′ x) a)))
    tc₁ : (w : M) → (E c w t′ → w ≡ h) × (w ≡ h → E c w t′)
    tc₁ = subst (λ v → (w : M) → (E c w t′ → w ≡ v) × (w ≡ v → E c w t′)) (sym e) tc
    e′ : t ≡ t′
    e′ = me o t t′ (λ w → (λ a → snd (tc₁ w) (fst (ts w) a)) , (λ a → snd (ts w) (fst (tc₁ w) a)))
    tc′ : (w : M) → (E c w t → w ≡ h) × (w ≡ h → E c w t)
    tc′ = subst (λ v → (w : M) → (E c w v → w ≡ h) × (w ≡ h → E c w v)) (sym e′) tc₁
    rt : Reg t
    rt = reg-of o (λ w → (λ a → snd (tc′ w) (fst (ts w) a)) , (λ a → snd (ts w) (fst (tc′ w) a)))
    pt : Pure E t
    pt = pure-of s rt (λ w a → subst Reg (sym (fst (ts w) a)) rh)
    -- k := {x | ∃z ∃u (z ∈ t ∧ u ∈ z ∧ x ∈ u)}: its c-face is the s-face of y.
    k = comp o (⋁ (⋁ ((fs fz ∈̇ fs (fs (fs fz))) ∧̇ (fz ∈̇ fs fz) ∧̇ (fs (fs fz) ∈̇ fz))))
               (t ∷ []) (λ { fz → rp t rt pt })
    ck : (x : M) → E c x (fst k) ↔ E s x y
    ck x = (λ a → let (z , u , zt , uz , xu) = fst (snd (snd k) x) a
                      uh = subst (E s u) (fst (ts z) zt) uz
                  in subst (E s x) (fst (hs u) uh) xu)
         , (λ a → snd (snd (snd k) x) (h , y , snd (ts h) refl , snd (hs y) refl , a))
    e₂ : y ≡ fst k
    e₂ = me o y (fst k) (λ x → snd (ck x) , fst (ck x))
    cy : (x : M) → E c x y ↔ E s x y
    cy = subst (λ v → (x : M) → E c x v ↔ E s x y) (sym e₂) ck

  refutation : ⊥
  refutation = Prop2.refutation (λ a b _ → ME a b) sing2-reg (λ p q _ → ME p q)
    where
    open Asymmetry M E L COMP rp sing2-f (λ s ρ → ↔-refl) sing2-rp
                   (regext-of {M} {E} (λ a b _ → ME a b))
                   (λ o → DiagonalG.no-asym (ord-of sing2-f fz) [] (λ ()) o) dne

------------------------------------------------------------------------
-- PART 3.  Trusted statements: Section 4.

------------------------------------------------------------------------
-- 4. The theorems

-- Kisielewicz's parameter condition, read strictly: ME + COMP whose
-- parameters come from any class L containing every regular object with
-- regular members is inconsistent.
kisielewicz-strict : (M : Set) (E : Rel M) (L : M → Set) →
                     ((a : M) → Regular E a → ((y : M) → E ∈ y a ⊎ E ε y a → Regular E y) → L a) →
                     ((a b : M) → ((x : M) → E ∈ x a ↔ E ε x b) → a ≡ b) →
                     CompL M E L → DNE → ⊥
kisielewicz-strict M E L rp me C dne = Kisielewicz.refutation M E L rp me C dne

-- COMP and extensionality between regular objects, without ME, give each
-- side an irregular ordinal.
irregular-ordinals : (M : Set) (E : Rel M) → Comp M E → RegExt M E → DNE → (c : Side) →
                     Σ M λ a → Sat E c (ord-f fz) (a ∷ []) × ¬ Regular E a
irregular-ordinals M E C X dne ∈ = RegularParameters.irregular M E C X dne ε∈
irregular-ordinals M E C X dne ε = RegularParameters.irregular M E C X dne ∈ε

-- ME is needed on two objects not known to be regular only at the second
-- claim of the singleton lemma and at p = q in Proposition 2: COMP, ME when
-- one of the two objects is regular, and those two uses as axioms are
-- inconsistent.
me-localized : (M : Set) (E : Rel M) → Comp M E → MEone M E → SingAx M E → PureME M E →
               DNE → ⊥
me-localized M E C mo sa pme dne =
  RegularParameters.Prop2.refutation M E C (regext-of {M} {E} mo) dne mo (sing-ax sa) pme
