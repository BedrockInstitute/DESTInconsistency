{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Weak double extension set theory is inconsistent.
--
-- Holmes, "The structure of the ordinals and the interpretation of ZF in
-- double extension set theory", Studia Logica 2005, §2: two membership
-- relations ∈ and ε; mixed extensionality (Axiom 2.2); comprehension for
-- ε-free formulas with regular parameters (Axiom 2.8, with Definitions
-- 2.1, 2.6, 2.7); the regularity axiom (Axiom 2.5, Definitions 2.3, 2.4).
--
-- This file imports nothing.  Sections 0–1 and the statements in Section 4
-- are the whole trusted part: logic, first-order syntax with one membership
-- symbol, its two readings, the axioms, and asymmetry.  The theorems are
--   diagonal          : (M : Set) (E : Rel M) → Comp M E → ... → ¬ Asymmetric E P ρ b c
--   inconsistent      : (M : Set) (E : Rel M) → DEST⁻ M E → ⊥
--   DEST-inconsistent : (M : Set) (E : Rel M) → DEST  M E → ⊥
-- `diagonal` uses comprehension alone: no ME.  No proof uses classical
-- logic (excluded middle or double-negation elimination).  REG is not used.
--
-- Check (in any directory containing just this file):
--   agda --safe --no-libraries Intuitionistic.agda
-- Paper: ../pdf/dest-inconsistency.en.pdf
-- Lean 4 version: ../lean/Intuitionistic.lean
------------------------------------------------------------------------
module Intuitionistic where

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
-- 2. Formulas.  Each formula below takes the index of the variable it is
--    about, so that it can be used in any context without renaming.

infix 1 _⇔̇_
_⇔̇_ : {n : ℕ} → Fm n → Fm n → Fm n
φ ⇔̇ ψ = (φ ⇒̇ ψ) ∧̇ (ψ ⇒̇ φ)

nn : {n : ℕ} → Fm n → Fm n
nn φ = ¬̇ ¬̇ φ

-- y has a singleton:  ∃h ∀v (v ∈ h ↔ v = y)
sing-f : {n : ℕ} → Fin n → Fm n
sing-f i = ⋁ (⋀ ((fz ∈̇ fs fz) ⇔̇ (fz ≐ fs (fs i))))

-- ∀y ∀z (¬¬ z ∈ y → ¬¬ y ∈ a → ¬¬ z ∈ a)
trans-f : {n : ℕ} → Fin n → Fm n
trans-f i = ⋀ (⋀ (nn (fz ∈̇ fs fz) ⇒̇ nn (fs fz ∈̇ fs (fs i)) ⇒̇ nn (fz ∈̇ fs (fs i))))

-- ∀y ∀z (¬¬ y ∈ a → ¬¬ z ∈ a → ¬¬ (y ∈ z ∨ y = z ∨ z ∈ y))
tri-f : {n : ℕ} → Fin n → Fm n
tri-f i = ⋀ (⋀ (nn (fs fz ∈̇ fs (fs i)) ⇒̇ nn (fz ∈̇ fs (fs i)) ⇒̇
               nn ((fs fz ∈̇ fz) ∨̇ (fs fz ≐ fz) ∨̇ (fz ∈̇ fs fz))))

-- ∀C ∀x (¬¬ x ∈ a → x ∉ C → ¬¬ ∃z ((z = x ∨ z ∈ x) ∧ z ∉ C ∧ ∀w (w ∈ z → ¬¬ w ∈ C)))
wf-f : {n : ℕ} → Fin n → Fm n
wf-f i = ⋀ (⋀ (nn (fz ∈̇ fs (fs i)) ⇒̇ ¬̇ (fz ∈̇ fs fz) ⇒̇
           nn (⋁ (((fz ≐ fs fz) ∨̇ (fz ∈̇ fs fz)) ∧̇ ¬̇ (fz ∈̇ fs (fs fz)) ∧̇
                  ⋀ ((fz ∈̇ fs fz) ⇒̇ nn (fz ∈̇ fs (fs (fs fz))))))))

-- the face of a is stable:  ∀x (¬¬ x ∈ a → x ∈ a)
st-f : {n : ℕ} → Fin n → Fm n
st-f i = ⋀ (nn (fz ∈̇ fs i) ⇒̇ (fz ∈̇ fs i))

-- κ(a), the ordinal formula: (K1) trans-f; (K2) every member satisfies
-- trans-f; (K3) no member is a member of itself; (K4) every member ¬¬-has a
-- singleton; (K5) tri-f; (K6) wf-f; (K7) ¬¬ st-f; (K8) every member
-- satisfies ¬¬ st-f.  "Every member y" is ∀y (¬¬ y ∈ a → ...).
κ-f : {n : ℕ} → Fin n → Fm n
κ-f i = trans-f i
      ∧̇ ⋀ (nn (fz ∈̇ fs i) ⇒̇ trans-f fz)
      ∧̇ ⋀ (nn (fz ∈̇ fs i) ⇒̇ ¬̇ (fz ∈̇ fz))
      ∧̇ ⋀ (nn (fz ∈̇ fs i) ⇒̇ nn (sing-f fz))
      ∧̇ tri-f i
      ∧̇ wf-f i
      ∧̇ nn (st-f i)
      ∧̇ ⋀ (nn (fz ∈̇ fs i) ⇒̇ nn (st-f fz))

xor-f : {n : ℕ} → Fm n → Fm n → Fm n
xor-f φ ψ = φ ∧̇ ¬̇ ψ ∨̇ ¬̇ φ ∧̇ ψ

-- Renaming of variables, for the arbitrary formula P of the diagonal.
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

------------------------------------------------------------------------
-- 3. The proofs

opp : {s c : Side} → Opp s c → Opp c s
opp ∈ε = ε∈
opp ε∈ = ∈ε

-- 3.1 Renaming does what it should.

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

-- 3.2 What comprehension alone gives.

module Basic (M : Set) (E : Rel M) (COMP : Comp M E) where

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

  -- COMP for a pair of opposite sides.
  comp : {s c : Side} → Opp s c → {k : ℕ} (φ : Fm (suc k)) (ρ : Fin k → M) →
         ((i : Fin k) → Reg (ρ i)) →
         Σ M λ A → ((x : M) → E s x A ↔ Sat E c φ (x ∷ ρ))
                 × ((x : M) → E c x A ↔ Sat E s φ (x ∷ ρ))
  comp ∈ε φ ρ r = fst (COMP φ ρ r) , snd (snd (COMP φ ρ r)) , fst (snd (COMP φ ρ r))
  comp ε∈ φ ρ r = fst (COMP φ ρ r) , fst (snd (COMP φ ρ r)) , snd (snd (COMP φ ρ r))

  -- The universal object.
  U : M
  U = fst (comp ∈ε (fz ≐ fz) [] (λ ()))

  full : (s : Side) (x : M) → E s x U
  full ∈ x = snd (fst (snd (comp ∈ε (fz ≐ fz) [] (λ ()))) x) refl
  full ε x = snd (snd (snd (comp ∈ε (fz ≐ fz) [] (λ ()))) x) refl

  U-reg : Reg U
  U-reg x = (λ _ → full ε x) , (λ _ → full ∈ x)

-- 3.3 The diagonal.  Comprehension alone; no ME.

module Diagonal (M : Set) (E : Rel M) (COMP : Comp M E) {k : ℕ} (P : Fm (suc k))
                (ρ : Fin k → M) (rρ : (i : Fin k) → Regular E (ρ i))
                {b c : Side} (o : Opp b c) where
  open Basic M E COMP

  -- P on side t, as a property of objects.
  Pt : Side → M → Set
  Pt t x = Sat E t P (x ∷ ρ)

  -- In context [z ; U ; ρ]:
  --   Θ(z) = ∃u (P(u) ∧ u ∉ z)
  --   Φ(z) = z = U ∨ P(z) ∨ (U ∈ z ∧ (z ∈ z  xor  Θ(z)))
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

  Θ : Side → M → Set
  Θ t z = Σ M λ u → Pt t u × ¬ E t u z

  Xor : Set → Set → Set
  Xor X Y = X × ¬ Y ⊎ ¬ X × Y

  Φ : Side → M → Set
  Φ t z = z ≡ U ⊎ Pt t z ⊎ E t U z × Xor (E t z z) (Θ t z)

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
    to (inr (inr (uz , inl (zz , nθ)))) = inr (inr (uz , inl (zz , λ θ → nθ (snd (θ-sat t z) θ))))
    to (inr (inr (uz , inr (nzz , θ)))) = inr (inr (uz , inr (nzz , fst (θ-sat t z) θ)))
    from : Φ t z → Sat E t Φ-f (z ∷ U ∷ ρ)
    from (inl e) = inl e
    from (inr (inl p)) = inr (inl (snd (P-z t z) p))
    from (inr (inr (uz , inl (zz , nθ)))) = inr (inr (uz , inl (zz , λ θ → nθ (fst (θ-sat t z) θ))))
    from (inr (inr (uz , inr (nzz , θ)))) = inr (inr (uz , inr (nzz , snd (θ-sat t z) θ)))

  -- A := {z | Φ(z)}
  A₀ = comp o Φ-f (U ∷ ρ) (λ { fz → U-reg ; (fs i) → rρ i })
  A = fst A₀
  Ab : (z : M) → E b z A ↔ Φ c z
  Ab z = (λ h → fst (Φ-sat c z) (fst (fst (snd A₀) z) h)) , (λ h → snd (fst (snd A₀) z) (snd (Φ-sat c z) h))
  Ac : (z : M) → E c z A ↔ Φ b z
  Ac z = (λ h → fst (Φ-sat b z) (fst (snd (snd A₀) z) h)) , (λ h → snd (snd (snd A₀) z) (snd (Φ-sat b z) h))

  contradiction : Asymmetric E P ρ b c → ⊥
  contradiction (rich , irr , W , Wb , Wc , PW) = no-x (y→x (nx→y no-x))
    where
    U-not : ¬ Pt b U
    U-not pu = irr U U pu (full b U) (full b U)
    W-not : ¬ Pt c W
    W-not pc = irr W W PW (snd (Wb W) pc) (snd (Wb W) pc)

    -- On side b, A omits the P-object W; on side c it contains every P-object.
    omits : ¬ E b W A
    omits h = case fst (Ab W) h of λ
      { (inl e) → U-not (subst (Pt b) e PW)
      ; (inr (inl pc)) → W-not pc
      ; (inr (inr (UW , _))) → U-not (fst (Wc U) UW) }
    θb : Θ b A
    θb = W , PW , omits
    nθc : ¬ Θ c A
    nθc (u , pu , nu) = nu (snd (Ac u) (inr (inl (rich u pu))))

    A≢U : ¬ (A ≡ U)
    A≢U e = omits (subst (E b W) (sym e) (full b W))
    UAb : E b U A
    UAb = snd (Ab U) (inl refl)
    UAc : E c U A
    UAc = snd (Ac U) (inl refl)
    A-not : ¬ Pt b A
    A-not pa = irr A U pa UAb (full b U)

    -- At z = A only the last disjunct can hold.
    x→y : E b A A → E c A A
    x→y x = case fst (Ab A) x of λ
      { (inl e) → ⊥-elim (A≢U e)
      ; (inr (inl pa)) → ⊥-elim (A-not (rich A pa))
      ; (inr (inr (_ , inl (y , _)))) → y
      ; (inr (inr (_ , inr (_ , θ)))) → ⊥-elim (nθc θ) }
    y→x : E c A A → E b A A
    y→x y = snd (Ab A) (inr (inr (UAc , inl (y , nθc))))
    y→nx : E c A A → ¬ E b A A
    y→nx y = case fst (Ac A) y of λ
      { (inl e) → ⊥-elim (A≢U e)
      ; (inr (inl pa)) → ⊥-elim (A-not pa)
      ; (inr (inr (_ , inl (_ , nθ)))) → ⊥-elim (nθ θb)
      ; (inr (inr (_ , inr (nx , _)))) → nx }
    nx→y : ¬ E b A A → E c A A
    nx→y nx = snd (Ac A) (inr (inr (UAb , inr (nx , θb))))
    no-x : ¬ E b A A
    no-x x = y→nx (x→y x) x

-- 3.4 The κ-ordinals are asymmetric.  ME and COMP.
--
-- Every clause of κ is a negation, so κ is ¬¬-stable.  Wherever the proof
-- needs a fact that it has only up to ¬¬ (a stable face, the regularity of a
-- member), the goal is a negation, and from ¬¬A and A → ¬B follows ¬B.

module Proof (M : Set) (E : Rel M) (T : DEST⁻ M E) where
  open DEST⁻ T
  open Basic M E COMP

  -- The readings of the formulas of §2 (definitionally equal to them).
  Trans : Side → M → Set
  Trans s a = (y z : M) → ¬ ¬ E s z y → ¬ ¬ E s y a → ¬ ¬ E s z a

  Sing : Side → M → Set
  Sing s y = Σ M λ h → (v : M) → (E s v h → v ≡ y) × (v ≡ y → E s v h)

  Tri : Side → M → Set
  Tri s a = (y z : M) → ¬ ¬ E s y a → ¬ ¬ E s z a → ¬ ¬ (E s y z ⊎ y ≡ z ⊎ E s z y)

  WF : Side → M → Set
  WF s a = (k x : M) → ¬ ¬ E s x a → ¬ E s x k →
           ¬ ¬ (Σ M λ z → (z ≡ x ⊎ E s z x) × ¬ E s z k × ((w : M) → E s w z → ¬ ¬ E s w k))

  St : Side → M → Set
  St s a = (x : M) → ¬ ¬ E s x a → E s x a

  Kappa : Side → M → Set
  Kappa s a = Trans s a × ((y : M) → ¬ ¬ E s y a → Trans s y) × ((y : M) → ¬ ¬ E s y a → ¬ E s y y)
            × ((y : M) → ¬ ¬ E s y a → ¬ ¬ Sing s y) × Tri s a × WF s a × ¬ ¬ St s a
            × ((y : M) → ¬ ¬ E s y a → ¬ ¬ St s y)

  o-tr : {s : Side} {a : M} → Kappa s a → Trans s a
  o-tr (t , _) = t
  o-mt : {s : Side} {a : M} → Kappa s a → (y : M) → ¬ ¬ E s y a → Trans s y
  o-mt (_ , m , _) = m
  o-irr : {s : Side} {a : M} → Kappa s a → (y : M) → ¬ ¬ E s y a → ¬ E s y y
  o-irr (_ , _ , i , _) = i
  o-ms : {s : Side} {a : M} → Kappa s a → (y : M) → ¬ ¬ E s y a → ¬ ¬ Sing s y
  o-ms (_ , _ , _ , m , _) = m
  o-tri : {s : Side} {a : M} → Kappa s a → Tri s a
  o-tri (_ , _ , _ , _ , t , _) = t
  o-wf : {s : Side} {a : M} → Kappa s a → WF s a
  o-wf (_ , _ , _ , _ , _ , w , _) = w
  o-st : {s : Side} {a : M} → Kappa s a → ¬ ¬ St s a
  o-st (_ , _ , _ , _ , _ , _ , t , _) = t
  o-mst : {s : Side} {a : M} → Kappa s a → (y : M) → ¬ ¬ E s y a → ¬ ¬ St s y
  o-mst (_ , _ , _ , _ , _ , _ , _ , m) = m

  -- κ is ¬¬-stable.
  stable : {s : Side} {a : M} → ¬ ¬ Kappa s a → Kappa s a
  stable h = (λ y z p q n → h λ k → o-tr k y z p q n)
           , (λ y p y′ z′ p′ q′ n → h λ k → o-mt k y p y′ z′ p′ q′ n)
           , (λ y p n → h λ k → o-irr k y p n)
           , (λ y p n → h λ k → o-ms k y p n)
           , (λ y z p q n → h λ k → o-tri k y z p q n)
           , (λ C x p q n → h λ k → o-wf k C x p q n)
           , (λ n → h λ k → o-st k n)
           , (λ y p n → h λ k → o-mst k y p n)

  -- κ-ordinals.

  -- A ¬¬-member of a κ-ordinal is a κ-ordinal (Lemma 5(1)).
  member-κ : {s : Side} {a y : M} → Kappa s a → ¬ ¬ E s y a → Kappa s y
  member-κ {s} {a} {y} ka ya =
      o-mt ka y ya
    , (λ z zy → o-mt ka z (up zy))
    , (λ z zy → o-irr ka z (up zy))
    , (λ z zy → o-ms ka z (up zy))
    , (λ z z′ zy z′y → o-tri ka z z′ (up zy) (up z′y))
    , (λ k x xy nxk → o-wf ka k x (up xy) nxk)
    , o-mst ka y ya
    , (λ z zy → o-mst ka z (up zy))
    where
    up : {z : M} → ¬ ¬ E s z y → ¬ ¬ E s z a
    up zy = o-tr ka y _ zy ya

  down : {s : Side} {a x z : M} → Kappa s a → ¬ ¬ E s x a → z ≡ x ⊎ E s z x → ¬ ¬ E s z a
  down _ xa (inl refl) = xa
  down ka xa (inr zx) = o-tr ka _ _ (λ n → n zx) xa

  -- On a stable face, transitivity holds outright.
  trP : {s : Side} {a : M} → Kappa s a → St s a → (y z : M) → E s z y → E s y a → E s z a
  trP ka sa y z zy ya = sa z (down ka (λ n → n ya) (inr zy))

  -- A regular object has both faces stable or neither.
  stR : {s t : Side} {x : M} → Reg x → St s x → St t x
  stR {s} {t} rx sx z h = move s t rx (sx z λ n → h λ h′ → n (move t s rx h′))

  me : {s c : Side} → Opp s c → (a b : M) → ((x : M) → E s x a ↔ E c x b) → a ≡ b
  me ∈ε a b h = ME a b h
  me ε∈ a b h = sym (ME b a (λ x → snd (h x) , fst (h x)))

  -- An object with the s-face of a regular object is that object (Lemma 2).
  same : {s c : Side} → Opp s c → {z g : M} → Reg g →
         ((x : M) → E s x z → E s x g) → ((x : M) → E s x g → E s x z) → z ≡ g
  same {s} {c} o {z} {g} rg to from =
    me o z g (λ x → (λ h → move s c rg (to x h)) , (λ h → from x (move c s rg h)))

  -- Singletons (Lemma 4; Holmes Lemma 2.10).
  sing-reg : {s c : Side} → Opp s c → {y : M} → Reg y → Sing s y
  sing-reg o {y} ry = fst h , fst (snd h)
    where h = comp o (fz ≐ fs fz) (y ∷ []) (λ { fz → ry })

  sing-sing : {s c : Side} → Opp s c → {y : M} → Sing s y → Sing c y → Reg y
  sing-sing {s} {c} o {y} (h , hs) (h′ , hc) = reg-of o (λ x → snd (cy x) , fst (cy x))
    where
    e : h ≡ h′
    e = me o h h′ (λ x → (λ a → snd (hc x) (fst (hs x) a)) , (λ a → snd (hs x) (fst (hc x) a)))
    hc′ : (x : M) → E c x h ↔ x ≡ y
    hc′ = subst (λ v → (x : M) → E c x v ↔ x ≡ y) (sym e) hc
    rh : Reg h
    rh = reg-of o (λ x → (λ a → snd (hc′ x) (fst (hs x) a)) , (λ a → snd (hs x) (fst (hc′ x) a)))
    -- k := {x | ∃u (x ∈ u ∧ u ∈ h)}: its c-face is the s-face of y.
    k = comp o (⋁ ((fs fz ∈̇ fz) ∧̇ (fz ∈̇ fs (fs fz)))) (h ∷ []) (λ { fz → rh })
    ck : (x : M) → E c x (fst k) ↔ E s x y
    ck x = (λ a → let (u , xu , uh) = fst (snd (snd k) x) a in
                  subst (λ v → E s x v) (fst (hs u) uh) xu)
         , (λ a → snd (snd (snd k) x) (y , a , snd (hs y) refl))
    e₂ : y ≡ fst k
    e₂ = me o y (fst k) (λ x → snd (ck x) , fst (ck x))
    cy : (x : M) → E c x y ↔ E s x y
    cy = subst (λ v → (x : M) → E c x v ↔ E s x y) (sym e₂) ck

  -- At a regular point the two readings of κ agree: Lemma 3 for κ(r), which
  -- gives Lemma 5(4) (Holmes Lemma 2.11).
  κ-flip : {s c : Side} → Opp s c → {r : M} → Reg r → Kappa s r → Kappa c r
  κ-flip {s} {c} o {r} rr kr = fst (fst (snd A) U) (subst (E s U) (sym A≡U) (full s U))
    where
    A = comp o (κ-f (fs fz)) (r ∷ []) (λ { fz → rr })
    A≡U : fst A ≡ U
    A≡U = me (opp o) (fst A) U (λ x → (λ _ → full s x) , (λ _ → snd (snd (snd A) x) kr))

  -- Lemma 5(3) on a stable face, up to ¬¬: some z = x or z ∈ x lies outside
  -- k and has all its members in k, up to ¬¬.
  self-wf : {s : Side} {x k : M} → Kappa s x → St s x → ¬ E s x k →
            ¬ ¬ (Σ M λ z → (z ≡ x ⊎ E s z x) × ¬ E s z k × ((w : M) → E s w z → ¬ ¬ E s w k))
  self-wf {s} {x} {k} kx sx nxk none =
    none (x , inl refl , nxk , λ w wx nwk → o-wf kx k w (λ n → n wx) nwk λ
      { (z , zw , nzk , zk) → none (z , inr (sx z (down kx (λ n → n wx) zw)) , nzk , zk) })

  -- A regular transitive object whose face lies inside a κ-ordinal α is α or
  -- a member of α, up to ¬¬ (Lemma 6).  The faces of α and γ are stable.
  seg : {s c : Side} → Opp s c → {α γ : M} → Kappa s α → St s α → Reg γ → St s γ →
        ((y z : M) → E s z y → E s y γ → E s z γ) →
        ((x : M) → E s x γ → E s x α) → ¬ ¬ (γ ≡ α ⊎ E s γ α)
  seg {s} o {α} {γ} kα sα rγ sγ tγ γα no = no (inl (sym (same o rγ sub γα)))
    where
    sub : (x : M) → E s x α → E s x γ
    sub x xα = sγ x λ nxγ → o-wf kα γ x (λ n → n xα) nxγ λ { (z , zx , nzγ , zγ) →
      let zα = sα z (down kα (λ n → n xα) zx)
          back : St s z → (y : M) → E s y γ → E s y z
          back sz y yγ = sz y λ nyz → o-tri kα y z (λ n → n (γα y yγ)) (λ n → n zα) λ
            { (inl yz) → nyz yz
            ; (inr (inl e)) → nzγ (subst (λ v → E s v γ) e yγ)
            ; (inr (inr zy)) → nzγ (tγ y z zy yγ) }
      in o-mst kα z (λ n → n zα) λ sz →
         no (inr (subst (λ v → E s v α) (same o rγ (λ w wz → sγ w (zγ w wz)) (back sz)) zα)) }

  -- Regular κ-ordinals with stable faces are comparable, up to ¬¬ (Lemma 7):
  -- apply seg to γ := α ∩ β.
  compare : {s c : Side} → Opp s c → {α β : M} → Reg α → Reg β → Kappa s α → Kappa s β →
            St s α → St s β → ¬ ¬ (E s α β ⊎ α ≡ β ⊎ E s β α)
  compare {s} {c} o {α} {β} rα rβ kα kβ sα sβ n =
    seg o kα sα rγ sγ tγ (λ x h → fst (fst (g x) h)) λ a →
    seg o kβ sβ rγ sγ tγ (λ x h → snd (fst (g x) h)) λ b → cases a b
    where
    γ₀ = comp o ((fz ∈̇ fs fz) ∧̇ (fz ∈̇ fs (fs fz))) (α ∷ β ∷ []) (λ { fz → rα ; (fs fz) → rβ })
    γ = fst γ₀
    g : (x : M) → E s x γ ↔ E s x α × E s x β
    g x = (λ h → let (a , b) = fst (fst (snd γ₀) x) h in move c s rα a , move c s rβ b)
        , (λ h → snd (fst (snd γ₀) x) (move s c rα (fst h) , move s c rβ (snd h)))
    rγ : Reg γ
    rγ = reg-of o (λ x → (λ h → snd (snd (snd γ₀) x) (fst (g x) h))
                       , (λ h → snd (g x) (fst (snd (snd γ₀) x) h)))
    sγ : St s γ
    sγ x h = snd (g x) ( sα x (λ k → h λ i → k (fst (fst (g x) i)))
                       , sβ x (λ k → h λ i → k (snd (fst (g x) i))))
    tγ : (y z : M) → E s z y → E s y γ → E s z γ
    tγ y z zy yγ = let (yα , yβ) = fst (g y) yγ in snd (g z) (trP kα sα y z zy yα , trP kβ sβ y z zy yβ)
    cases : γ ≡ α ⊎ E s γ α → γ ≡ β ⊎ E s γ β → ⊥
    cases (inl a) (inl b) = n (inr (inl (trans (sym a) b)))
    cases (inl a) (inr b) = n (inl (subst (λ v → E s v β) a b))
    cases (inr a) (inl b) = n (inr (inr (subst (λ v → E s v α) b a)))
    cases (inr a) (inr b) = o-irr kα γ (λ k → k a) (snd (g γ) (a , b))

  -- Proposition 1: if every κ-ordinal of side c is regular up to ¬¬, then κ
  -- is asymmetric from c to b, with W := {x | κ(x)}.
  one : {b c : Side} → Opp b c → ((x : M) → Kappa c x → ¬ ¬ Reg x) → Asymmetric E (κ-f fz) [] b c
  one {b} {c} o poor = rich , (λ x y kx yx → o-irr kx y (λ n → n yx)) , w , wb , wc , kw
    where
    W = comp o (κ-f fz) [] (λ ())
    w = fst W
    wb : (x : M) → E b x w ↔ Kappa c x
    wb = fst (snd W)
    wc : (x : M) → E c x w ↔ Kappa b x
    wc = snd (snd W)
    rich : (x : M) → Kappa c x → Kappa b x
    rich x kx = stable λ n → poor x kx λ rx → n (κ-flip (opp o) rx kx)
    -- Under the goal ⊥, a ¬¬-member y of w is regular, a κ-ordinal on both
    -- sides, and has a stable face.
    get : {y : M} → ¬ ¬ E b y w → (Reg y → Kappa c y → Kappa b y → St b y → ⊥) → ⊥
    get {y} yw f = yw λ h → let ky = fst (wb y) h in
                   poor y ky λ ry → o-st ky λ sy → f ry ky (κ-flip (opp o) ry ky) (stR ry sy)
    kw : Kappa b w
    kw = (λ y z zy yw nzw → get yw λ ry ky _ _ →
            zy λ h → nzw (snd (wb z) (member-κ ky (λ n → n (move b c ry h)))))
       , (λ y yw y′ z′ p q n → get yw λ _ _ ky _ → o-tr ky y′ z′ p q n)
       , (λ y yw yy → get yw λ _ _ ky _ → o-irr ky y (λ n → n yy) yy)
       , (λ y yw n → get yw λ ry _ _ _ → n (sing-reg o ry))
       , (λ y z yw zw n → get yw λ ry _ ky sy → get zw λ rz _ kz sz → compare o ry rz ky kz sy sz n)
       , (λ C x xw nxC n → get xw λ _ _ kx sx → self-wf kx sx nxC n)
       , (λ n → n λ x h → snd (wb x) (stable λ k → h λ xw → k (fst (wb x) xw)))
       , (λ y yw n → get yw λ _ _ _ sy → n sy)

  -- By Proposition 1 and the diagonal, each side has an irregular κ-ordinal,
  -- up to ¬¬.
  irregular : {b c : Side} → Opp b c → ¬ ¬ (Σ M λ a → Kappa c a × ¬ Reg a)
  irregular o none = Diagonal.contradiction M E COMP (κ-f fz) [] (λ ()) o
                       (one o λ x kx nx → none (x , kx , nx))

  -- Cut (in Proposition 2): an irregular κ-ordinal p contains every regular
  -- κ-ordinal t whose members are regular up to ¬¬.  The faces of p and t are
  -- stable.
  cut : {s c : Side} → Opp s c → {p t : M} → Kappa s p → St s p → ¬ Reg p →
        Reg t → Kappa s t → St s t → ((y : M) → ¬ ¬ E s y t → ¬ ¬ Reg y) → E s t p
  cut {s} o {p} {t} kp sp np rt kt st tpure = inside rt kt st sub
    where
    inside : {z : M} → Reg z → Kappa s z → St s z → ((x : M) → E s x z → E s x p) → E s z p
    inside rz kz sz zp = sp _ λ nzp → seg o kp sp rz sz (trP kz sz) zp λ
      { (inl e) → np (subst Reg e rz) ; (inr zp′) → nzp zp′ }
    sub : (x : M) → E s x t → E s x p
    sub x xt = sp x λ nxp → o-wf kt p x (λ n → n xt) nxp λ { (z , zx , nzp , zp) →
      let zt = down kt (λ n → n xt) zx in
      tpure z zt λ rz → o-mst kt z zt λ sz →
      nzp (inside rz (member-κ kt zt) sz λ w wz → sp w (zp w wz)) }

  -- Descent (in Proposition 2): below an irregular κ-ordinal there is one
  -- whose members are regular up to ¬¬; all up to ¬¬.
  descent : {s c : Side} → Opp s c → {α : M} → Kappa s α → ¬ Reg α →
            ¬ ¬ (Σ M λ p → Kappa s p × ¬ Reg p × ((y : M) → ¬ ¬ E s y p → ¬ ¬ Reg y))
  descent {s} {c} o {α} kα nα none =
    impure λ { (x , xα , nx) → o-wf kα D x xα (λ xD → sreg xα (λ n → n (fst (Df x) xD)) nx) λ
      { (z , zx , nzD , zD) → let zα = down kα xα zx in
        none ( z , member-κ kα zα , (λ rz → nzD (snd (Df z) (sing-reg (opp o) rz)))
             , λ y yz → sreg (o-tr kα z y yz zα) λ n → yz λ h → zD y h λ yD → n (fst (Df y) yD)) } }
    where
    -- D := {x | x has a singleton}; its s-face: has a c-singleton.
    D₀ = comp o (sing-f fz) [] (λ ())
    D = fst D₀
    Df : (x : M) → E s x D ↔ Sing c x
    Df = fst (snd D₀)
    impure : ¬ ¬ (Σ M λ x → ¬ ¬ E s x α × ¬ Reg x)
    impure nx = none (α , kα , nα , λ y yα ny → nx (y , yα , ny))
    sreg : {y : M} → ¬ ¬ E s y α → ¬ ¬ Sing c y → ¬ ¬ Reg y
    sreg {y} yα sc n = o-ms kα y yα λ ss → sc λ sc′ → n (sing-sing o ss sc′)

  -- Each s-member of p is a c-member of q (in Proposition 2).
  into : {s c : Side} → Opp s c → {p q : M} → Kappa s p → ((y : M) → ¬ ¬ E s y p → ¬ ¬ Reg y) →
         Kappa c q → St c q → ¬ Reg q → (x : M) → E s x p → E c x q
  into {s} {c} o kp pp kq sq nq x xp =
    sq x λ nxq → pp x (λ n → n xp) λ rx → o-mst kp x (λ n → n xp) λ sx →
    nxq (cut (opp o) kq sq nq rx (κ-flip o rx (member-κ kp λ n → n xp)) (stR rx sx)
             λ y yx → pp y (o-tr kp x y (λ n → yx λ h → n (move c s rx h)) λ n → n xp))

  -- Proposition 2: the two sides do not both have irregular κ-ordinals.  By
  -- descent, take p and q whose members are regular up to ¬¬, and open (K7)
  -- for both; by into, F_∈(p) = F_ε(q), so ME identifies them and p is regular.
  both : {a a′ : M} → Kappa ∈ a → ¬ Reg a → Kappa ε a′ → ¬ Reg a′ → ⊥
  both ka na ka′ na′ =
    descent ∈ε ka na λ { (p , kp , np , pp) → descent ε∈ ka′ na′ λ { (q , kq , nq , pq) →
    o-st kp λ sp → o-st kq λ sq →
    let face : (x : M) → E ∈ x p ↔ E ε x q
        face x = into ∈ε kp pp kq sq nq x , into ε∈ kq pq kp sp np x
    in np (subst (λ v → (x : M) → E ∈ x p ↔ E ε x v) (sym (ME p q face)) face) } }

  -- Theorem 2: each side has an irregular κ-ordinal, against Proposition 2.
  refutation : ⊥
  refutation = irregular ε∈ λ { (a , ka , na) → irregular ∈ε λ { (a′ , ka′ , na′) → both ka na ka′ na′ } }

------------------------------------------------------------------------
-- 4. The theorems

-- Comprehension alone refutes every asymmetric formula.  No ME.
diagonal : (M : Set) (E : Rel M) → Comp M E →
           {k : ℕ} (P : Fm (suc k)) (ρ : Fin k → M) →
           ((i : Fin k) → Regular E (ρ i)) →
           {b c : Side} → Opp b c → ¬ Asymmetric E P ρ b c
diagonal M E C P ρ rρ o = Diagonal.contradiction M E C P ρ rρ o

inconsistent : (M : Set) (E : Rel M) → DEST⁻ M E → ⊥
inconsistent M E T = Proof.refutation M E T

DEST-inconsistent : (M : Set) (E : Rel M) → DEST M E → ⊥
DEST-inconsistent M E D = inconsistent M E (DEST.core D)
