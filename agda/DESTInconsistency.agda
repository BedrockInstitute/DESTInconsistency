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
--   inconsistent      : (M : Set) (E : Rel M) → DEST⁻ M E → DNE → ⊥
--   DEST-inconsistent : (M : Set) (E : Rel M) → DEST  M E → DNE → ⊥
-- `diagonal` uses comprehension alone: no ME and no classical logic.
-- DNE (double-negation elimination) is classical logic, as an explicit
-- hypothesis of the other two.  REG is not used.
--
-- Check (in any directory containing just this file):
--   agda --safe --no-libraries DESTInconsistency.agda
-- Paper: ../pdf/dest-inconsistency.en.pdf
-- Lean 4 version: ../lean/DESTInconsistency.lean
------------------------------------------------------------------------
module DESTInconsistency where

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
-- 2. Formulas.  Each formula below takes the index of the variable it is
--    about, so that it can be used in any context without renaming.

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

-- 3.3 The diagonal.  Comprehension alone; no ME, no DNE.

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

-- 3.4 The ordinals are asymmetric.  ME, COMP and DNE.

module Proof (M : Set) (E : Rel M) (T : DEST⁻ M E) (dne : DNE) where
  open DEST⁻ T
  open Basic M E COMP

  -- The readings of the formulas of §2 (definitionally equal to them).
  Trans : Side → M → Set
  Trans s a = (y z : M) → E s z y → E s y a → E s z a

  Sing : Side → M → Set
  Sing s y = Σ M λ h → (v : M) → (E s v h → v ≡ y) × (v ≡ y → E s v h)

  Tri : Side → M → Set
  Tri s a = (y z : M) → E s y a → E s z a → E s y z ⊎ y ≡ z ⊎ E s z y

  WF : Side → M → Set
  WF s a = (k x : M) → E s x a → ¬ E s x k →
           Σ M λ z → (z ≡ x ⊎ E s z x) × ¬ E s z k × ((w : M) → E s w z → E s w k)

  Ord : Side → M → Set
  Ord s a = Trans s a × ((y : M) → E s y a → Trans s y) × ((y : M) → E s y a → ¬ E s y y)
          × ((y : M) → E s y a → Sing s y) × Tri s a × WF s a

  o-tr : {s : Side} {a : M} → Ord s a → Trans s a
  o-tr (t , _) = t
  o-mt : {s : Side} {a : M} → Ord s a → (y : M) → E s y a → Trans s y
  o-mt (_ , m , _) = m
  o-irr : {s : Side} {a : M} → Ord s a → (y : M) → E s y a → ¬ E s y y
  o-irr (_ , _ , i , _) = i
  o-ms : {s : Side} {a : M} → Ord s a → (y : M) → E s y a → Sing s y
  o-ms (_ , _ , _ , m , _) = m
  o-tri : {s : Side} {a : M} → Ord s a → Tri s a
  o-tri (_ , _ , _ , _ , t , _) = t
  o-wf : {s : Side} {a : M} → Ord s a → WF s a
  o-wf (_ , _ , _ , _ , _ , w) = w

  me : {s c : Side} → Opp s c → (a b : M) → ((x : M) → E s x a ↔ E c x b) → a ≡ b
  me ∈ε a b h = ME a b h
  me ε∈ a b h = sym (ME b a (λ x → snd (h x) , fst (h x)))

  -- An object with the s-face of a regular object is that object.
  same : {s c : Side} → Opp s c → {z g : M} → Reg g →
         ((x : M) → E s x z → E s x g) → ((x : M) → E s x g → E s x z) → z ≡ g
  same {s} {c} o {z} {g} rg to from =
    me o z g (λ x → (λ h → move s c rg (to x h)) , (λ h → from x (move c s rg h)))

  -- Singletons (Holmes Lemma 2.10).
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

  -- At a regular point the two readings of the ordinal formula agree
  -- (Holmes Lemma 2.11, by the constant-column argument).
  ord-flip : {s c : Side} → Opp s c → {r : M} → Reg r → Ord s r → Ord c r
  ord-flip {s} {c} o {r} rr or = fst (fst (snd A) U) (subst (E s U) (sym A≡U) (full s U))
    where
    A = comp o (ord-f (fs fz)) (r ∷ []) (λ { fz → rr })
    A≡U : fst A ≡ U
    A≡U = me (opp o) (fst A) U (λ x → (λ _ → full s x) , (λ _ → snd (snd (snd A) x) or))

  -- Ordinals.

  down : {s : Side} {a x z : M} → Ord s a → E s x a → z ≡ x ⊎ E s z x → E s z a
  down _ xa (inl refl) = xa
  down oa xa (inr zx) = o-tr oa _ _ zx xa

  member-ord : {s : Side} {a y : M} → Ord s a → E s y a → Ord s y
  member-ord {s} {a} {y} oa ya =
      o-mt oa y ya
    , (λ z zy → o-mt oa z (up zy))
    , (λ z zy → o-irr oa z (up zy))
    , (λ z zy → o-ms oa z (up zy))
    , (λ z z′ zy z′y → o-tri oa z z′ (up zy) (up z′y))
    , (λ k x xy nxk → o-wf oa k x (up xy) nxk)
    where
    up : {z : M} → E s z y → E s z a
    up zy = o-tr oa _ _ zy ya

  not-self : {s : Side} {a : M} → Ord s a → ¬ E s a a
  not-self oa aa = o-irr oa _ aa aa

  self-wf : {s : Side} {x k : M} → Ord s x → ¬ E s x k →
            Σ M λ z → (z ≡ x ⊎ E s z x) × ¬ E s z k × ((w : M) → E s w z → E s w k)
  self-wf {s} {x} {k} ox nxk = dne _ λ none →
    none (x , inl refl , nxk , λ w wx → dne _ λ nwk →
      let (z , zw , nzk , zk) = o-wf ox k w wx nwk in
      none (z , inr (down ox wx zw) , nzk , zk))

  -- A regular transitive object whose face lies inside an ordinal α is α
  -- or a member of α.
  seg : {s c : Side} → Opp s c → {α γ : M} → Ord s α → Reg γ → Trans s γ →
        ((x : M) → E s x γ → E s x α) → γ ≡ α ⊎ E s γ α
  seg {s} {c} o {α} {γ} oα rγ tγ γα = dne _ λ no →
    no (inl (sym (same o rγ (sub no) γα)))
    where
    sub : ¬ (γ ≡ α ⊎ E s γ α) → (x : M) → E s x α → E s x γ
    sub no x xα = dne _ λ nxγ →
      let (z , zx , nzγ , zγ) = o-wf oα γ x xα nxγ
          zα = down oα xα zx
          back : (y : M) → E s y γ → E s y z
          back y yγ = case o-tri oα y z (γα y yγ) zα of λ
            { (inl yz) → yz
            ; (inr (inl e)) → ⊥-elim (nzγ (subst (λ v → E s v γ) e yγ))
            ; (inr (inr zy)) → ⊥-elim (nzγ (tγ y z zy yγ)) }
      in no (inr (subst (λ v → E s v α) (same o rγ zγ back) zα))

  -- Regular ordinals are comparable: apply seg to γ := α ∩ β.
  compare : {s c : Side} → Opp s c → {α β : M} → Reg α → Reg β → Ord s α → Ord s β →
            E s α β ⊎ α ≡ β ⊎ E s β α
  compare {s} {c} o {α} {β} rα rβ oα oβ =
    cases (seg o oα rγ tγ (λ x h → fst (fst (g x) h))) (seg o oβ rγ tγ (λ x h → snd (fst (g x) h)))
    where
    γ₀ = comp o ((fz ∈̇ fs fz) ∧̇ (fz ∈̇ fs (fs fz))) (α ∷ β ∷ []) (λ { fz → rα ; (fs fz) → rβ })
    γ = fst γ₀
    g : (x : M) → E s x γ ↔ E s x α × E s x β
    g x = (λ h → let (a , b) = fst (fst (snd γ₀) x) h in move c s rα a , move c s rβ b)
        , (λ h → snd (fst (snd γ₀) x) (move s c rα (fst h) , move s c rβ (snd h)))
    rγ : Reg γ
    rγ = reg-of o (λ x → (λ h → snd (snd (snd γ₀) x) (fst (g x) h))
                       , (λ h → snd (g x) (fst (snd (snd γ₀) x) h)))
    tγ : Trans s γ
    tγ y z zy yγ = let (yα , yβ) = fst (g y) yγ in snd (g z) (o-tr oα y z zy yα , o-tr oβ y z zy yβ)
    cases : γ ≡ α ⊎ E s γ α → γ ≡ β ⊎ E s γ β → E s α β ⊎ α ≡ β ⊎ E s β α
    cases (inl a) (inl b) = inr (inl (trans (sym a) b))
    cases (inl a) (inr b) = inl (subst (λ v → E s v β) a b)
    cases (inr a) (inl b) = inr (inr (subst (λ v → E s v α) b a))
    cases (inr a) (inr b) = ⊥-elim (o-irr oα γ a (snd (g γ) (a , b)))

  -- An irregular ordinal p contains every regular ordinal t whose members
  -- are regular.
  cut : {s c : Side} → Opp s c → {p t : M} → Ord s p → ¬ Reg p →
        Reg t → Ord s t → ((y : M) → E s y t → Reg y) → E s t p
  cut {s} o {p} {t} op np rt ot tpure = inside rt ot sub
    where
    inside : {z : M} → Reg z → Ord s z → ((x : M) → E s x z → E s x p) → E s z p
    inside rz oz zp = case seg o op rz (o-tr oz) zp of λ
      { (inl e) → ⊥-elim (np (subst Reg e rz)) ; (inr zp′) → zp′ }
    sub : (x : M) → E s x t → E s x p
    sub x xt = dne _ λ nxp →
      let (z , zx , nzp , zp) = o-wf ot p x xt nxp
          zt = down ot xt zx
      in nzp (inside (tpure z zt) (member-ord ot zt) zp)

  -- Below an irregular ordinal there is one whose members are regular.
  descent : {s c : Side} → Opp s c → {α : M} → Ord s α → ¬ Reg α →
            Σ M λ p → Ord s p × ¬ Reg p × ((y : M) → E s y p → Reg y)
  descent {s} {c} o {α} oα nα = dne _ λ none →
    let (x , xα , nx) = impure none
        (z , zx , nzD , zD) = o-wf oα D x xα
                                (λ xD → nx (sing-sing o (o-ms oα x xα) (fst (fst (snd D₀) x) xD)))
        zα = down oα xα zx
    in none ( z , member-ord oα zα
            , (λ rz → nzD (snd (fst (snd D₀) z) (sing-reg (opp o) rz)))
            , (λ y yz → sing-sing o (o-ms oα y (o-tr oα z y yz zα)) (fst (fst (snd D₀) y) (zD y yz))))
    where
    -- D := {x | x has a singleton}; its s-face: has a c-singleton.
    D₀ = comp o (sing-f fz) [] (λ ())
    D = fst D₀
    impure : ¬ (Σ M λ p → Ord s p × ¬ Reg p × ((y : M) → E s y p → Reg y)) →
             Σ M λ x → E s x α × ¬ Reg x
    impure none = dne _ λ nx → none (α , oα , nα , λ y yα → dne _ λ ny → nx (y , yα , ny))

  -- Case B: both sides have irregular ordinals.  Their pure representatives
  -- p, q both have face "all regular ordinals with regular members", so ME
  -- identifies them and p is regular.
  both : {p q : M} → Ord ∈ p → ¬ Reg p → ((y : M) → E ∈ y p → Reg y) →
                      Ord ε q → ¬ Reg q → ((y : M) → E ε y q → Reg y) → ⊥
  both {p} {q} op np pp oq nq pq = np (subst (λ v → (x : M) → E ∈ x p ↔ E ε x v) (sym (ME p q face)) face)
    where
    face : (x : M) → E ∈ x p ↔ E ε x q
    face x = (λ xp → cut ε∈ oq nq (pp x xp) (ord-flip ∈ε (pp x xp) (member-ord op xp))
                         (λ y yx → pp y (o-tr op x y (move ε ∈ (pp x xp) yx) xp)))
           , (λ xq → cut ∈ε op np (pq x xq) (ord-flip ε∈ (pq x xq) (member-ord oq xq))
                         (λ y yx → pq y (o-tr oq x y (move ∈ ε (pq x xq) yx) xq)))

  -- Case A: every ordinal of side c is regular.  Then the ordinal formula is
  -- asymmetric from c to b, with W := {x | ord(x)}, and the diagonal applies.
  one : {b c : Side} → Opp b c → ((x : M) → Ord c x → Reg x) → ⊥
  one {b} {c} o poor =
    Diagonal.contradiction M E COMP (ord-f fz) [] (λ ()) o
      (rich , (λ x y ox → o-irr ox y) , w , wb , wc , w-ord)
    where
    W = comp o (ord-f fz) [] (λ ())
    w = fst W
    wb : (x : M) → E b x w ↔ Ord c x
    wb = fst (snd W)
    wc : (x : M) → E c x w ↔ Ord b x
    wc = snd (snd W)
    rich : (x : M) → Ord c x → Ord b x
    rich x ox = ord-flip (opp o) (poor x ox) ox

    w-ord : Ord b w
    w-ord = (λ y z zy yw → let oy = fst (wb y) yw in
                             snd (wb z) (member-ord oy (move b c (poor y oy) zy)))
          , (λ y yw → o-tr (rich y (fst (wb y) yw)))
          , (λ y yw → not-self (rich y (fst (wb y) yw)))
          , (λ y yw → sing-reg o (poor y (fst (wb y) yw)))
          , (λ y z yw zw → let oy = fst (wb y) yw ; oz = fst (wb z) zw in
                             compare o (poor y oy) (poor z oz) (rich y oy) (rich z oz))
          , (λ k x xw nxk → self-wf (rich x (fst (wb x) xw)) nxk)

  -- Each side has an irregular ordinal (else Case A); then Case B.
  irregular : {b c : Side} → Opp b c → Σ M λ a → Ord c a × ¬ Reg a
  irregular o = dne _ λ none → one o (λ x ox → dne _ λ nx → none (x , ox , nx))

  refutation : ⊥
  refutation =
    let (a , oa , na) = irregular ε∈
        (a′ , oa′ , na′) = irregular ∈ε
        (p , op , np , pp) = descent ∈ε oa na
        (q , oq , nq , pq) = descent ε∈ oa′ na′
    in both op np pp oq nq pq

------------------------------------------------------------------------
-- 4. The theorems

-- Comprehension alone refutes every asymmetric formula.  No ME, no DNE.
diagonal : (M : Set) (E : Rel M) → Comp M E →
           {k : ℕ} (P : Fm (suc k)) (ρ : Fin k → M) →
           ((i : Fin k) → Regular E (ρ i)) →
           {b c : Side} → Opp b c → ¬ Asymmetric E P ρ b c
diagonal M E C P ρ rρ o = Diagonal.contradiction M E C P ρ rρ o

inconsistent : (M : Set) (E : Rel M) → DEST⁻ M E → DNE → ⊥
inconsistent M E T dne = Proof.refutation M E T dne

DEST-inconsistent : (M : Set) (E : Rel M) → DEST M E → DNE → ⊥
DEST-inconsistent M E D = inconsistent M E (DEST.core D)
