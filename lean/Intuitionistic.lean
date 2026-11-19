/-
Weak double extension set theory is inconsistent.

Holmes, "The structure of the ordinals and the interpretation of ZF in
double extension set theory", Studia Logica 79 (2005), §2:
two membership relations ∈ and ε;
mixed extensionality (Axiom 2.2); comprehension for ε-free ("uniform")
formulas with regular parameters (Axiom 2.8, with Definitions 2.1, 2.6,
2.7); the regularity axiom (Axiom 2.5, Definitions 2.3, 2.4).

Part I below is the whole trusted part: syntax with one membership symbol,
its two readings, the axioms, asymmetry, and the statements of the theorems
(Part III).  Part II is the proof; it is checked by Lean and need not be read.

This file imports nothing beyond Lean's prelude (no Mathlib, no Batteries).
`diagonal` uses comprehension alone: no ME.  No proof uses classical logic
(excluded middle or double-negation elimination); `#print axioms` reports
no axioms.  REG is never used.

Check:  cd lean && lake build
        lake env lean Intuitionistic.lean
Paper: ../pdf/dest-inconsistency.en.pdf
Agda version: ../agda/Intuitionistic.agda.
-/

namespace DEST

/-! ## Part I. Trusted part -/

/-- The two membership relations: `mem` is Holmes's ∈, `eps` is his ε. -/
inductive Side where
  | mem
  | eps

/-- A pair of opposite sides. -/
inductive Opp : Side → Side → Prop where
  | me : Opp .mem .eps
  | em : Opp .eps .mem

/-- Environment extension: the new variable is variable 0. -/
def cons {α : Type} {n : Nat} (x : α) (ρ : Fin n → α) : Fin (n + 1) → α
  | ⟨0, _⟩ => x
  | ⟨i + 1, h⟩ => ρ ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- The empty environment. -/
def nil {α : Type} : Fin 0 → α
  | ⟨_, h⟩ => absurd h (Nat.not_lt_zero _)

/-- First-order formulas with equality and ONE membership symbol
(Holmes's uniform, i.e. ε-free, formulas).  Variables are de Bruijn
indices `Fin n`; `all` and `ex` bind variable 0. -/
inductive Fm : Nat → Type where
  | mem : Fin n → Fin n → Fm n
  | eq  : Fin n → Fin n → Fm n
  | not : Fm n → Fm n
  | and : Fm n → Fm n → Fm n
  | or  : Fm n → Fm n → Fm n
  | imp : Fm n → Fm n → Fm n
  | all : Fm (n + 1) → Fm n
  | ex  : Fm (n + 1) → Fm n

/-- `Sat E s φ ρ`: φ read with its membership symbol as the relation `E s`,
equality as `=` on the carrier, quantifiers over the whole carrier.
`Sat E .mem φ` is Holmes's φ and `Sat E .eps φ` is his dual φ*. -/
def Sat {M : Type} (E : Side → M → M → Prop) (s : Side) :
    {n : Nat} → Fm n → (Fin n → M) → Prop
  | _, .mem i j, ρ => E s (ρ i) (ρ j)
  | _, .eq i j,  ρ => ρ i = ρ j
  | _, .not φ,   ρ => ¬ Sat E s φ ρ
  | _, .and φ ψ, ρ => Sat E s φ ρ ∧ Sat E s ψ ρ
  | _, .or φ ψ,  ρ => Sat E s φ ρ ∨ Sat E s ψ ρ
  | _, .imp φ ψ, ρ => Sat E s φ ρ → Sat E s ψ ρ
  | _, .all φ,   ρ => ∀ x : M, Sat E s φ (cons x ρ)
  | _, .ex φ,    ρ => ∃ x : M, Sat E s φ (cons x ρ)

/-- Holmes Definition 2.1.  `E .mem x a` is x ∈ a, `E .eps x a` is x ε a. -/
def Regular {M : Type} (E : Side → M → M → Prop) (a : M) : Prop :=
  ∀ x : M, E .mem x a ↔ E .eps x a

/-- COMP (Axiom 2.8).  Variable 0 of φ is the comprehension variable and ρ
assigns the parameters, all of which must be regular.  The direction is
crossed: the ε-face of A is φ, the ∈-face of A is φ*. -/
def Comp (M : Type) (E : Side → M → M → Prop) : Prop :=
  ∀ {k : Nat} (φ : Fm (k + 1)) (ρ : Fin k → M), (∀ i : Fin k, Regular E (ρ i)) →
    ∃ A : M, ∀ x : M,
      (E .eps x A ↔ Sat E .mem φ (cons x ρ)) ∧ (E .mem x A ↔ Sat E .eps φ (cons x ρ))

/-- DEST⁻ = ME (Axiom 2.2) + COMP. -/
structure DESTminus (M : Type) (E : Side → M → M → Prop) : Prop where
  ME : ∀ a b : M, (∀ x : M, E .mem x a ↔ E .eps x b) → a = b
  COMP : Comp M E

/-- DEST adds REG (Axiom 2.5): an object partially contained (Definition 2.4)
in an object with regular elements (Definition 2.3) is regular. -/
structure DEST (M : Type) (E : Side → M → M → Prop) : Prop where
  core : DESTminus M E
  REG : ∀ a b : M,
    ((∀ x : M, E .mem x a → E .mem x b) ∨ (∀ x : M, E .eps x a → E .eps x b)) →
    (∀ y : M, (E .mem y b ∨ E .eps y b) → Regular E y) →
    Regular E a

/-- P (with parameters ρ) is asymmetric from side c to side b:
(i) every c-P object is a b-P object; (ii) no b-P object has a b-member that
b-belongs to itself; (iii) some W with b-face {x | P^c x} and c-face
{x | P^b x} is a b-P object. -/
def Asymmetric {M : Type} (E : Side → M → M → Prop) {k : Nat}
    (P : Fm (k + 1)) (ρ : Fin k → M) (b c : Side) : Prop :=
  (∀ x : M, Sat E c P (cons x ρ) → Sat E b P (cons x ρ)) ∧
  (∀ x y : M, Sat E b P (cons x ρ) → E b y x → ¬ E b y y) ∧
  ∃ W : M, (∀ x : M, E b x W ↔ Sat E c P (cons x ρ)) ∧
           (∀ x : M, E c x W ↔ Sat E b P (cons x ρ)) ∧ Sat E b P (cons W ρ)

/-! ## Part II. Proof (checked by Lean) -/

/-! ### Formulas used.  Each takes the index of the variable it is about. -/

@[reducible] def fz {n : Nat} : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
@[reducible] def fs {n : Nat} (i : Fin n) : Fin (n + 1) := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

def iffF (φ ψ : Fm n) : Fm n := .and (.imp φ ψ) (.imp ψ φ)

def nnF (φ : Fm n) : Fm n := .not (.not φ)

/-- y has a singleton:  ∃h ∀v (v ∈ h ↔ v = y) -/
def singF (i : Fin n) : Fm n :=
  .ex (.all (iffF (.mem fz (fs fz)) (.eq fz (fs (fs i)))))

/-- ∀y ∀z (¬¬ z ∈ y → ¬¬ y ∈ a → ¬¬ z ∈ a) -/
def transF (i : Fin n) : Fm n :=
  .all (.all (.imp (nnF (.mem fz (fs fz)))
    (.imp (nnF (.mem (fs fz) (fs (fs i)))) (nnF (.mem fz (fs (fs i)))))))

/-- ∀y ∀z (¬¬ y ∈ a → ¬¬ z ∈ a → ¬¬ (y ∈ z ∨ y = z ∨ z ∈ y)) -/
def triF (i : Fin n) : Fm n :=
  .all (.all (.imp (nnF (.mem (fs fz) (fs (fs i)))) (.imp (nnF (.mem fz (fs (fs i))))
    (nnF (.or (.mem (fs fz) fz) (.or (.eq (fs fz) fz) (.mem fz (fs fz))))))))

/-- ∀C ∀x (¬¬ x ∈ a → x ∉ C → ¬¬ ∃z ((z = x ∨ z ∈ x) ∧ z ∉ C ∧ ∀w (w ∈ z → ¬¬ w ∈ C))) -/
def wfF (i : Fin n) : Fm n :=
  .all (.all (.imp (nnF (.mem fz (fs (fs i)))) (.imp (.not (.mem fz (fs fz)))
    (nnF (.ex (.and (.or (.eq fz (fs fz)) (.mem fz (fs fz)))
      (.and (.not (.mem fz (fs (fs fz))))
        (.all (.imp (.mem fz (fs fz)) (nnF (.mem fz (fs (fs (fs fz))))))))))))))

/-- the face of a is stable:  ∀x (¬¬ x ∈ a → x ∈ a) -/
def stF (i : Fin n) : Fm n := .all (.imp (nnF (.mem fz (fs i))) (.mem fz (fs i)))

/-- κ(a), the ordinal formula: (K1) `transF`, (K2) every member satisfies
`transF`, (K3) no member is a member of itself, (K4) every member ¬¬-has a
singleton, (K5) `triF`, (K6) `wfF`, (K7) ¬¬ `stF`, (K8) every member
satisfies ¬¬ `stF`.  Here "every member y" is ∀y (¬¬ y ∈ a → ...). -/
def kappaF (i : Fin n) : Fm n :=
  .and (transF i)
    (.and (.all (.imp (nnF (.mem fz (fs i))) (transF fz)))
      (.and (.all (.imp (nnF (.mem fz (fs i))) (.not (.mem fz fz))))
        (.and (.all (.imp (nnF (.mem fz (fs i))) (nnF (singF fz))))
          (.and (triF i) (.and (wfF i) (.and (nnF (stF i))
            (.all (.imp (nnF (.mem fz (fs i))) (nnF (stF fz))))))))))

def xorF (φ ψ : Fm n) : Fm n := .or (.and φ (.not ψ)) (.and (.not φ) ψ)

/-! ### Renaming, for the arbitrary formula P of the diagonal. -/

def lift {m n : Nat} (f : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  cons fz (fun i => fs (f i))

def ren {m n : Nat} (f : Fin m → Fin n) : Fm m → Fm n
  | .mem i j => .mem (f i) (f j)
  | .eq i j  => .eq (f i) (f j)
  | .not φ   => .not (ren f φ)
  | .and φ ψ => .and (ren f φ) (ren f ψ)
  | .or φ ψ  => .or (ren f φ) (ren f ψ)
  | .imp φ ψ => .imp (ren f φ) (ren f ψ)
  | .all φ   => .all (ren (lift f) φ)
  | .ex φ    => .ex (ren (lift f) φ)

/-! ### The diagonal formula, in context [z ; U ; ρ]. -/

def atZ {k : Nat} : Fin (k + 1) → Fin (k + 1 + 1) := cons fz (fun i => fs (fs i))
def atU {k : Nat} : Fin (k + 1) → Fin (k + 1 + 1 + 1) := cons fz (fun i => fs (fs (fs i)))

/-- Θ(z) = ∃u (P(u) ∧ u ∉ z) -/
def thetaF {k : Nat} (P : Fm (k + 1)) : Fm (k + 1 + 1) :=
  .ex (.and (ren atU P) (.not (.mem fz (fs fz))))

/-- Φ(z) = z = U ∨ P(z) ∨ (U ∈ z ∧ (z ∈ z xor Θ(z))) -/
def diagF {k : Nat} (P : Fm (k + 1)) : Fm (k + 1 + 1) :=
  .or (.eq fz (fs fz)) (.or (ren atZ P) (.and (.mem (fs fz) fz) (xorF (.mem fz fz) (thetaF P))))

/-! ### Readings of the formulas (definitionally equal to them). -/

section Readings
variable {M : Type} (E : Side → M → M → Prop)

def Trans (s : Side) (a : M) : Prop := ∀ y z : M, ¬¬ E s z y → ¬¬ E s y a → ¬¬ E s z a

def Sing (s : Side) (y : M) : Prop := ∃ h : M, ∀ v : M, (E s v h → v = y) ∧ (v = y → E s v h)

def Tri (s : Side) (a : M) : Prop :=
  ∀ y z : M, ¬¬ E s y a → ¬¬ E s z a → ¬¬ (E s y z ∨ y = z ∨ E s z y)

def WF (s : Side) (a : M) : Prop :=
  ∀ k x : M, ¬¬ E s x a → ¬ E s x k →
    ¬¬ ∃ z : M, (z = x ∨ E s z x) ∧ ¬ E s z k ∧ ∀ w : M, E s w z → ¬¬ E s w k

def St (s : Side) (a : M) : Prop := ∀ x : M, ¬¬ E s x a → E s x a

def Kappa (s : Side) (a : M) : Prop :=
  Trans E s a ∧ (∀ y, ¬¬ E s y a → Trans E s y) ∧ (∀ y, ¬¬ E s y a → ¬ E s y y) ∧
  (∀ y, ¬¬ E s y a → ¬¬ Sing E s y) ∧ Tri E s a ∧ WF E s a ∧ ¬¬ St E s a ∧
  (∀ y, ¬¬ E s y a → ¬¬ St E s y)

def Xor (P Q : Prop) : Prop := P ∧ ¬ Q ∨ ¬ P ∧ Q

end Readings

/-! ### Sides -/

theorem Opp.symm : Opp s c → Opp c s
  | .me => .em
  | .em => .me

section Proof
variable {M : Type} {E : Side → M → M → Prop}

theorem regNil : ∀ i : Fin 0, Regular E (nil i)
  | ⟨_, h⟩ => absurd h (Nat.not_lt_zero _)

theorem regCons {ρ : Fin n → M} (r : Regular E a) (rs : ∀ i, Regular E (ρ i)) :
    ∀ i : Fin (n + 1), Regular E (cons a ρ i)
  | ⟨0, _⟩ => r
  | ⟨i + 1, h⟩ => rs ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem move {r x : M} (s t : Side) (rr : Regular E r) (h : E s x r) : E t x r := by
  cases s <;> cases t
  · exact h
  · exact (rr x).mp h
  · exact (rr x).mpr h
  · exact h

theorem reg_of : Opp s c → (∀ x, E s x a ↔ E c x a) → Regular E a
  | .me, h => h
  | .em, h => fun x => (h x).symm

/-! ### κ-ordinals (no axioms needed)

Every clause of κ is a negation, so κ is ¬¬-stable.  Wherever the proof needs
a fact that it has only up to ¬¬ (a stable face, the regularity of a member),
the goal is a negation, and from ¬¬A and A → ¬B follows ¬B. -/

theorem o_tr (ka : Kappa E s a) : Trans E s a := ka.1
theorem o_mt (ka : Kappa E s a) : ∀ y, ¬¬ E s y a → Trans E s y := ka.2.1
theorem o_irr (ka : Kappa E s a) : ∀ y, ¬¬ E s y a → ¬ E s y y := ka.2.2.1
theorem o_ms (ka : Kappa E s a) : ∀ y, ¬¬ E s y a → ¬¬ Sing E s y := ka.2.2.2.1
theorem o_tri (ka : Kappa E s a) : Tri E s a := ka.2.2.2.2.1
theorem o_wf (ka : Kappa E s a) : WF E s a := ka.2.2.2.2.2.1
theorem o_st (ka : Kappa E s a) : ¬¬ St E s a := ka.2.2.2.2.2.2.1
theorem o_mst (ka : Kappa E s a) : ∀ y, ¬¬ E s y a → ¬¬ St E s y := ka.2.2.2.2.2.2.2

/-- κ is ¬¬-stable. -/
theorem stable (h : ¬¬ Kappa E s a) : Kappa E s a :=
  ⟨fun y z p q n => h fun k => o_tr k y z p q n,
   fun y p y' z' p' q' n => h fun k => o_mt k y p y' z' p' q' n,
   fun y p n => h fun k => o_irr k y p n,
   fun y p n => h fun k => o_ms k y p n,
   fun y z p q n => h fun k => o_tri k y z p q n,
   fun C x p q n => h fun k => o_wf k C x p q n,
   fun n => h fun k => o_st k n,
   fun y p n => h fun k => o_mst k y p n⟩

/-- A ¬¬-member of a κ-ordinal is a κ-ordinal (Lemma 5(1)). -/
theorem member_kappa (ka : Kappa E s a) (ya : ¬¬ E s y a) : Kappa E s y :=
  have up : ∀ {z}, ¬¬ E s z y → ¬¬ E s z a := fun zy => o_tr ka y _ zy ya
  ⟨o_mt ka y ya,
   fun z zy => o_mt ka z (up zy),
   fun z zy => o_irr ka z (up zy),
   fun z zy => o_ms ka z (up zy),
   fun z z' zy z'y => o_tri ka z z' (up zy) (up z'y),
   fun k x xy nxk => o_wf ka k x (up xy) nxk,
   o_mst ka y ya,
   fun z zy => o_mst ka z (up zy)⟩

theorem down (ka : Kappa E s a) (xa : ¬¬ E s x a) : z = x ∨ E s z x → ¬¬ E s z a
  | .inl e => e ▸ xa
  | .inr zx => o_tr ka _ _ (not_not_intro zx) xa

/-- On a stable face, transitivity holds outright. -/
theorem trP (ka : Kappa E s a) (sa : St E s a) : ∀ y z, E s z y → E s y a → E s z a :=
  fun _ z zy ya => sa z (down ka (not_not_intro ya) (.inr zy))

/-- A regular object has both faces stable or neither. -/
theorem stR (rx : Regular E x) (sx : St E s x) : St E t x :=
  fun z h => move s t rx (sx z fun n => h fun h' => n (move t s rx h'))

/-- Lemma 5(3) on a stable face, up to ¬¬: some z = x or z ∈ x lies outside k and
has all its members in k, up to ¬¬. -/
theorem self_wf (kx : Kappa E s x) (sx : St E s x) (nxk : ¬ E s x k) :
    ¬¬ ∃ z : M, (z = x ∨ E s z x) ∧ ¬ E s z k ∧ ∀ w, E s w z → ¬¬ E s w k := fun none =>
  none ⟨x, .inl rfl, nxk, fun w wx nwk =>
    o_wf kx k w (not_not_intro wx) nwk fun ⟨z, zw, nzk, zk⟩ =>
      none ⟨z, .inr (sx z (down kx (not_not_intro wx) zw)), nzk, zk⟩⟩

/-! ### Renaming does what it should -/

theorem sat_ren {s : Side} : ∀ {m n : Nat} (f : Fin m → Fin n) (φ : Fm m) (ρ : Fin n → M)
    (σ : Fin m → M), (∀ i, ρ (f i) = σ i) → (Sat E s (ren f φ) ρ ↔ Sat E s φ σ)
  | _, _, f, .mem i j, ρ, σ, h => by
    show E s (ρ (f i)) (ρ (f j)) ↔ E s (σ i) (σ j)
    rw [h i, h j]
  | _, _, f, .eq i j, ρ, σ, h => by
    show ρ (f i) = ρ (f j) ↔ σ i = σ j
    rw [h i, h j]
  | _, _, f, .not φ, ρ, σ, h => by
    show ¬ Sat E s (ren f φ) ρ ↔ ¬ Sat E s φ σ
    have r := sat_ren (s := s) f φ ρ σ h
    exact ⟨fun n a => n (r.mpr a), fun n a => n (r.mp a)⟩
  | _, _, f, .and φ ψ, ρ, σ, h => by
    show Sat E s (ren f φ) ρ ∧ Sat E s (ren f ψ) ρ ↔ Sat E s φ σ ∧ Sat E s ψ σ
    have r := sat_ren (s := s) f φ ρ σ h
    have q := sat_ren (s := s) f ψ ρ σ h
    exact ⟨fun ⟨a, b⟩ => ⟨r.mp a, q.mp b⟩, fun ⟨a, b⟩ => ⟨r.mpr a, q.mpr b⟩⟩
  | _, _, f, .or φ ψ, ρ, σ, h => by
    show Sat E s (ren f φ) ρ ∨ Sat E s (ren f ψ) ρ ↔ Sat E s φ σ ∨ Sat E s ψ σ
    have r := sat_ren (s := s) f φ ρ σ h
    have q := sat_ren (s := s) f ψ ρ σ h
    exact ⟨fun | .inl a => .inl (r.mp a) | .inr b => .inr (q.mp b),
           fun | .inl a => .inl (r.mpr a) | .inr b => .inr (q.mpr b)⟩
  | _, _, f, .imp φ ψ, ρ, σ, h => by
    show (Sat E s (ren f φ) ρ → Sat E s (ren f ψ) ρ) ↔ (Sat E s φ σ → Sat E s ψ σ)
    have r := sat_ren (s := s) f φ ρ σ h
    have q := sat_ren (s := s) f ψ ρ σ h
    exact ⟨fun g a => q.mp (g (r.mpr a)), fun g a => q.mpr (g (r.mp a))⟩
  | _, _, f, .all φ, ρ, σ, h => by
    show (∀ x, Sat E s (ren (lift f) φ) (cons x ρ)) ↔ ∀ x, Sat E s φ (cons x σ)
    have l : ∀ x, ∀ i, cons x ρ (lift f i) = cons x σ i := fun x => fun
      | ⟨0, _⟩ => rfl
      | ⟨j + 1, hj⟩ => h ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    exact ⟨fun g x => (sat_ren (s := s) (lift f) φ _ _ (l x)).mp (g x),
           fun g x => (sat_ren (s := s) (lift f) φ _ _ (l x)).mpr (g x)⟩
  | _, _, f, .ex φ, ρ, σ, h => by
    show (∃ x, Sat E s (ren (lift f) φ) (cons x ρ)) ↔ ∃ x, Sat E s φ (cons x σ)
    have l : ∀ x, ∀ i, cons x ρ (lift f i) = cons x σ i := fun x => fun
      | ⟨0, _⟩ => rfl
      | ⟨j + 1, hj⟩ => h ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    exact ⟨fun ⟨x, a⟩ => ⟨x, (sat_ren (s := s) (lift f) φ _ _ (l x)).mp a⟩,
           fun ⟨x, a⟩ => ⟨x, (sat_ren (s := s) (lift f) φ _ _ (l x)).mpr a⟩⟩

/-! ### The reading of the diagonal formula -/

/-- The reading of Φ on side t, with Θ(z) = ∃u (P(u) ∧ u ∉ z). -/
def PhiS (E : Side → M → M → Prop) {k : Nat} (P : Fm (k + 1)) (ρ : Fin k → M) (U : M)
    (t : Side) (z : M) : Prop :=
  z = U ∨ Sat E t P (cons z ρ) ∨
    (E t U z ∧ Xor (E t z z) (∃ u, Sat E t P (cons u ρ) ∧ ¬ E t u z))

theorem sat_diagF {k : Nat} (P : Fm (k + 1)) (ρ : Fin k → M) (U : M) (t : Side) (z : M) :
    Sat E t (diagF P) (cons z (cons U ρ)) ↔ PhiS E P ρ U t z := by
  have hz : Sat E t (ren atZ P) (cons z (cons U ρ)) ↔ Sat E t P (cons z ρ) :=
    sat_ren atZ P (cons z (cons U ρ)) (cons z ρ) fun
      | ⟨0, _⟩ => rfl
      | ⟨_ + 1, _⟩ => rfl
  have hu : ∀ u, Sat E t (ren atU P) (cons u (cons z (cons U ρ))) ↔ Sat E t P (cons u ρ) :=
    fun u => sat_ren atU P (cons u (cons z (cons U ρ))) (cons u ρ) fun
      | ⟨0, _⟩ => rfl
      | ⟨_ + 1, _⟩ => rfl
  have hθ : Sat E t (thetaF P) (cons z (cons U ρ)) ↔ ∃ u, Sat E t P (cons u ρ) ∧ ¬ E t u z :=
    ⟨fun ⟨u, pu, nu⟩ => ⟨u, (hu u).mp pu, nu⟩, fun ⟨u, pu, nu⟩ => ⟨u, (hu u).mpr pu, nu⟩⟩
  constructor
  · intro h
    rcases h with e | p | ⟨uz, ⟨zz, nθ⟩ | ⟨nzz, θ⟩⟩
    · exact .inl e
    · exact .inr (.inl (hz.mp p))
    · exact .inr (.inr ⟨uz, .inl ⟨zz, fun θ' => nθ (hθ.mpr θ')⟩⟩)
    · exact .inr (.inr ⟨uz, .inr ⟨nzz, hθ.mp θ⟩⟩)
  · intro h
    rcases h with e | p | ⟨uz, ⟨zz, nθ⟩ | ⟨nzz, θ⟩⟩
    · exact .inl e
    · exact .inr (.inl (hz.mpr p))
    · exact .inr (.inr ⟨uz, .inl ⟨zz, fun θ' => nθ (hθ.mp θ')⟩⟩)
    · exact .inr (.inr ⟨uz, .inr ⟨nzz, hθ.mpr θ⟩⟩)

/-! ### What comprehension alone gives -/

section WithC
variable (C : Comp M E)
include C

theorem comp (o : Opp s c) {k : Nat} (φ : Fm (k + 1)) (ρ : Fin k → M)
    (r : ∀ i, Regular E (ρ i)) :
    ∃ A : M, ∀ x : M, (E s x A ↔ Sat E c φ (cons x ρ)) ∧ (E c x A ↔ Sat E s φ (cons x ρ)) := by
  obtain ⟨A, hA⟩ := C φ ρ r
  cases o
  · exact ⟨A, fun x => ⟨(hA x).2, (hA x).1⟩⟩
  · exact ⟨A, hA⟩

/-- The universal object {x | x = x}. -/
theorem univ : ∃ U : M, ∀ s x, E s x U := by
  obtain ⟨U, hU⟩ := comp C .me (.eq fz fz) nil regNil
  refine ⟨U, fun s x => ?_⟩
  cases s
  · exact (hU x).1.mpr rfl
  · exact (hU x).2.mpr rfl

/-! ### The diagonal: comprehension alone, no ME -/

theorem diagonal_core {k : Nat} (P : Fm (k + 1)) (ρ : Fin k → M)
    (rρ : ∀ i, Regular E (ρ i)) (o : Opp b c) : ¬ Asymmetric E P ρ b c := by
  rintro ⟨rich, irr, W, Wb, Wc, PW⟩
  obtain ⟨U, full⟩ := univ C
  have U_reg : Regular E U := fun x => ⟨fun _ => full _ x, fun _ => full _ x⟩
  -- A := {z | Φ(z)}
  obtain ⟨A, hA⟩ := comp C o (diagF P) (cons U ρ) (regCons U_reg rρ)
  have Ab : ∀ z, E b z A ↔ PhiS E P ρ U c z := fun z => (hA z).1.trans (sat_diagF P ρ U c z)
  have Ac : ∀ z, E c z A ↔ PhiS E P ρ U b z := fun z => (hA z).2.trans (sat_diagF P ρ U b z)
  have U_not : ¬ Sat E b P (cons U ρ) := fun pu => irr U U pu (full b U) (full b U)
  have W_not : ¬ Sat E c P (cons W ρ) := fun pc => irr W W PW ((Wb W).mpr pc) ((Wb W).mpr pc)
  -- On side b, A omits the P-object W; on side c it contains every P-object.
  have omits : ¬ E b W A := fun h => by
    rcases (Ab W).mp h with e | pc | ⟨UW, _⟩
    · exact U_not (e ▸ PW)
    · exact W_not pc
    · exact U_not ((Wc U).mp UW)
  have θb : ∃ u, Sat E b P (cons u ρ) ∧ ¬ E b u A := ⟨W, PW, omits⟩
  have nθc : ¬ ∃ u, Sat E c P (cons u ρ) ∧ ¬ E c u A := fun ⟨u, pu, nu⟩ =>
    nu ((Ac u).mpr (.inr (.inl (rich u pu))))
  have AU : A ≠ U := fun e => omits (by rw [e]; exact full b W)
  have UAb : E b U A := (Ab U).mpr (.inl rfl)
  have UAc : E c U A := (Ac U).mpr (.inl rfl)
  have A_not : ¬ Sat E b P (cons A ρ) := fun pa => irr A U pa UAb (full b U)
  -- At z = A only the last disjunct can hold.
  have x_y : E b A A → E c A A := fun x => by
    rcases (Ab A).mp x with e | pa | ⟨_, ⟨y, _⟩ | ⟨_, θ⟩⟩
    · exact absurd e AU
    · exact absurd (rich A pa) A_not
    · exact y
    · exact absurd θ nθc
  have y_x : E c A A → E b A A := fun y => (Ab A).mpr (.inr (.inr ⟨UAc, .inl ⟨y, nθc⟩⟩))
  have y_nx : E c A A → ¬ E b A A := fun y => by
    rcases (Ac A).mp y with e | pa | ⟨_, ⟨_, nθ⟩ | ⟨nx, _⟩⟩
    · exact absurd e AU
    · exact absurd pa A_not
    · exact absurd θb nθ
    · exact nx
  have nx_y : ¬ E b A A → E c A A := fun nx => (Ac A).mpr (.inr (.inr ⟨UAb, .inr ⟨nx, θb⟩⟩))
  have no_x : ¬ E b A A := fun x => y_nx (x_y x) x
  exact no_x (y_x (nx_y no_x))

end WithC

/-! ### The κ-ordinals are asymmetric: ME and COMP -/

section WithT
variable (T : DESTminus M E)
include T

theorem me : Opp s c → ∀ a b : M, (∀ x, E s x a ↔ E c x b) → a = b
  | .me, a, b, h => T.ME a b h
  | .em, a, b, h => (T.ME b a fun x => (h x).symm).symm

/-- An object with the s-face of a regular object is that object (Lemma 2). -/
theorem same (o : Opp s c) (rg : Regular E g)
    (to : ∀ x, E s x z → E s x g) (fr : ∀ x, E s x g → E s x z) : z = g :=
  me T o z g fun x => ⟨fun h => move s c rg (to x h), fun h => fr x (move c s rg h)⟩

/-- Regular objects have singletons on both sides: {x | x = y}. -/
theorem sing_reg (o : Opp s c) (ry : Regular E y) : Sing E s y := by
  obtain ⟨h, hh⟩ := comp T.COMP o (.eq fz (fs fz)) (cons y nil) (regCons ry regNil)
  exact ⟨h, fun v => ⟨(hh v).1.mp, (hh v).1.mpr⟩⟩

/-- Objects with singletons on both sides are regular (Lemma 4; Holmes Lemma 2.10). -/
theorem sing_sing (o : Opp s c) : Sing E s y → Sing E c y → Regular E y := by
  rintro ⟨h, hs⟩ ⟨h', hc⟩
  have e : h = h' := me T o h h' fun x =>
    ⟨fun a => (hc x).2 ((hs x).1 a), fun a => (hs x).2 ((hc x).1 a)⟩
  subst e
  have rh : Regular E h := reg_of o fun x =>
    ⟨fun a => (hc x).2 ((hs x).1 a), fun a => (hs x).2 ((hc x).1 a)⟩
  -- k := {x | ∃u (x ∈ u ∧ u ∈ h)}: its c-face is the s-face of y.
  obtain ⟨k, hk⟩ := comp T.COMP o (.ex (.and (.mem (fs fz) fz) (.mem fz (fs (fs fz)))))
    (cons h nil) (regCons rh regNil)
  have ck : ∀ x, E c x k ↔ E s x y := fun x =>
    ⟨fun a => by
      obtain ⟨u, xu, uh⟩ := (hk x).2.mp a
      have xu : E s x u := xu
      have uy : u = y := (hs u).1 uh
      exact uy ▸ xu,
     fun a => (hk x).2.mpr ⟨y, a, (hs y).2 rfl⟩⟩
  have e₂ : y = k := me T o y k fun x => (ck x).symm
  subst e₂
  exact reg_of o fun x => (ck x).symm

/-- At a regular point the two readings of κ agree: Lemma 3 for κ(r), which gives
Lemma 5(4) (Holmes Lemma 2.11). -/
theorem kappa_flip (o : Opp s c) (rr : Regular E r) (kr : Kappa E s r) : Kappa E c r := by
  obtain ⟨U, full⟩ := univ T.COMP
  obtain ⟨A, hA⟩ := comp T.COMP o (kappaF (fs fz)) (cons r nil) (regCons rr regNil)
  have e : A = U := me T o.symm A U fun x => ⟨fun _ => full s x, fun _ => (hA x).2.mpr kr⟩
  have hUA : E s U A := by rw [e]; exact full s U
  exact (hA U).1.mp hUA

/-- A regular transitive object whose face lies inside a κ-ordinal α is α or a
member of α, up to ¬¬ (Lemma 6).  The faces of α and γ are stable. -/
theorem seg (o : Opp s c) (kα : Kappa E s α) (sα : St E s α) (rγ : Regular E γ)
    (sγ : St E s γ) (tγ : ∀ y z, E s z y → E s y γ → E s z γ) (γα : ∀ x, E s x γ → E s x α) :
    ¬¬ (γ = α ∨ E s γ α) := fun no =>
  have sub : ∀ x, E s x α → E s x γ := fun x xα => sγ x fun nxγ =>
    o_wf kα γ x (not_not_intro xα) nxγ fun ⟨z, zx, nzγ, zγ⟩ =>
      have zα := sα z (down kα (not_not_intro xα) zx)
      o_mst kα z (not_not_intro zα) fun sz =>
        have back : ∀ y, E s y γ → E s y z := fun y yγ => sz y fun nyz =>
          o_tri kα y z (not_not_intro (γα y yγ)) (not_not_intro zα) fun
            | .inl yz => nyz yz
            | .inr (.inl e) => nzγ (e ▸ yγ)
            | .inr (.inr zy) => nzγ (tγ y z zy yγ)
        no (.inr (same T o rγ (fun w wz => sγ w (zγ w wz)) back ▸ zα))
  no (.inl (same T o rγ sub γα).symm)

/-- Regular κ-ordinals with stable faces are comparable, up to ¬¬ (Lemma 7): apply
`seg` to γ := α ∩ β. -/
theorem compare (o : Opp s c) (rα : Regular E α) (rβ : Regular E β) (kα : Kappa E s α)
    (kβ : Kappa E s β) (sα : St E s α) (sβ : St E s β) :
    ¬¬ (E s α β ∨ α = β ∨ E s β α) := by
  intro n
  obtain ⟨γ, hγ⟩ := comp T.COMP o (.and (.mem fz (fs fz)) (.mem fz (fs (fs fz))))
    (cons α (cons β nil)) (regCons rα (regCons rβ regNil))
  have g : ∀ x, E s x γ ↔ E s x α ∧ E s x β := fun x =>
    ⟨fun h => ⟨move c s rα ((hγ x).1.mp h).1, move c s rβ ((hγ x).1.mp h).2⟩,
     fun h => (hγ x).1.mpr ⟨move s c rα h.1, move s c rβ h.2⟩⟩
  have rγ : Regular E γ := reg_of o fun x =>
    ⟨fun h => (hγ x).2.mpr ((g x).mp h), fun h => (g x).mpr ((hγ x).2.mp h)⟩
  have sγ : St E s γ := fun x h => (g x).mpr
    ⟨sα x fun k => h fun i => k ((g x).mp i).1, sβ x fun k => h fun i => k ((g x).mp i).2⟩
  have tγ : ∀ y z, E s z y → E s y γ → E s z γ := fun y z zy yγ =>
    (g z).mpr ⟨trP kα sα y z zy ((g y).mp yγ).1, trP kβ sβ y z zy ((g y).mp yγ).2⟩
  apply seg T o kα sα rγ sγ tγ fun x h => ((g x).mp h).1
  intro a
  apply seg T o kβ sβ rγ sγ tγ fun x h => ((g x).mp h).2
  intro b
  rcases a with a | a <;> rcases b with b | b
  · exact n (.inr (.inl (a.symm.trans b)))
  · exact n (.inl (a ▸ b))
  · exact n (.inr (.inr (b ▸ a)))
  · exact o_irr kα γ (not_not_intro a) ((g γ).mpr ⟨a, b⟩)

/-- Proposition 1: if every κ-ordinal of side c is regular up to ¬¬, then κ is
asymmetric from c to b, with W := {x | κ(x)}. -/
theorem one (o : Opp b c) (poor : ∀ x, Kappa E c x → ¬¬ Regular E x) :
    Asymmetric E (kappaF fz) nil b c := by
  obtain ⟨w, hW⟩ := comp T.COMP o (kappaF fz) nil regNil
  have wb : ∀ x, E b x w ↔ Kappa E c x := fun x => (hW x).1
  have rich : ∀ x, Kappa E c x → Kappa E b x := fun x kx =>
    stable fun n => poor x kx fun rx => n (kappa_flip T o.symm rx kx)
  -- Under the goal False, a ¬¬-member y of w is regular, a κ-ordinal on both
  -- sides, and has a stable face.
  have get : ∀ {y}, ¬¬ E b y w →
      (Regular E y → Kappa E c y → Kappa E b y → St E b y → False) → False :=
    fun {y} yw f => yw fun h =>
      have ky := (wb y).mp h
      poor y ky fun ry => o_st ky fun sy => f ry ky (kappa_flip T o.symm ry ky) (stR ry sy)
  have kw : Kappa E b w :=
    ⟨fun y z zy yw nzw => get yw fun ry ky _ _ =>
        zy fun h => nzw ((wb z).mpr (member_kappa ky (not_not_intro (move b c ry h)))),
     fun y yw y' z' p q n => get yw fun _ _ ky _ => o_tr ky y' z' p q n,
     fun y yw yy => get yw fun _ _ ky _ => o_irr ky y (not_not_intro yy) yy,
     fun y yw n => get yw fun ry _ _ _ => n (sing_reg T o ry),
     fun y z yw zw n => get yw fun ry _ ky sy => get zw fun rz _ kz sz =>
        compare T o ry rz ky kz sy sz n,
     fun C x xw nxC n => get xw fun _ _ kx sx => self_wf kx sx nxC n,
     fun n => n fun x h => (wb x).mpr (stable fun k => h fun xw => k ((wb x).mp xw)),
     fun y yw n => get yw fun _ _ _ sy => n sy⟩
  exact ⟨rich, fun x y kx yx => o_irr kx y (not_not_intro yx), w, wb, fun x => (hW x).2, kw⟩

/-- By Proposition 1 and the diagonal, each side has an irregular κ-ordinal, up
to ¬¬. -/
theorem irregular (o : Opp b c) : ¬¬ ∃ a : M, Kappa E c a ∧ ¬ Regular E a := fun none =>
  diagonal_core T.COMP (kappaF fz) nil regNil o (one T o fun x kx nx => none ⟨x, kx, nx⟩)

/-- Cut (in Proposition 2): an irregular κ-ordinal p contains every regular
κ-ordinal t whose members are regular up to ¬¬.  The faces of p and t are stable. -/
theorem cut (o : Opp s c) (kp : Kappa E s p) (sp : St E s p) (np : ¬ Regular E p)
    (rt : Regular E t) (kt : Kappa E s t) (st : St E s t)
    (tpure : ∀ y, ¬¬ E s y t → ¬¬ Regular E y) : E s t p :=
  have inside : ∀ z, Regular E z → Kappa E s z → St E s z → (∀ x, E s x z → E s x p) →
      E s z p := fun z rz kz sz zp => sp z fun nzp =>
    seg T o kp sp rz sz (trP kz sz) zp fun
      | .inl e => np (e ▸ rz)
      | .inr h => nzp h
  inside t rt kt st fun x xt => sp x fun nxp =>
    o_wf kt p x (not_not_intro xt) nxp fun ⟨z, zx, nzp, zp⟩ =>
      have zt := down kt (not_not_intro xt) zx
      tpure z zt fun rz => o_mst kt z zt fun sz =>
        nzp (inside z rz (member_kappa kt zt) sz fun w wz => sp w (zp w wz))

/-- Descent (in Proposition 2): below an irregular κ-ordinal there is one whose
members are regular up to ¬¬; all up to ¬¬. -/
theorem descent (o : Opp s c) (kα : Kappa E s α) (nα : ¬ Regular E α) :
    ¬¬ ∃ p : M, Kappa E s p ∧ ¬ Regular E p ∧ ∀ y, ¬¬ E s y p → ¬¬ Regular E y := by
  intro none
  -- D := {x | x has a singleton}; its s-face: has a c-singleton.
  obtain ⟨D, hD⟩ := comp T.COMP o (singF fz) nil regNil
  have sreg : ∀ {y}, ¬¬ E s y α → ¬¬ Sing E c y → ¬¬ Regular E y := fun {y} yα sc n =>
    o_ms kα y yα fun ss => sc fun sc' => n (sing_sing T o ss sc')
  apply show ¬¬ ∃ x, ¬¬ E s x α ∧ ¬ Regular E x from fun nx =>
    none ⟨α, kα, nα, fun y yα ny => nx ⟨y, yα, ny⟩⟩
  rintro ⟨x, xα, nx⟩
  apply o_wf kα D x xα fun xD => sreg xα (not_not_intro ((hD x).1.mp xD)) nx
  rintro ⟨z, zx, nzD, zD⟩
  have zα := down kα xα zx
  exact none ⟨z, member_kappa kα zα, fun rz => nzD ((hD z).1.mpr (sing_reg T o.symm rz)),
    fun y yz => sreg (o_tr kα z y yz zα) fun n =>
      yz fun h => zD y h fun yD => n ((hD y).1.mp yD)⟩

/-- Each s-member of p is a c-member of q (in Proposition 2). -/
theorem into (o : Opp s c) (kp : Kappa E s p) (pp : ∀ y, ¬¬ E s y p → ¬¬ Regular E y)
    (kq : Kappa E c q) (sq : St E c q) (nq : ¬ Regular E q) (x : M) (xp : E s x p) : E c x q :=
  sq x fun nxq => pp x (not_not_intro xp) fun rx => o_mst kp x (not_not_intro xp) fun sx =>
    nxq (cut T o.symm kq sq nq rx (kappa_flip T o rx (member_kappa kp (not_not_intro xp)))
      (stR rx sx) fun y yx => pp y (o_tr kp x y (fun n => yx fun h => n (move c s rx h))
        (not_not_intro xp)))

/-- Proposition 2: the two sides do not both have irregular κ-ordinals.  By descent,
take p and q whose members are regular up to ¬¬, and open (K7) for both; by `into`,
F_∈(p) = F_ε(q), so ME identifies them and p is regular. -/
theorem both (ka : Kappa E .mem a) (na : ¬ Regular E a) (ka' : Kappa E .eps a')
    (na' : ¬ Regular E a') : False := by
  apply descent T .me ka na
  rintro ⟨p, kp, np, pp⟩
  apply descent T .em ka' na'
  rintro ⟨q, kq, nq, pq⟩
  apply o_st kp
  intro sp
  apply o_st kq
  intro sq
  have face : ∀ x, E .mem x p ↔ E .eps x q := fun x =>
    ⟨into T .me kp pp kq sq nq x, into T .em kq pq kp sp np x⟩
  have e : p = q := T.ME p q face
  subst e
  exact np face

/-- Theorem 2: each side has an irregular κ-ordinal, against Proposition 2. -/
theorem refutation : False :=
  irregular T Opp.em fun ⟨_, ka, na⟩ =>
    irregular T Opp.me fun ⟨_, ka', na'⟩ => both T ka na ka' na'

end WithT
end Proof

/-! ## Part III. The theorems (statements are part of the trusted part) -/

/-- Comprehension alone refutes every asymmetric formula.  No ME. -/
theorem diagonal (M : Type) (E : Side → M → M → Prop) (C : Comp M E)
    {k : Nat} (P : Fm (k + 1)) (ρ : Fin k → M)
    (rρ : ∀ i : Fin k, Regular E (ρ i))
    {b c : Side} (o : Opp b c) : ¬ Asymmetric E P ρ b c :=
  diagonal_core C P ρ rρ o

/-- ME + COMP (DEST without REG) has no model, without classical logic. -/
theorem inconsistent (M : Type) (E : Side → M → M → Prop) (T : DESTminus M E) : False :=
  refutation T

/-- Full DEST has no model. -/
theorem DEST_inconsistent (M : Type) (E : Side → M → M → Prop) (T : DEST M E) : False :=
  inconsistent M E T.core

end DEST

#print axioms DEST.diagonal
#print axioms DEST.inconsistent
#print axioms DEST.DEST_inconsistent
