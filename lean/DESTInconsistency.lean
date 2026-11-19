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
`diagonal` uses comprehension alone: no ME and no classical logic.
Classical logic enters the main theorem only as the explicit hypothesis
`dne`.  REG is never used.

Check:  cd lean && lake build
        lake env lean DESTInconsistency.lean
Paper: ../pdf/dest-inconsistency.en.pdf
Agda version: ../agda/DESTInconsistency.agda.
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

/-- y has a singleton:  ∃h ∀v (v ∈ h ↔ v = y) -/
def singF (i : Fin n) : Fm n :=
  .ex (.all (iffF (.mem fz (fs fz)) (.eq fz (fs (fs i)))))

/-- a is transitive:  ∀y ∀z (z ∈ y → y ∈ a → z ∈ a) -/
def transF (i : Fin n) : Fm n :=
  .all (.all (.imp (.mem fz (fs fz)) (.imp (.mem (fs fz) (fs (fs i))) (.mem fz (fs (fs i))))))

/-- ∀y ∀z (y ∈ a → z ∈ a → y ∈ z ∨ y = z ∨ z ∈ y) -/
def triF (i : Fin n) : Fm n :=
  .all (.all (.imp (.mem (fs fz) (fs (fs i))) (.imp (.mem fz (fs (fs i)))
    (.or (.mem (fs fz) fz) (.or (.eq (fs fz) fz) (.mem fz (fs fz)))))))

/-- ∀C ∀x (x ∈ a → x ∉ C → ∃z ((z = x ∨ z ∈ x) ∧ z ∉ C ∧ ∀w (w ∈ z → w ∈ C))) -/
def wfF (i : Fin n) : Fm n :=
  .all (.all (.imp (.mem fz (fs (fs i))) (.imp (.not (.mem fz (fs fz)))
    (.ex (.and (.or (.eq fz (fs fz)) (.mem fz (fs fz)))
      (.and (.not (.mem fz (fs (fs fz))))
        (.all (.imp (.mem fz (fs fz)) (.mem fz (fs (fs (fs fz))))))))))))

/-- a is an ordinal: transitive, members transitive, members not
self-membered, members have singletons, trichotomous, well-founded. -/
def ordF (i : Fin n) : Fm n :=
  .and (transF i)
    (.and (.all (.imp (.mem fz (fs i)) (transF fz)))
      (.and (.all (.imp (.mem fz (fs i)) (.not (.mem fz fz))))
        (.and (.all (.imp (.mem fz (fs i)) (singF fz)))
          (.and (triF i) (wfF i)))))

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

def Trans (s : Side) (a : M) : Prop := ∀ y z : M, E s z y → E s y a → E s z a

def Sing (s : Side) (y : M) : Prop := ∃ h : M, ∀ v : M, (E s v h → v = y) ∧ (v = y → E s v h)

def Tri (s : Side) (a : M) : Prop :=
  ∀ y z : M, E s y a → E s z a → E s y z ∨ y = z ∨ E s z y

def WF (s : Side) (a : M) : Prop :=
  ∀ k x : M, E s x a → ¬ E s x k →
    ∃ z : M, (z = x ∨ E s z x) ∧ ¬ E s z k ∧ ∀ w : M, E s w z → E s w k

def Ord (s : Side) (a : M) : Prop :=
  Trans E s a ∧ (∀ y, E s y a → Trans E s y) ∧ (∀ y, E s y a → ¬ E s y y) ∧
  (∀ y, E s y a → Sing E s y) ∧ Tri E s a ∧ WF E s a

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

/-! ### Ordinals (no axioms needed) -/

theorem o_tr (oa : Ord E s a) : Trans E s a := oa.1
theorem o_mt (oa : Ord E s a) : ∀ y, E s y a → Trans E s y := oa.2.1
theorem o_irr (oa : Ord E s a) : ∀ y, E s y a → ¬ E s y y := oa.2.2.1
theorem o_ms (oa : Ord E s a) : ∀ y, E s y a → Sing E s y := oa.2.2.2.1
theorem o_tri (oa : Ord E s a) : Tri E s a := oa.2.2.2.2.1
theorem o_wf (oa : Ord E s a) : WF E s a := oa.2.2.2.2.2

theorem down (oa : Ord E s a) (xa : E s x a) : z = x ∨ E s z x → E s z a
  | .inl e => e ▸ xa
  | .inr zx => o_tr oa _ _ zx xa

theorem member_ord (oa : Ord E s a) (ya : E s y a) : Ord E s y :=
  have up : ∀ {z}, E s z y → E s z a := fun zy => o_tr oa _ _ zy ya
  ⟨o_mt oa y ya,
   fun z zy => o_mt oa z (up zy),
   fun z zy => o_irr oa z (up zy),
   fun z zy => o_ms oa z (up zy),
   fun z z' zy z'y => o_tri oa z z' (up zy) (up z'y),
   fun k x xy nxk => o_wf oa k x (up xy) nxk⟩

theorem not_self (oa : Ord E s a) : ¬ E s a a := fun aa => o_irr oa a aa aa

/-! ### Renaming does what it should -/

theorem lift_ok {f : Fin m → Fin n} {ρ : Fin n → M} {σ : Fin m → M}
    (h : ∀ i, ρ (f i) = σ i) (x : M) : ∀ i, cons x ρ (lift f i) = cons x σ i
  | ⟨0, _⟩ => rfl
  | ⟨j + 1, hj⟩ => h ⟨j, Nat.lt_of_succ_lt_succ hj⟩

theorem sat_ren {s : Side} : ∀ {m n : Nat} (f : Fin m → Fin n) (φ : Fm m) (ρ : Fin n → M)
    (σ : Fin m → M), (∀ i, ρ (f i) = σ i) → (Sat E s (ren f φ) ρ ↔ Sat E s φ σ)
  | _, _, f, .mem i j, ρ, σ, h => by
    show E s (ρ (f i)) (ρ (f j)) ↔ E s (σ i) (σ j)
    rw [h i, h j]
  | _, _, f, .eq i j, ρ, σ, h => by
    show ρ (f i) = ρ (f j) ↔ σ i = σ j
    rw [h i, h j]
  | _, _, f, .not φ, ρ, σ, h => not_congr (sat_ren f φ ρ σ h)
  | _, _, f, .and φ ψ, ρ, σ, h => and_congr (sat_ren f φ ρ σ h) (sat_ren f ψ ρ σ h)
  | _, _, f, .or φ ψ, ρ, σ, h => or_congr (sat_ren f φ ρ σ h) (sat_ren f ψ ρ σ h)
  | _, _, f, .imp φ ψ, ρ, σ, h => imp_congr (sat_ren f φ ρ σ h) (sat_ren f ψ ρ σ h)
  | _, _, f, .all φ, ρ, σ, h => forall_congr' fun x => sat_ren (lift f) φ _ _ (lift_ok h x)
  | _, _, f, .ex φ, ρ, σ, h => exists_congr fun x => sat_ren (lift f) φ _ _ (lift_ok h x)

/-! ### The reading of the diagonal formula -/

/-- The reading of Φ on side t, with Θ(z) = ∃u (P(u) ∧ u ∉ z). -/
def PhiS (E : Side → M → M → Prop) {k : Nat} (P : Fm (k + 1)) (ρ : Fin k → M) (U : M)
    (t : Side) (z : M) : Prop :=
  z = U ∨ Sat E t P (cons z ρ) ∨
    (E t U z ∧ Xor (E t z z) (∃ u, Sat E t P (cons u ρ) ∧ ¬ E t u z))

theorem sat_diagF {k : Nat} (P : Fm (k + 1)) (ρ : Fin k → M) (U : M) (t : Side) (z : M) :
    Sat E t (diagF P) (cons z (cons U ρ)) ↔ PhiS E P ρ U t z :=
  have hθ : Sat E t (thetaF P) (cons z (cons U ρ)) ↔ ∃ u, Sat E t P (cons u ρ) ∧ ¬ E t u z :=
    exists_congr fun _ =>
      and_congr (sat_ren atU P _ _ fun | ⟨0, _⟩ => rfl | ⟨_ + 1, _⟩ => rfl) .rfl
  or_congr .rfl (or_congr (sat_ren atZ P _ _ fun | ⟨0, _⟩ => rfl | ⟨_ + 1, _⟩ => rfl)
    (and_congr .rfl (or_congr (and_congr .rfl (not_congr hθ)) (and_congr .rfl hθ))))

/-! ### The exclusive-or lemma: propositional and intuitionistic -/

/-- With X = (A ∈_s A), Y = (A ∈_s̄ A), S = φ^s(A), T = φ^s̄(A):
if X ↔ (Y ⊕ T) and Y ↔ (X ⊕ S), then S and ¬T do not both hold. -/
theorem xor_lemma (hx : X ↔ Xor Y T) (hy : Y ↔ Xor X S) (s : S) (nt : ¬ T) : False :=
  have nx : ¬ X := fun x => match hx.mp x with
    | .inl ⟨y, _⟩ => match hy.mp y with
      | .inl ⟨_, ns⟩ => ns s
      | .inr ⟨n, _⟩ => n x
    | .inr ⟨_, t⟩ => nt t
  nx (hx.mpr (.inl ⟨hy.mpr (.inr ⟨nx, s⟩), nt⟩))

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

/-! ### The diagonal: comprehension alone, no ME, no classical logic -/

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
  -- At z = A only the last disjunct can hold, so the exclusive-or lemma applies.
  have last : ∀ {t}, E t U A → ¬ Sat E t P (cons A ρ) →
      (PhiS E P ρ U t A ↔ Xor (E t A A) (∃ u, Sat E t P (cons u ρ) ∧ ¬ E t u A)) :=
    fun UA np => ⟨fun | .inl e => absurd e AU | .inr (.inl pa) => absurd pa np
                      | .inr (.inr ⟨_, x⟩) => x, fun x => .inr (.inr ⟨UA, x⟩)⟩
  exact xor_lemma ((Ab A).trans (last UAc fun pa => A_not (rich A pa)))
    ((Ac A).trans (last UAb A_not)) θb nθc

end WithC

/-! ### The ordinals are asymmetric: ME, COMP and classical logic -/

section WithT
variable (T : DESTminus M E)
include T

theorem me : Opp s c → ∀ a b : M, (∀ x, E s x a ↔ E c x b) → a = b
  | .me, a, b, h => T.ME a b h
  | .em, a, b, h => (T.ME b a fun x => (h x).symm).symm

/-- An object with the s-face of a regular object is that object. -/
theorem same (o : Opp s c) (rg : Regular E g)
    (to : ∀ x, E s x z → E s x g) (fr : ∀ x, E s x g → E s x z) : z = g :=
  me T o z g fun x => ⟨fun h => move s c rg (to x h), fun h => fr x (move c s rg h)⟩

/-- Regular objects have singletons on both sides: {x | x = y}. -/
theorem sing_reg (o : Opp s c) (ry : Regular E y) : Sing E s y := by
  obtain ⟨h, hh⟩ := comp T.COMP o (.eq fz (fs fz)) (cons y nil) (regCons ry regNil)
  exact ⟨h, fun v => ⟨(hh v).1.mp, (hh v).1.mpr⟩⟩

/-- Objects with singletons on both sides are regular (Holmes Lemma 2.10). -/
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

section WithDNE
variable (dne : ∀ P : Prop, ¬¬P → P)
include dne

/-- At a regular point the two readings of the ordinal formula agree
(Holmes Lemma 2.11): the exclusive-or lemma for {x | x ∈ x ⊕ ord(r)}. -/
theorem ord_flip (o : Opp s c) (rr : Regular E r) (or : Ord E s r) : Ord E c r := by
  obtain ⟨A, hA⟩ := comp T.COMP o (xorF (.mem fz fz) (ordF (fs fz))) (cons r nil)
    (regCons rr regNil)
  exact dne _ fun n => xor_lemma (hA A).1 (hA A).2 or n

omit T in
theorem self_wf (ox : Ord E s x) (nxk : ¬ E s x k) :
    ∃ z : M, (z = x ∨ E s z x) ∧ ¬ E s z k ∧ ∀ w, E s w z → E s w k :=
  dne _ fun none => none ⟨x, .inl rfl, nxk, fun w wx => dne _ fun nwk => by
    obtain ⟨z, zw, nzk, zk⟩ := o_wf ox k w wx nwk
    exact none ⟨z, .inr (down ox wx zw), nzk, zk⟩⟩

/-- A regular transitive object whose face lies inside an ordinal α is α or
a member of α. -/
theorem seg (o : Opp s c) (oα : Ord E s α) (rγ : Regular E γ) (tγ : Trans E s γ)
    (γα : ∀ x, E s x γ → E s x α) : γ = α ∨ E s γ α :=
  dne _ fun no => by
    have sub : ∀ x, E s x α → E s x γ := fun x xα => dne _ fun nxγ => by
      obtain ⟨z, zx, nzγ, zγ⟩ := o_wf oα γ x xα nxγ
      have zα := down oα xα zx
      have back : ∀ y, E s y γ → E s y z := fun y yγ => by
        rcases o_tri oα y z (γα y yγ) zα with yz | e | zy
        · exact yz
        · exact absurd (e ▸ yγ) nzγ
        · exact absurd (tγ y z zy yγ) nzγ
      have zγ' : z = γ := same T o rγ zγ back
      exact no (.inr (zγ' ▸ zα))
    exact no (.inl (same T o rγ sub γα).symm)

/-- Regular ordinals are comparable: apply `seg` to γ := α ∩ β. -/
theorem compare (o : Opp s c) (rα : Regular E α) (rβ : Regular E β)
    (oα : Ord E s α) (oβ : Ord E s β) : E s α β ∨ α = β ∨ E s β α := by
  obtain ⟨γ, hγ⟩ := comp T.COMP o (.and (.mem fz (fs fz)) (.mem fz (fs (fs fz))))
    (cons α (cons β nil)) (regCons rα (regCons rβ regNil))
  have g : ∀ x, E s x γ ↔ E s x α ∧ E s x β := fun x =>
    ⟨fun h => ⟨move c s rα ((hγ x).1.mp h).1, move c s rβ ((hγ x).1.mp h).2⟩,
     fun h => (hγ x).1.mpr ⟨move s c rα h.1, move s c rβ h.2⟩⟩
  have rγ : Regular E γ := reg_of o fun x =>
    ⟨fun h => (hγ x).2.mpr ((g x).mp h), fun h => (g x).mpr ((hγ x).2.mp h)⟩
  have tγ : Trans E s γ := fun y z zy yγ =>
    (g z).mpr ⟨o_tr oα y z zy ((g y).mp yγ).1, o_tr oβ y z zy ((g y).mp yγ).2⟩
  have h1 := seg T dne o oα rγ tγ fun x h => ((g x).mp h).1
  have h2 := seg T dne o oβ rγ tγ fun x h => ((g x).mp h).2
  rcases h1 with a | a <;> rcases h2 with b | b
  · exact .inr (.inl (a.symm.trans b))
  · exact .inl (a ▸ b)
  · exact .inr (.inr (b ▸ a))
  · exact absurd ((g γ).mpr ⟨a, b⟩) (o_irr oα γ a)

/-- Proposition 1: if every ordinal of side c is regular, the ordinal formula is
asymmetric from c to b, with W := {x | ord(x)}. -/
theorem one (o : Opp b c) (poor : ∀ x, Ord E c x → Regular E x) :
    Asymmetric E (ordF fz) nil b c := by
  obtain ⟨w, hW⟩ := comp T.COMP o (ordF fz) nil regNil
  have wb : ∀ x, E b x w ↔ Ord E c x := fun x => (hW x).1
  have rich : ∀ x, Ord E c x → Ord E b x := fun x ox => ord_flip T dne o.symm (poor x ox) ox
  have w_ord : Ord E b w :=
    ⟨fun y z zy yw => (wb z).mpr
        (member_ord ((wb y).mp yw) (move b c (poor y ((wb y).mp yw)) zy)),
     fun y yw => o_tr (rich y ((wb y).mp yw)),
     fun y yw => not_self (rich y ((wb y).mp yw)),
     fun y yw => sing_reg T o (poor y ((wb y).mp yw)),
     fun y z yw zw => compare T dne o (poor y ((wb y).mp yw)) (poor z ((wb z).mp zw))
        (rich y ((wb y).mp yw)) (rich z ((wb z).mp zw)),
     fun _ x xw nxk => self_wf dne (rich x ((wb x).mp xw)) nxk⟩
  exact ⟨rich, fun _ y ox => o_irr ox y, w, wb, fun x => (hW x).2, w_ord⟩

/-- Cut: an irregular ordinal p contains every regular ordinal t whose members
are regular. -/
theorem cut (o : Opp s c) (op : Ord E s p) (np : ¬ Regular E p) (rt : Regular E t)
    (ot : Ord E s t) (tpure : ∀ y, E s y t → Regular E y) : E s t p := by
  have inside : ∀ z, Regular E z → Ord E s z → (∀ x, E s x z → E s x p) → E s z p :=
    fun z rz oz zp => by
      rcases seg T dne o op rz (o_tr oz) zp with e | h
      · exact absurd (e ▸ rz) np
      · exact h
  exact inside t rt ot fun x xt => dne _ fun nxp => by
    obtain ⟨z, zx, nzp, zp⟩ := o_wf ot p x xt nxp
    have zt := down ot xt zx
    exact nzp (inside z (tpure z zt) (member_ord ot zt) zp)

/-- Descent: below an irregular ordinal there is one whose members are regular. -/
theorem descent (o : Opp s c) (oα : Ord E s α) (nα : ¬ Regular E α) :
    ∃ p : M, Ord E s p ∧ ¬ Regular E p ∧ ∀ y, E s y p → Regular E y := by
  -- D := {x | x has a singleton}; its s-face: has a c-singleton.
  obtain ⟨D, hD⟩ := comp T.COMP o (singF fz) nil regNil
  refine dne _ fun none => ?_
  have impure : ∃ x, E s x α ∧ ¬ Regular E x := dne _ fun nx =>
    none ⟨α, oα, nα, fun y yα => dne _ fun ny => nx ⟨y, yα, ny⟩⟩
  obtain ⟨x, xα, nx⟩ := impure
  obtain ⟨z, zx, nzD, zD⟩ := o_wf oα D x xα fun xD =>
    nx (sing_sing T o (o_ms oα x xα) ((hD x).1.mp xD))
  have zα := down oα xα zx
  exact none ⟨z, member_ord oα zα,
    fun rz => nzD ((hD z).1.mpr (sing_reg T o.symm rz)),
    fun y yz => sing_sing T o (o_ms oα y (o_tr oα z y yz zα)) ((hD y).1.mp (zD y yz))⟩

/-- Proposition 2: the two sides do not both have irregular ordinals.  By
descent, take p and q whose members are regular; by cut, F_∈(p) = F_ε(q), so ME
identifies them and p is regular. -/
theorem both (oa : Ord E .mem a) (na : ¬ Regular E a) (oa' : Ord E .eps a')
    (na' : ¬ Regular E a') : False := by
  obtain ⟨p, op, np, pp⟩ := descent T dne .me oa na
  obtain ⟨q, oq, nq, pq⟩ := descent T dne .em oa' na'
  have face : ∀ x, E .mem x p ↔ E .eps x q := fun x =>
    ⟨fun xp => cut T dne .em oq nq (pp x xp) (ord_flip T dne .me (pp x xp) (member_ord op xp))
        fun y yx => pp y (o_tr op x y (move .eps .mem (pp x xp) yx) xp),
     fun xq => cut T dne .me op np (pq x xq) (ord_flip T dne .em (pq x xq) (member_ord oq xq))
        fun y yx => pq y (o_tr oq x y (move .mem .eps (pq x xq) yx) xq)⟩
  have e : p = q := T.ME p q face
  subst e
  exact np face

/-- By Proposition 1 and the diagonal, each side has an irregular ordinal. -/
theorem irregular (o : Opp b c) : ∃ a : M, Ord E c a ∧ ¬ Regular E a :=
  dne _ fun none => diagonal_core T.COMP (ordF fz) nil regNil o
    (one T dne o fun x ox => dne _ fun nx => none ⟨x, ox, nx⟩)

/-- Theorem 2: irregular ordinals on both sides contradict Proposition 2. -/
theorem refutation : False := by
  obtain ⟨a, oa, na⟩ := irregular T dne Opp.em
  obtain ⟨a', oa', na'⟩ := irregular T dne Opp.me
  exact both T dne oa na oa' na'

end WithDNE
end WithT
end Proof

/-! ## Part III. The theorems (statements are part of the trusted part) -/

/-- Comprehension alone refutes every asymmetric formula.
No ME and no classical logic. -/
theorem diagonal (M : Type) (E : Side → M → M → Prop) (C : Comp M E)
    {k : Nat} (P : Fm (k + 1)) (ρ : Fin k → M)
    (rρ : ∀ i : Fin k, Regular E (ρ i))
    {b c : Side} (o : Opp b c) : ¬ Asymmetric E P ρ b c :=
  diagonal_core C P ρ rρ o

/-- Classical ME + COMP (DEST without REG) has no model.
Classical logic is the explicit hypothesis `dne`. -/
theorem inconsistent (M : Type) (E : Side → M → M → Prop)
    (dne : ∀ P : Prop, ¬¬P → P) (T : DESTminus M E) : False :=
  refutation T dne

/-- Full DEST has no model. -/
theorem DEST_inconsistent (M : Type) (E : Side → M → M → Prop)
    (dne : ∀ P : Prop, ¬¬P → P) (T : DEST M E) : False :=
  inconsistent M E dne T.core

/-- Versions using Lean's built-in classical logic instead of `dne`. -/
theorem inconsistent' (M : Type) (E : Side → M → M → Prop) (T : DESTminus M E) : False :=
  inconsistent M E (fun _ => Classical.byContradiction) T

theorem DEST_inconsistent' (M : Type) (E : Side → M → M → Prop) (T : DEST M E) : False :=
  DEST_inconsistent M E (fun _ => Classical.byContradiction) T

end DEST

#print axioms DEST.diagonal
#print axioms DEST.inconsistent
#print axioms DEST.DEST_inconsistent
#print axioms DEST.inconsistent'
#print axioms DEST.DEST_inconsistent'
