/-
Probes (brief §5).  Not imported by the main theorem.

They show that the formalization has no shortcut to a contradiction that
Holmes's system lacks: the regular-parameter gate and the crossed direction
of COMP both matter, and the Russell instance alone is satisfiable.
-/
import DESTInconsistency

namespace DEST.Probes
open DEST

variable {M : Type} {E : Side → M → M → Prop}

/-- Russell's formula ¬(x ∈ x), in context [x]. -/
def russellF : Fm 1 := .not (.mem fz fz)

/-- The single COMP instance for the Russell formula (no parameters). -/
def RussellInst (M : Type) (E : Side → M → M → Prop) : Prop :=
  ∃ A : M, ∀ x : M,
    (E .eps x A ↔ Sat E .mem russellF (cons x nil)) ∧ (E .mem x A ↔ Sat E .eps russellF (cons x nil))

theorem russell_of_comp (T : DESTminus M E) : RussellInst M E := T.COMP russellF nil regNil

/-! ### Probe 1.  Russell instance + ME: only "the witness is irregular". -/

/-- Constructively (no `dne`, no axioms): the Russell object is irregular. -/
theorem russell_irregular (_ : ∀ a b : M, (∀ x, E .mem x a ↔ E .eps x b) → a = b)
    (R : RussellInst M E) : ∃ A : M, ¬ Regular E A := by
  obtain ⟨A, hA⟩ := R
  refine ⟨A, fun rA => ?_⟩
  -- A ∈ A ↔ ¬ A ε A  and  A ∈ A ↔ A ε A
  have h1 : E .mem A A ↔ ¬ E .eps A A := (hA A).2
  have h2 : E .mem A A ↔ E .eps A A := rA A
  have n : ¬ E .eps A A := fun e => h1.mp (h2.mpr e) e
  exact n (h2.mp (h1.mpr n))

/-- A one-point structure: ∈ always true, ε always false. -/
def oneE : Side → Unit → Unit → Prop
  | .mem, _, _ => True
  | .eps, _, _ => False

theorem one_ME : ∀ a b : Unit, (∀ x, oneE .mem x a ↔ oneE .eps x b) → a = b :=
  fun _ _ _ => rfl

theorem one_russell : RussellInst Unit oneE :=
  ⟨(), fun _ => ⟨⟨False.elim, fun h => h trivial⟩, ⟨fun _ h => h, fun _ => trivial⟩⟩⟩

/-- So ME + the Russell instance alone do not yield `False`. -/
theorem russell_consistent :
    ∃ (M : Type) (E : Side → M → M → Prop),
      (∀ a b : M, (∀ x, E .mem x a ↔ E .eps x b) → a = b) ∧ RussellInst M E :=
  ⟨Unit, oneE, one_ME, one_russell⟩

/-! ### Probe 2.  COMP without the regular-parameter gate + ME is inconsistent. -/

def LooseCOMP (M : Type) (E : Side → M → M → Prop) : Prop :=
  ∀ {k : Nat} (φ : Fm (k + 1)) (ρ : Fin k → M),
    ∃ A : M, ∀ x : M,
      (E .eps x A ↔ Sat E .mem φ (cons x ρ)) ∧ (E .mem x A ↔ Sat E .eps φ (cons x ρ))

/-- Holmes p. 3: A* = {x | x ∈ A} makes every A regular; the Russell object is not. -/
theorem loose_inconsistent
    (ME : ∀ a b : M, (∀ x, E .mem x a ↔ E .eps x b) → a = b) (C : LooseCOMP M E) : False := by
  have all_reg : ∀ a : M, Regular E a := fun a => by
    obtain ⟨A, hA⟩ := C (.mem fz (fs fz)) (cons a nil)
    -- x ε A ↔ x ∈ a, so ME gives a = A
    have e : a = A := ME a A fun x => (hA x).1.symm
    subst e
    exact fun x => (hA x).1.symm
  obtain ⟨R, hR⟩ := russell_irregular ME (C russellF nil)
  exact hR (all_reg R)

/-! ### Probe 3.  Same-side COMP is inconsistent by itself (no ME). -/

def SameCOMP (M : Type) (E : Side → M → M → Prop) : Prop :=
  ∀ {k : Nat} (φ : Fm (k + 1)) (ρ : Fin k → M), (∀ i : Fin k, Regular E (ρ i)) →
    ∃ A : M, ∀ x : M,
      (E .mem x A ↔ Sat E .mem φ (cons x ρ)) ∧ (E .eps x A ↔ Sat E .eps φ (cons x ρ))

theorem same_inconsistent (C : SameCOMP M E) : False := by
  obtain ⟨R, hR⟩ := C russellF nil regNil
  have h : E .mem R R ↔ ¬ E .mem R R := (hR R).1
  have n : ¬ E .mem R R := fun r => h.mp r r
  exact n (h.mpr n)

end DEST.Probes

#print axioms DEST.Probes.russell_irregular
#print axioms DEST.Probes.russell_consistent
#print axioms DEST.Probes.loose_inconsistent
#print axioms DEST.Probes.same_inconsistent
