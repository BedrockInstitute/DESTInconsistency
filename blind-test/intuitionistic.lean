/-
  Weak double extension set theory without REG, DEST⁻ = ME + COMP,
  is inconsistent, in intuitionistic logic.

  Lean 4 core only (no Mathlib).  No `Classical`, no `propext`,
  no `Quot.sound`, no `sorry`; see the `#print axioms` at the end.

  Part 1 (lines marked TRUSTED) is the theory of Part A, Section 1,
  together with the definition of "asymmetric" from Part A, Section 2.
  Part 2 is the proof, following Part B (M1-M6) and Part A, Section 3.
  Part 3 states the two theorems.
-/

universe u

namespace DEST

/-! ════════════════ Part 1. TRUSTED definitions ════════════════ -/

/-- The two sides: `inn` is the relation ∈, `eps` is the relation ε. -/
inductive Side where
  | inn
  | eps

/-- The other side, s̄. -/
def Side.op : Side → Side
  | .inn => .eps
  | .eps => .inn

/-- A structure for the language: objects with two membership relations. -/
structure Str where
  U   : Type u
  inn : U → U → Prop   -- x ∈ y
  eps : U → U → Prop   -- x ε y

/-- `M.mem s x y` is `x ∈_s y`. -/
def Str.mem (M : Str.{u}) : Side → M.U → M.U → Prop
  | .inn => M.inn
  | .eps => M.eps

/-- Variables of a context of `n` variables (de Bruijn indices):
    `Var 0` is empty, `Var (n+1) = Option (Var n)`; `none` is the innermost
    variable and `some i` is the variable `i` of the outer context. -/
def Var : Nat → Type
  | 0 => Empty
  | n+1 => Option (Var n)

/-- Uniform formulas in a context of `n` variables: `=` and the single
    membership symbol `∈` (constructor `mem`). -/
inductive Fml : Nat → Type where
  | mem : Var n → Var n → Fml n
  | eq  : Var n → Var n → Fml n
  | fal : Fml n
  | imp : Fml n → Fml n → Fml n
  | and : Fml n → Fml n → Fml n
  | or  : Fml n → Fml n → Fml n
  | all : Fml (n+1) → Fml n
  | ex  : Fml (n+1) → Fml n

/-- Extend an assignment `ρ` by the value `x` for the new variable `vz`. -/
def cons {α : Type u} {n : Nat} (x : α) (ρ : Var n → α) : Var (n+1) → α :=
  fun (i : Option (Var n)) => match i with
    | none => x
    | some j => ρ j

/-- The s-reading `φ^s` under the assignment `ρ`: the symbol ∈ is read as ∈_s. -/
def Fml.eval (M : Str.{u}) (s : Side) : {n : Nat} → Fml n → (Var n → M.U) → Prop
  | _, .mem i j, ρ => M.mem s (ρ i) (ρ j)
  | _, .eq i j,  ρ => ρ i = ρ j
  | _, .fal,     _ => False
  | _, .imp φ ψ, ρ => φ.eval M s ρ → ψ.eval M s ρ
  | _, .and φ ψ, ρ => φ.eval M s ρ ∧ ψ.eval M s ρ
  | _, .or φ ψ,  ρ => φ.eval M s ρ ∨ ψ.eval M s ρ
  | _, .all φ,   ρ => ∀ x, φ.eval M s (cons x ρ)
  | _, .ex φ,    ρ => ∃ x, φ.eval M s (cons x ρ)

/-- `a` is regular: F_∈(a) = F_ε(a). -/
def Reg (M : Str.{u}) (a : M.U) : Prop := ∀ x, M.inn x a ↔ M.eps x a

/-- ME (mixed extensionality): if F_∈(x) = F_ε(y) then x = y. -/
def ME (M : Str.{u}) : Prop := ∀ x y : M.U, (∀ z, M.inn z x ↔ M.eps z y) → x = y

/-- COMP (crossed comprehension): for every uniform formula φ(x) (x is `vz`)
    whose parameters `ρ` are all regular, there is A with
    F_ε(A) = {x : φ^∈(x)} and F_∈(A) = {x : φ^ε(x)}. -/
def COMP (M : Str.{u}) : Prop :=
  ∀ (n : Nat) (φ : Fml (n+1)) (ρ : Var n → M.U), (∀ i, Reg M (ρ i)) →
    ∃ A : M.U, ∀ x, (M.eps x A ↔ φ.eval M .inn (cons x ρ)) ∧
                    (M.inn x A ↔ φ.eval M .eps (cons x ρ))

/-- The uniform formula P(x) with parameters ρ is asymmetric from c to b = c̄. -/
def Asym (M : Str.{u}) {n : Nat} (P : Fml (n+1)) (ρ : Var n → M.U) (c : Side) : Prop :=
  -- (i)   P^c(x) implies P^b(x)
  (∀ x, P.eval M c (cons x ρ) → P.eval M c.op (cons x ρ)) ∧
  -- (ii)  if P^b(x), then no b-member y of x has y ∈_b y
  (∀ x, P.eval M c.op (cons x ρ) → ∀ y, M.mem c.op y x → ¬ M.mem c.op y y) ∧
  -- (iii) some W with F_b(W) = {x : P^c(x)} and F_c(W) = {x : P^b(x)} has P^b(W)
  (∃ W, (∀ x, M.mem c.op x W ↔ P.eval M c (cons x ρ)) ∧
        (∀ x, M.mem c x W ↔ P.eval M c.op (cons x ρ)) ∧
        P.eval M c.op (cons W ρ))

/-! ════════════════ End of the trusted part ════════════════ -/

/-! ════════════════ Part 2. The proof ════════════════ -/

section Proof

variable {M : Str.{u}}

/-! ### Intuitionistic helpers -/

theorem nn_intro {p : Prop} (h : p) : ¬¬p := fun n => n h
theorem nn_map {p q : Prop} (f : p → q) (h : ¬¬p) : ¬¬q := fun n => h (fun x => n (f x))
/-- "Opening": use ¬¬p for a negative goal ¬q. -/
theorem nn_bind {p q : Prop} (h : ¬¬p) (f : p → ¬q) : ¬q := fun x => h (fun y => f y x)

theorem or_iff {a b c d : Prop} (h1 : a ↔ b) (h2 : c ↔ d) : (a ∨ c) ↔ (b ∨ d) :=
  ⟨fun h => h.elim (fun x => Or.inl (h1.1 x)) (fun x => Or.inr (h2.1 x)),
   fun h => h.elim (fun x => Or.inl (h1.2 x)) (fun x => Or.inr (h2.2 x))⟩
theorem and_iff {a b c d : Prop} (h1 : a ↔ b) (h2 : c ↔ d) : (a ∧ c) ↔ (b ∧ d) :=
  ⟨fun ⟨x, y⟩ => ⟨h1.1 x, h2.1 y⟩, fun ⟨x, y⟩ => ⟨h1.2 x, h2.2 y⟩⟩
theorem not_iff {a b : Prop} (h : a ↔ b) : ¬a ↔ ¬b :=
  ⟨fun n x => n (h.2 x), fun n x => n (h.1 x)⟩

/-! ### Syntax helpers: empty assignment, renaming -/

/-- The innermost variable and the weakening of a variable. -/
def Var.vz {n : Nat} : Var (n+1) := (none : Option (Var n))
def Var.vs {n : Nat} (i : Var n) : Var (n+1) := (some i : Option (Var n))

def nil {α : Type u} : Var 0 → α := fun (i : Empty) => i.elim

/-- Sanity check of the readings: `x ∈ y` read on side ε is `x ε y`. -/
example (x y : M.U) :
    (Fml.mem Var.vz (Var.vs Var.vz) : Fml 2).eval M .eps (cons x (cons y nil)) = M.eps x y :=
  rfl

theorem reg_nil : ∀ i : Var 0, Reg M (nil i) := fun (i : Empty) => i.elim

theorem reg_cons {n : Nat} {x : M.U} {ρ : Var n → M.U} (hx : Reg M x)
    (hρ : ∀ i, Reg M (ρ i)) : ∀ i, Reg M (cons x ρ i) :=
  fun (i : Option (Var n)) => match i with
    | none => hx
    | some i => hρ i

def Var.lift {n m : Nat} (f : Var n → Var m) : Var (n+1) → Var (m+1) :=
  fun (i : Option (Var n)) => match i with
    | none => Var.vz
    | some j => Var.vs (f j)

def Fml.rename : {n m : Nat} → (Var n → Var m) → Fml n → Fml m
  | _, _, f, .mem i j => .mem (f i) (f j)
  | _, _, f, .eq i j  => .eq (f i) (f j)
  | _, _, _, .fal     => .fal
  | _, _, f, .imp φ ψ => .imp (Fml.rename f φ) (Fml.rename f ψ)
  | _, _, f, .and φ ψ => .and (Fml.rename f φ) (Fml.rename f ψ)
  | _, _, f, .or φ ψ  => .or (Fml.rename f φ) (Fml.rename f ψ)
  | _, _, f, .all φ   => .all (Fml.rename (Var.lift f) φ)
  | _, _, f, .ex φ    => .ex (Fml.rename (Var.lift f) φ)

theorem lift_cons {α : Type u} {n m : Nat} {f : Var n → Var m} {ρ : Var m → α}
    {ρ' : Var n → α} (h : ∀ i, ρ (f i) = ρ' i) (x : α) :
    ∀ i, cons x ρ (Var.lift f i) = cons x ρ' i :=
  fun (i : Option (Var n)) => match i with
    | none => rfl
    | some i => h i

theorem eval_rename (M : Str.{u}) (s : Side) : {n m : Nat} → (φ : Fml n) →
    (f : Var n → Var m) → (ρ : Var m → M.U) → (ρ' : Var n → M.U) →
    (∀ i, ρ (f i) = ρ' i) → ((Fml.rename f φ).eval M s ρ ↔ φ.eval M s ρ')
  | _, _, .mem i j, f, ρ, ρ', h => by
      show M.mem s (ρ (f i)) (ρ (f j)) ↔ M.mem s (ρ' i) (ρ' j)
      rw [h i, h j]
  | _, _, .eq i j, f, ρ, ρ', h => by
      show ρ (f i) = ρ (f j) ↔ ρ' i = ρ' j
      rw [h i, h j]
  | _, _, .fal, _, _, _, _ => Iff.rfl
  | _, _, .imp φ ψ, f, ρ, ρ', h =>
      have h1 := eval_rename M s φ f ρ ρ' h
      have h2 := eval_rename M s ψ f ρ ρ' h
      ⟨fun g x => h2.1 (g (h1.2 x)), fun g x => h2.2 (g (h1.1 x))⟩
  | _, _, .and φ ψ, f, ρ, ρ', h =>
      and_iff (eval_rename M s φ f ρ ρ' h) (eval_rename M s ψ f ρ ρ' h)
  | _, _, .or φ ψ, f, ρ, ρ', h =>
      or_iff (eval_rename M s φ f ρ ρ' h) (eval_rename M s ψ f ρ ρ' h)
  | _, _, .all φ, f, ρ, ρ', h =>
      have hx : ∀ x, ((Fml.rename (Var.lift f) φ).eval M s (cons x ρ) ↔
          φ.eval M s (cons x ρ')) :=
        fun x => eval_rename M s φ (Var.lift f) (cons x ρ) (cons x ρ') (lift_cons h x)
      ⟨fun g x => (hx x).1 (g x), fun g x => (hx x).2 (g x)⟩
  | _, _, .ex φ, f, ρ, ρ', h =>
      have hx : ∀ x, ((Fml.rename (Var.lift f) φ).eval M s (cons x ρ) ↔
          φ.eval M s (cons x ρ')) :=
        fun x => eval_rename M s φ (Var.lift f) (cons x ρ) (cons x ρ') (lift_cons h x)
      ⟨fun ⟨x, g⟩ => ⟨x, (hx x).1 g⟩, fun ⟨x, g⟩ => ⟨x, (hx x).2 g⟩⟩

def notF {n : Nat} (φ : Fml n) : Fml n := .imp φ .fal
def nnF {n : Nat} (φ : Fml n) : Fml n := notF (notF φ)
def iffF {n : Nat} (φ ψ : Fml n) : Fml n := .and (.imp φ ψ) (.imp ψ φ)

/-! ### Sides, regularity, ME and COMP in side-generic form -/

theorem reg_any {a : M.U} (r : Reg M a) : ∀ (s t : Side) (x : M.U), M.mem s x a → M.mem t x a
  | .inn, .inn, _, h => h
  | .inn, .eps, x, h => (r x).1 h
  | .eps, .inn, x, h => (r x).2 h
  | .eps, .eps, _, h => h

theorem reg_of_sides {a : M.U} : ∀ s : Side, (∀ x, M.mem s x a ↔ M.mem s.op x a) → Reg M a
  | .inn, h => h
  | .eps, h => fun x => (h x).symm

/-- St_s(a): the s-face of a is ¬¬-stable. -/
def St (M : Str.{u}) (s : Side) (a : M.U) : Prop := ∀ x, ¬¬ M.mem s x a → M.mem s x a

theorem st_transfer {s : Side} {a : M.U} (r : Reg M a) (st : St M s a) (t : Side) : St M t a :=
  fun x h => reg_any r s t x (st x (nn_map (reg_any r t s x) h))

theorem me1 (hM : ME M) : ∀ (s : Side) (x y : M.U), (∀ z, M.mem s z x ↔ M.mem s.op z y) → x = y
  | .inn, x, y, h => hM x y h
  | .eps, x, y, h => (hM y x (fun z => (h z).symm)).symm

theorem me2 (hM : ME M) : ∀ (s : Side) (x y : M.U), (∀ z, M.mem s.op z x ↔ M.mem s z y) → x = y
  | .inn, x, y, h => (hM y x (fun z => (h z).symm)).symm
  | .eps, x, y, h => hM x y h

/-- Part A, Lemma 1: if g is regular and F_s(z) = F_s(g), then z = g. -/
theorem lemma1 (hM : ME M) {g z : M.U} (rg : Reg M g) (s : Side)
    (h : ∀ x, M.mem s x z ↔ M.mem s x g) : z = g :=
  me1 hM s z g (fun x => (h x).trans ⟨reg_any rg s s.op x, reg_any rg s.op s x⟩)

/-- COMP, side-generic: F_t(A) = {x : φ^{t̄}(x)} and F_{t̄}(A) = {x : φ^t(x)}. -/
theorem comp' (hC : COMP M) {n : Nat} (φ : Fml (n+1)) (ρ : Var n → M.U)
    (hρ : ∀ i, Reg M (ρ i)) :
    ∃ A : M.U, (∀ t x, M.mem t x A ↔ φ.eval M t.op (cons x ρ)) ∧
               (∀ t x, M.mem t.op x A ↔ φ.eval M t (cons x ρ)) :=
  match hC n φ ρ hρ with
  | ⟨A, hA⟩ =>
    ⟨A, fun t x => match t with
          | .inn => (hA x).2
          | .eps => (hA x).1,
        fun t x => match t with
          | .inn => (hA x).1
          | .eps => (hA x).2⟩

/-- V = {x | x = x}: both faces are everything. -/
theorem exists_V (hC : COMP M) : ∃ V : M.U, ∀ t x, M.mem t x V :=
  match comp' hC (.eq .vz .vz : Fml 1) nil reg_nil with
  | ⟨V, hV, _⟩ => ⟨V, fun t x => (hV t x).2 rfl⟩

/-! ### S(y) and Part A, Lemma 3 -/

/-- S^s(y): y has an s-singleton, ∃h ∀v (v ∈_s h ↔ v = y). -/
def Sg (M : Str.{u}) (s : Side) (y : M.U) : Prop :=
  ∃ h, ∀ v, (M.mem s v h → v = y) ∧ (v = y → M.mem s v h)

def sgF {n : Nat} (y : Var n) : Fml n :=
  .ex (.all (iffF (.mem .vz (.vs .vz)) (.eq .vz y.vs.vs)))

/-- Lemma 3, first half: {x | x = r} is a singleton of a regular r on both sides. -/
theorem sg_of_reg (hC : COMP M) {r : M.U} (hr : Reg M r) (s : Side) : Sg M s r :=
  match comp' hC (.eq .vz (.vs .vz) : Fml 2) (cons r nil) (reg_cons hr reg_nil) with
  | ⟨h, hh, _⟩ => ⟨h, fun v => ⟨(hh s v).1, (hh s v).2⟩⟩

/-- Lemma 3, second half: an object with singletons on both sides is regular. -/
theorem reg_of_sg (hM : ME M) (hC : COMP M) {y : M.U} {s : Side}
    (h1 : Sg M s y) (h2 : Sg M s.op y) : Reg M y := by
  obtain ⟨h, hh⟩ := h1
  obtain ⟨h', hh'⟩ := h2
  have e : h = h' := me1 hM s h h'
    (fun z => ⟨fun hz => (hh' z).2 ((hh z).1 hz), fun hz => (hh z).2 ((hh' z).1 hz)⟩)
  subst h'
  have rh : Reg M h := reg_of_sides s
    (fun z => ⟨fun hz => (hh' z).2 ((hh z).1 hz), fun hz => (hh z).2 ((hh' z).1 hz)⟩)
  -- k = {x | ∃u (x ∈ u ∧ u ∈ h)}
  obtain ⟨k, hk1, hk2⟩ := comp' hC
    (.ex (.and (.mem (.vs .vz) .vz) (.mem .vz (.vs (.vs .vz)))) : Fml 2)
    (cons h nil) (reg_cons rh reg_nil)
  have e2 : y = k := me1 hM s y k (fun x =>
    ⟨fun hx => (hk2 s x).2 ⟨y, hx, (hh y).2 rfl⟩,
     fun hx => match (hk2 s x).1 hx with
       | ⟨u, hxu, huh⟩ => Eq.mp (congrArg (M.mem s x) ((hh u).1 huh)) hxu⟩)
  subst k
  exact reg_of_sides s (fun x =>
    ⟨fun hx => match (hk1 s x).1 hx with
       | ⟨u, hxu, huh⟩ => Eq.mp (congrArg (M.mem s.op x) ((hh' u).1 huh)) hxu,
     fun hx => (hk1 s x).2 ⟨y, hx, (hh' y).2 rfl⟩⟩)

/-! ### M1. The ordinal formula κ -/

def K1 (M : Str.{u}) (s : Side) (a : M.U) : Prop :=
  ∀ y z, ¬¬ M.mem s z y → ¬¬ M.mem s y a → ¬¬ M.mem s z a
def K2 (M : Str.{u}) (s : Side) (a : M.U) : Prop :=
  ∀ y, ¬¬ M.mem s y a → K1 M s y
def K3 (M : Str.{u}) (s : Side) (a : M.U) : Prop :=
  ∀ y, ¬¬ M.mem s y a → ¬ M.mem s y y
def K4 (M : Str.{u}) (s : Side) (a : M.U) : Prop :=
  ∀ y, ¬¬ M.mem s y a → ¬¬ Sg M s y
def K5 (M : Str.{u}) (s : Side) (a : M.U) : Prop :=
  ∀ y z, ¬¬ M.mem s y a → ¬¬ M.mem s z a → ¬¬ (M.mem s y z ∨ y = z ∨ M.mem s z y)
def K6 (M : Str.{u}) (s : Side) (a : M.U) : Prop :=
  ∀ C x, ¬¬ M.mem s x a → ¬ M.mem s x C →
    ¬¬ ∃ z, (z = x ∨ M.mem s z x) ∧ ¬ M.mem s z C ∧ ∀ w, M.mem s w z → ¬¬ M.mem s w C
def K7 (M : Str.{u}) (s : Side) (a : M.U) : Prop := ¬¬ St M s a
def K8 (M : Str.{u}) (s : Side) (a : M.U) : Prop :=
  ∀ y, ¬¬ M.mem s y a → ¬¬ St M s y

/-- κ^s(a), the s-reading of κ(a). -/
def Kap (M : Str.{u}) (s : Side) (a : M.U) : Prop :=
  K1 M s a ∧ K2 M s a ∧ K3 M s a ∧ K4 M s a ∧ K5 M s a ∧ K6 M s a ∧ K7 M s a ∧ K8 M s a

/-! The formula κ(a) itself, for a variable `a`; `kapF_eval` checks that its
    s-reading is `Kap`. -/

def stF {n : Nat} (a : Var n) : Fml n := .all (.imp (nnF (.mem .vz a.vs)) (.mem .vz a.vs))
def k1F {n : Nat} (a : Var n) : Fml n :=
  .all (.all (.imp (nnF (.mem .vz (.vs .vz)))
    (.imp (nnF (.mem (.vs .vz) a.vs.vs)) (nnF (.mem .vz a.vs.vs)))))
def k2F {n : Nat} (a : Var n) : Fml n := .all (.imp (nnF (.mem .vz a.vs)) (k1F .vz))
def k3F {n : Nat} (a : Var n) : Fml n := .all (.imp (nnF (.mem .vz a.vs)) (notF (.mem .vz .vz)))
def k4F {n : Nat} (a : Var n) : Fml n := .all (.imp (nnF (.mem .vz a.vs)) (nnF (sgF .vz)))
def k5F {n : Nat} (a : Var n) : Fml n :=
  .all (.all (.imp (nnF (.mem (.vs .vz) a.vs.vs)) (.imp (nnF (.mem .vz a.vs.vs))
    (nnF (.or (.mem (.vs .vz) .vz) (.or (.eq (.vs .vz) .vz) (.mem .vz (.vs .vz))))))))
def k6F {n : Nat} (a : Var n) : Fml n :=
  .all (.all (.imp (nnF (.mem .vz a.vs.vs)) (.imp (notF (.mem .vz (.vs .vz)))
    (nnF (.ex (.and (.or (.eq .vz (.vs .vz)) (.mem .vz (.vs .vz)))
      (.and (notF (.mem .vz (.vs (.vs .vz))))
        (.all (.imp (.mem .vz (.vs .vz)) (nnF (.mem .vz (.vs (.vs (.vs .vz))))))))))))))
def k7F {n : Nat} (a : Var n) : Fml n := nnF (stF a)
def k8F {n : Nat} (a : Var n) : Fml n := .all (.imp (nnF (.mem .vz a.vs)) (nnF (stF .vz)))
def kapF {n : Nat} (a : Var n) : Fml n :=
  .and (k1F a) (.and (k2F a) (.and (k3F a) (.and (k4F a)
    (.and (k5F a) (.and (k6F a) (.and (k7F a) (k8F a)))))))

theorem kapF_eval {n : Nat} (s : Side) (a : Var n) (ρ : Var n → M.U) :
    (kapF a).eval M s ρ ↔ Kap M s (ρ a) := Iff.rfl

section Kacc
variable {s : Side} {a : M.U}
theorem Kap.k1 (h : Kap M s a) : K1 M s a := h.1
theorem Kap.k2 (h : Kap M s a) : K2 M s a := h.2.1
theorem Kap.k3 (h : Kap M s a) : K3 M s a := h.2.2.1
theorem Kap.k4 (h : Kap M s a) : K4 M s a := h.2.2.2.1
theorem Kap.k5 (h : Kap M s a) : K5 M s a := h.2.2.2.2.1
theorem Kap.k6 (h : Kap M s a) : K6 M s a := h.2.2.2.2.2.1
theorem Kap.k7 (h : Kap M s a) : K7 M s a := h.2.2.2.2.2.2.1
theorem Kap.k8 (h : Kap M s a) : K8 M s a := h.2.2.2.2.2.2.2
end Kacc

/-- M1(a) Stability: ¬¬κ^s(a) → κ^s(a). -/
theorem kap_stable {s : Side} {a : M.U} (h : ¬¬ Kap M s a) : Kap M s a :=
  ⟨fun y z h1 h2 n => h (fun k => k.k1 y z h1 h2 n),
   fun y hy u v h1 h2 n => h (fun k => k.k2 y hy u v h1 h2 n),
   fun y hy hyy => h (fun k => k.k3 y hy hyy),
   fun y hy n => h (fun k => k.k4 y hy n),
   fun y z hy hz n => h (fun k => k.k5 y z hy hz n),
   fun C x hx hxC n => h (fun k => k.k6 C x hx hxC n),
   fun n => h (fun k => k.k7 n),
   fun y hy n => h (fun k => k.k8 y hy n)⟩

/-- M1(b) Members (Lemma 4(1)): κ^s(a) ∧ ¬¬(y ∈_s a) → κ^s(y). -/
theorem kap_mem {s : Side} {a y : M.U} (k : Kap M s a) (hy : ¬¬ M.mem s y a) : Kap M s y :=
  have mA : ∀ {u}, ¬¬ M.mem s u y → ¬¬ M.mem s u a := fun hu => k.k1 y _ hu hy
  ⟨k.k2 y hy,
   fun u hu => k.k2 u (mA hu),
   fun u hu => k.k3 u (mA hu),
   fun u hu => k.k4 u (mA hu),
   fun u v hu hv => k.k5 u v (mA hu) (mA hv),
   fun C x hx hxC => k.k6 C x (mA hx) hxC,
   k.k8 y hy,
   fun u hu => k.k8 u (mA hu)⟩

/-- M1(c) Flip (Lemma 4(4) via Lemma 2 for the sentence κ(r)):
    Reg(r) ∧ κ^t(r) → κ^{t̄}(r). -/
theorem flip (hM : ME M) (hC : COMP M) {r : M.U} (hr : Reg M r) {t : Side}
    (k : Kap M t r) : Kap M t.op r := by
  obtain ⟨V, hV⟩ := exists_V hC
  -- A = {x | κ(r)}, x not free
  obtain ⟨A, hA1, hA2⟩ := comp' hC (kapF (.vs .vz) : Fml 2) (cons r nil) (reg_cons hr reg_nil)
  have e : A = V := me2 hM t A V (fun z => ⟨fun _ => hV t z, fun _ => (hA2 t z).2 k⟩)
  have hVA : M.mem t V A := by rw [e]; exact hV t V
  exact (hA1 t V).1 hVA

/-! ### M2. Lemmas 4(3), 5, 6 for κ -/

/-- Lemma 4(3), self-wf. -/
theorem self_wf {s : Side} {x C : M.U} (k : Kap M s x) (st : St M s x)
    (hxC : ¬ M.mem s x C) :
    ¬¬ ∃ z, (z = x ∨ M.mem s z x) ∧ ¬ M.mem s z C ∧ ∀ w, M.mem s w z → ¬¬ M.mem s w C := by
  intro hno
  refine hno ⟨x, Or.inl rfl, hxC, ?_⟩
  intro w hw hwC
  refine k.k6 C w (nn_intro hw) hwC ?_
  intro ⟨z', hz1, hz2, hz3⟩
  refine hno ⟨z', Or.inr ?_, hz2, hz3⟩
  cases hz1 with
  | inl e => subst e; exact hw
  | inr h => exact st z' (k.k1 w z' (nn_intro h) (nn_intro hw))

/-- Lemma 5, seg. -/
theorem seg (hM : ME M) {s : Side} {α γ : M.U} (kα : Kap M s α) (sα : St M s α)
    (rγ : Reg M γ) (sγ : St M s γ)
    (tγ : ∀ z y, M.mem s z y → M.mem s y γ → M.mem s z γ)
    (hsub : ∀ x, M.mem s x γ → M.mem s x α) : ¬¬ (γ = α ∨ M.mem s γ α) := by
  intro hn
  have hsup : ∀ x, M.mem s x α → M.mem s x γ := by
    intro x hx
    apply sγ x
    intro hxγ
    refine kα.k6 γ x (nn_intro hx) hxγ ?_
    intro ⟨z, hz1, hz2, hz3⟩
    have zα : M.mem s z α := by
      cases hz1 with
      | inl e => subst e; exact hx
      | inr h => exact sα z (kα.k1 x z (nn_intro h) (nn_intro hx))
    have zγ : ∀ w, M.mem s w z → M.mem s w γ := fun w hw => sγ w (hz3 w hw)
    refine kα.k8 z (nn_intro zα) ?_
    intro sz
    have γz : ∀ y, M.mem s y γ → M.mem s y z := by
      intro y hy
      apply sz y
      intro hyz
      refine kα.k5 y z (nn_intro (hsub y hy)) (nn_intro zα) ?_
      intro h3
      rcases h3 with h | e | h
      · exact hyz h
      · subst e; exact hz2 hy
      · exact hz2 (tγ z y h hy)
    have e : z = γ := lemma1 hM rγ s (fun w => ⟨zγ w, γz w⟩)
    subst e
    exact hn (Or.inr zα)
  have e : α = γ := lemma1 hM rγ s (fun x => ⟨hsup x, hsub x⟩)
  exact hn (Or.inl e.symm)

/-- Lemma 6, compare. -/
theorem compare (hM : ME M) (hC : COMP M) {s : Side} {α β : M.U}
    (rα : Reg M α) (rβ : Reg M β) (kα : Kap M s α) (kβ : Kap M s β)
    (sα : St M s α) (sβ : St M s β) :
    ¬¬ (M.mem s α β ∨ α = β ∨ M.mem s β α) := by
  -- γ = {x | x ∈ α ∧ x ∈ β}
  obtain ⟨γ, hγ1, hγ2⟩ := comp' hC
    (.and (.mem .vz (.vs .vz)) (.mem .vz (.vs (.vs .vz))) : Fml 3)
    (cons α (cons β nil)) (reg_cons rα (reg_cons rβ reg_nil))
  have face : ∀ x, M.mem s x γ ↔ M.mem s x α ∧ M.mem s x β := fun x =>
    ⟨fun h => match (hγ1 s x).1 h with
       | ⟨h1, h2⟩ => ⟨reg_any rα s.op s x h1, reg_any rβ s.op s x h2⟩,
     fun ⟨h1, h2⟩ => (hγ1 s x).2 ⟨reg_any rα s s.op x h1, reg_any rβ s s.op x h2⟩⟩
  have rγ : Reg M γ := reg_of_sides s (fun x =>
    ⟨fun h => (hγ2 s x).2 ((face x).1 h), fun h => (face x).2 ((hγ2 s x).1 h)⟩)
  have sγ : St M s γ := fun x h => (face x).2
    ⟨sα x (nn_map (fun h => ((face x).1 h).1) h), sβ x (nn_map (fun h => ((face x).1 h).2) h)⟩
  have tγ : ∀ z y, M.mem s z y → M.mem s y γ → M.mem s z γ := fun z y hz hy =>
    match (face y).1 hy with
    | ⟨hyα, hyβ⟩ => (face z).2
        ⟨sα z (kα.k1 y z (nn_intro hz) (nn_intro hyα)),
         sβ z (kβ.k1 y z (nn_intro hz) (nn_intro hyβ))⟩
  have g1 := seg hM kα sα rγ sγ tγ (fun x h => ((face x).1 h).1)
  have g2 := seg hM kβ sβ rγ sγ tγ (fun x h => ((face x).1 h).2)
  intro hn
  apply g1; intro c1
  apply g2; intro c2
  rcases c1 with e1 | h1 <;> rcases c2 with e2 | h2
  · exact hn (Or.inr (Or.inl (e1.symm.trans e2)))
  · subst e1; exact hn (Or.inl h2)
  · subst e2; exact hn (Or.inr (Or.inr h1))
  · exact kα.k3 γ (nn_intro h1) ((face γ).2 ⟨h1, h2⟩)

/-! ### Part A, Section 3: the diagonal (Theorem 1) -/

/-- The logical core of Theorem 1, for two abstract sides b and c. -/
theorem diag_core {U : Type u} (mb mc : U → U → Prop) (Pb Pc : U → Prop) (V W A : U)
    (hV : ∀ x, mb x V)
    (hi : ∀ x, Pc x → Pb x) (hii : ∀ x, Pb x → ∀ y, mb y x → ¬ mb y y)
    (hW1 : ∀ x, mb x W ↔ Pc x) (hW2 : ∀ x, mc x W ↔ Pb x) (hW3 : Pb W)
    (hAb : ∀ x, mb x A ↔ (x = V ∨ Pc x ∨ (mc V x ∧
        ((mc x x ∧ ¬ ∃ u, Pc u ∧ ¬ mc u x) ∨ (¬ mc x x ∧ ∃ u, Pc u ∧ ¬ mc u x)))))
    (hAc : ∀ x, mc x A ↔ (x = V ∨ Pb x ∨ (mb V x ∧
        ((mb x x ∧ ¬ ∃ u, Pb u ∧ ¬ mb u x) ∨ (¬ mb x x ∧ ∃ u, Pb u ∧ ¬ mb u x))))) :
    False := by
  -- 1.
  have nPbV : ¬ Pb V := fun h => hii V h V (hV V) (hV V)
  have nPcW : ¬ Pc W := fun h => hii W hW3 W ((hW1 W).2 h) ((hW1 W).2 h)
  -- 2.
  have WnA : ¬ mb W A := by
    intro h
    rcases (hAb W).1 h with e | h | ⟨hVW, _⟩
    · subst e; exact nPbV hW3
    · exact nPcW h
    · exact nPbV ((hW2 V).1 hVW)
  have thB : ∃ u, Pb u ∧ ¬ mb u A := ⟨W, hW3, WnA⟩
  -- 3.
  have nthC : ¬ ∃ u, Pc u ∧ ¬ mc u A := fun ⟨u, hu, hn⟩ =>
    hn ((hAc u).2 (Or.inr (Or.inl (hi u hu))))
  -- 4.
  have VbA : mb V A := (hAb V).2 (Or.inl rfl)
  have VcA : mc V A := (hAc V).2 (Or.inl rfl)
  have AneV : A ≠ V := by intro e; subst e; exact WnA (hV W)
  have nPbA : ¬ Pb A := fun h => hii A h V VbA (hV V)
  have nPcA : ¬ Pc A := fun h => nPbA (hi A h)
  -- 5.
  have e1 : mb A A ↔ mc A A := by
    constructor
    · intro h
      rcases (hAb A).1 h with e | h | ⟨_, ⟨h, _⟩ | ⟨_, th⟩⟩
      · exact absurd e AneV
      · exact absurd h nPcA
      · exact h
      · exact absurd th nthC
    · intro h
      exact (hAb A).2 (Or.inr (Or.inr ⟨VcA, Or.inl ⟨h, nthC⟩⟩))
  have e2 : mc A A ↔ ¬ mb A A := by
    constructor
    · intro h
      rcases (hAc A).1 h with e | h | ⟨_, ⟨_, nth⟩ | ⟨h, _⟩⟩
      · exact absurd e AneV
      · exact absurd h nPbA
      · exact absurd thB nth
      · exact h
    · intro h
      exact (hAc A).2 (Or.inr (Or.inr ⟨VbA, Or.inr ⟨h, thB⟩⟩))
  have nAA : ¬ mb A A := fun h => (e2.1 (e1.1 h)) h
  exact nAA (e1.2 (e2.2 nAA))

/-- Θ(z) := ∃u (P(u) ∧ u ∉ z), in the context (z, V, parameters of P). -/
def thetaF {n : Nat} (P : Fml (n+1)) : Fml (n+1+1) :=
  .ex (.and (Fml.rename (Var.lift (fun i => Var.vs (Var.vs i))) P) (notF (.mem .vz (.vs .vz))))

/-- The diagonal formula z = V ∨ P(z) ∨ V ∈ z ∧ (z ∈ z ⊕ Θ(z)),
    in the context (z, V, parameters of P). -/
def diagF {n : Nat} (P : Fml (n+1)) : Fml (n+1+1) :=
  .or (.eq .vz (.vs .vz))
    (.or (Fml.rename (Var.lift Var.vs) P)
      (.and (.mem (.vs .vz) .vz)
        (.or (.and (.mem .vz .vz) (notF (thetaF P)))
             (.and (notF (.mem .vz .vz)) (thetaF P)))))

theorem diag_eval {n : Nat} (P : Fml (n+1)) (ρ : Var n → M.U) (V z : M.U) (t : Side) :
    (diagF P).eval M t (cons z (cons V ρ)) ↔
    (z = V ∨ P.eval M t (cons z ρ) ∨ (M.mem t V z ∧
      ((M.mem t z z ∧ ¬ ∃ u, P.eval M t (cons u ρ) ∧ ¬ M.mem t u z) ∨
       (¬ M.mem t z z ∧ ∃ u, P.eval M t (cons u ρ) ∧ ¬ M.mem t u z)))) := by
  have hP : (Fml.rename (Var.lift Var.vs) P).eval M t (cons z (cons V ρ)) ↔
      P.eval M t (cons z ρ) :=
    eval_rename M t P _ _ _ (fun (i : Option (Var n)) => match i with | none => rfl | some _ => rfl)
  have hu : ∀ u, (Fml.rename (Var.lift (fun i => Var.vs (Var.vs i))) P).eval M t
      (cons u (cons z (cons V ρ))) ↔ P.eval M t (cons u ρ) := fun u =>
    eval_rename M t P _ _ _ (fun (i : Option (Var n)) => match i with | none => rfl | some _ => rfl)
  have hΘ : (thetaF P).eval M t (cons z (cons V ρ)) ↔
      ∃ u, P.eval M t (cons u ρ) ∧ ¬ M.mem t u z :=
    ⟨fun ⟨u, a, b⟩ => ⟨u, (hu u).1 a, b⟩, fun ⟨u, a, b⟩ => ⟨u, (hu u).2 a, b⟩⟩
  exact or_iff Iff.rfl (or_iff hP (and_iff Iff.rfl
    (or_iff (and_iff Iff.rfl (not_iff hΘ)) (and_iff Iff.rfl hΘ))))

/-- Theorem 1 (proof). -/
theorem theorem1_pf (hC : COMP M) {n : Nat} (P : Fml (n+1)) (ρ : Var n → M.U)
    (hρ : ∀ i, Reg M (ρ i)) (c : Side) : ¬ Asym M P ρ c := by
  intro h
  obtain ⟨hi, hii, W, hW1, hW2, hW3⟩ := h
  obtain ⟨V, hV⟩ := exists_V hC
  have rV : Reg M V := fun x => ⟨fun _ => hV .eps x, fun _ => hV .inn x⟩
  obtain ⟨A, hA1, hA2⟩ := comp' hC (diagF P) (cons V ρ) (reg_cons rV hρ)
  exact diag_core (M.mem c.op) (M.mem c)
    (fun x => P.eval M c.op (cons x ρ)) (fun x => P.eval M c (cons x ρ)) V W A
    (fun x => hV c.op x) hi hii hW1 hW2 hW3
    (fun x => (hA2 c x).trans (diag_eval P ρ V x c))
    (fun x => (hA1 c x).trans (diag_eval P ρ V x c.op))

/-! ### M3. Proposition 1 (Burali-Forti) for κ -/

theorem prop1 (hM : ME M) (hC : COMP M) (c : Side) : ¬ ∀ x, Kap M c x → ¬¬ Reg M x := by
  intro H
  -- W = {x | κ(x)}
  obtain ⟨W, hW1, hW2⟩ := comp' hC (kapF .vz : Fml 1) nil reg_nil
  have hWb : ∀ x, M.mem c.op x W ↔ Kap M c x := hW2 c
  have hWc : ∀ x, M.mem c x W ↔ Kap M c.op x := hW1 c
  -- opening a b-member of W
  have op3 : ∀ y, ¬¬ M.mem c.op y W → ¬¬ (Kap M c y ∧ Reg M y ∧ St M c y) :=
    fun y hy hn => hy (fun h =>
      H y ((hWb y).1 h) (fun ry => ((hWb y).1 h).k7 (fun sy => hn ⟨(hWb y).1 h, ry, sy⟩)))
  have kW : Kap M c.op W :=
    ⟨-- K1
     fun y z hzy hyW => nn_bind (op3 y hyW) (fun ⟨ky, ry, _⟩ =>
       nn_intro ((hWb z).2 (kap_mem ky (nn_map (reg_any ry c.op c z) hzy)))),
     -- K2
     fun y hy u v h1 h2 => nn_bind (op3 y hy) (fun ⟨ky, ry, _⟩ =>
       (flip hM hC ry ky).k1 u v h1 h2),
     -- K3
     fun y hy hyy => op3 y hy (fun ⟨ky, ry, _⟩ => (flip hM hC ry ky).k3 y (nn_intro hyy) hyy),
     -- K4
     fun y hy => nn_bind (op3 y hy) (fun ⟨_, ry, _⟩ => nn_intro (sg_of_reg hC ry c.op)),
     -- K5
     fun y z hy hz => nn_bind (op3 y hy) (fun ⟨ky, ry, sy⟩ =>
       nn_bind (op3 z hz) (fun ⟨kz, rz, sz⟩ =>
         compare hM hC ry rz (flip hM hC ry ky) (flip hM hC rz kz)
           (st_transfer ry sy c.op) (st_transfer rz sz c.op))),
     -- K6
     fun C x hx hxC => nn_bind (op3 x hx) (fun ⟨kx, rx, sx⟩ =>
       self_wf (flip hM hC rx kx) (st_transfer rx sx c.op) hxC),
     -- K7
     nn_intro (fun x hx => (hWb x).2 (kap_stable (nn_map (hWb x).1 hx))),
     -- K8
     fun y hy => nn_bind (op3 y hy) (fun ⟨_, ry, sy⟩ => nn_intro (st_transfer ry sy c.op))⟩
  exact theorem1_pf hC (kapF .vz) nil reg_nil c
    ⟨fun x kx => kap_stable (fun hn => H x kx (fun rx => hn (flip hM hC rx kx))),
     fun x kx y hy => Kap.k3 kx y (nn_intro hy),
     W, hWb, hWc, kW⟩

theorem prop1' (hM : ME M) (hC : COMP M) (c : Side) : ¬¬ ∃ a, Kap M c a ∧ ¬ Reg M a :=
  fun hn => prop1 hM hC c (fun x kx nr => hn ⟨x, kx, nr⟩)

/-! ### M4. Descent -/

theorem descent (hM : ME M) (hC : COMP M) {s : Side} {α : M.U} (kα : Kap M s α)
    (nα : ¬ Reg M α) :
    ¬¬ ∃ p, Kap M s p ∧ ¬ Reg M p ∧ ∀ y, ¬¬ M.mem s y p → ¬¬ Reg M y := by
  intro hno
  -- D = {x | ¬¬S(x)}
  obtain ⟨D, hD1, _⟩ := comp' hC (nnF (sgF .vz) : Fml 1) nil reg_nil
  have hD : ∀ x, M.mem s x D ↔ ¬¬ Sg M s.op x := hD1 s
  have regD : ∀ y, ¬¬ M.mem s y α → ¬¬ M.mem s y D → ¬¬ Reg M y := fun y hy hyD nry =>
    kα.k4 y hy (fun g1 => hyD (fun h => (hD y).1 h (fun g2 => nry (reg_of_sg hM hC g1 g2))))
  apply (fun hp => hno ⟨α, kα, nα, hp⟩ : ¬ ∀ y, ¬¬ M.mem s y α → ¬¬ Reg M y)
  intro x hx nrx
  have xD : ¬ M.mem s x D := fun h => regD x hx (nn_intro h) nrx
  refine kα.k6 D x hx xD ?_
  intro ⟨z, hz1, hz2, hz3⟩
  have zα : ¬¬ M.mem s z α := by
    cases hz1 with
    | inl e => subst e; exact hx
    | inr h => exact kα.k1 x z (nn_intro h) hx
  refine hno ⟨z, kap_mem kα zα, ?_, ?_⟩
  · intro rz
    exact hz2 ((hD z).2 (nn_intro (sg_of_reg hC rz s.op)))
  · intro y hy
    exact regD y (kα.k1 z y hy zα) (fun n => hy (fun h => hz3 y h n))

/-! ### M5. Cut and Proposition 2 -/

theorem cut (hM : ME M) {s : Side} {p t : M.U} (kp : Kap M s p) (sp : St M s p)
    (np : ¬ Reg M p) (rt : Reg M t) (kt : Kap M s t) (st : St M s t)
    (pt : ∀ y, ¬¬ M.mem s y t → ¬¬ Reg M y) : M.mem s t p := by
  have inside : ∀ z, Reg M z → Kap M s z → St M s z →
      (∀ w, M.mem s w z → M.mem s w p) → M.mem s z p := by
    intro z rz kz sz hsub
    apply sp z
    intro hzp
    refine seg hM kp sp rz sz
      (fun w y h1 h2 => sz w (kz.k1 y w (nn_intro h1) (nn_intro h2))) hsub ?_
    intro h
    cases h with
    | inl e => subst e; exact np rz
    | inr h => exact hzp h
  apply inside t rt kt st
  intro x hx
  apply sp x
  intro hxp
  refine kt.k6 p x (nn_intro hx) hxp ?_
  intro ⟨z, hz1, hz2, hz3⟩
  have zt : ¬¬ M.mem s z t := by
    cases hz1 with
    | inl e => subst e; exact nn_intro hx
    | inr h => exact kt.k1 x z (nn_intro h) (nn_intro hx)
  apply pt z zt
  intro rz
  apply kt.k8 z zt
  intro sz
  exact hz2 (inside z rz (kap_mem kt zt) sz (fun w hw => sp w (hz3 w hw)))

/-- One half of Proposition 2: F_s(p) ⊆ F_{s̄}(q). -/
theorem half (hM : ME M) (hC : COMP M) {s : Side} {p q : M.U}
    (kp : Kap M s p) (pp : ∀ y, ¬¬ M.mem s y p → ¬¬ Reg M y)
    (kq : Kap M s.op q) (sq : St M s.op q) (nq : ¬ Reg M q) :
    ∀ x, M.mem s x p → M.mem s.op x q := by
  intro x hx
  apply sq x
  intro hxq
  apply pp x (nn_intro hx)
  intro rx
  apply kp.k8 x (nn_intro hx)
  intro sx
  have kx : Kap M s x := kap_mem kp (nn_intro hx)
  exact hxq (cut hM kq sq nq rx (flip hM hC rx kx) (st_transfer rx sx s.op)
    (fun y hy => pp y (kp.k1 x y (nn_map (reg_any rx s.op s y) hy) (nn_intro hx))))

theorem prop2 (hM : ME M) (hC : COMP M) {p q : M.U}
    (kp : Kap M .inn p) (sp : St M .inn p) (np : ¬ Reg M p)
    (pp : ∀ y, ¬¬ M.mem .inn y p → ¬¬ Reg M y)
    (kq : Kap M .eps q) (sq : St M .eps q) (nq : ¬ Reg M q)
    (pq : ∀ y, ¬¬ M.mem .eps y q → ¬¬ Reg M y) : False := by
  have h1 : ∀ x, M.mem .inn x p → M.mem .eps x q := half hM hC kp pp kq sq nq
  have h2 : ∀ x, M.mem .eps x q → M.mem .inn x p := half hM hC kq pq kp sp np
  have e : p = q := hM p q (fun z => ⟨h1 z, h2 z⟩)
  subst e
  exact np (fun z => ⟨h1 z, h2 z⟩)

/-! ### M6. The main theorem -/

theorem main_pf (hM : ME M) (hC : COMP M) : False := by
  apply prop1' hM hC .inn; intro ⟨a, ka, na⟩
  apply prop1' hM hC .eps; intro ⟨a', ka', na'⟩
  apply descent hM hC ka na; intro ⟨p, kp, np, pp⟩
  apply descent hM hC ka' na'; intro ⟨q, kq, nq, pq⟩
  apply kp.k7; intro sp
  apply kq.k7; intro sq
  exact prop2 hM hC kp sp np pp kq sq nq pq

end Proof

/-! ════════════════ Part 3. The theorems ════════════════ -/

/-- Theorem 1 (Part A): under COMP, no uniform formula with regular parameters is
    asymmetric (from either side to the other). -/
theorem Theorem1 (M : Str.{u}) (hC : COMP M) {n : Nat} (P : Fml (n+1))
    (ρ : Var n → M.U) (hρ : ∀ i, Reg M (ρ i)) (c : Side) : ¬ Asym M P ρ c :=
  theorem1_pf hC P ρ hρ c

/-- Main theorem: every structure satisfying ME and COMP is contradictory. -/
theorem DESTminus_inconsistent : ∀ M : Str.{u}, ME M → COMP M → False :=
  fun _ hM hC => main_pf hM hC

end DEST

#print axioms DEST.Theorem1
#print axioms DEST.DESTminus_inconsistent
