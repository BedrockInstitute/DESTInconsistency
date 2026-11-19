# Input for an independent Lean 4 formalization

Part A is the published paper "Weak double extension set theory is inconsistent", Sections 1–5 (plain text extracted from the PDF). It proves the theory DEST⁻ = ME + COMP inconsistent in classical logic.

Part B is a new proof, written in Chinese, that DEST⁻ is inconsistent in intuitionistic logic. It reuses the paper's Theorem 1 (the diagonal argument, already intuitionistic) and the paper's lemmas in ¬¬-form, with a new ordinal formula κ. Notation follows Part A: F_s(a) is the s-face, Reg / 正则 means regular, St_s(a) means "the s-face of a is ¬¬-stable", i.e. ∀x(¬¬ x ∈_s a → x ∈_s a), S(y) means "y has a singleton", 打开 ("opening") means using ¬¬A together with A → G for a negative goal G.

================ PART A ================

               Weak double extension set theory is inconsistent
                                           Bedrock Institute*

                                             November 2026


                                                 Abstract
            We prove that Kisielewicz’s weak double extension set theory DEST is inconsistent:
        already two of its axioms, mixed extensionality and comprehension, contradict each other.
        DEST has two membership relations, ∈ and ε; it interprets ZF, and its consistency was an
        open problem.
            Holmes showed, using the regularity axiom, that the ordinals of the two relations differ:
        with the relations suitably named, every ε-ordinal is an ∈-ordinal, and the object Ord =
        {x | x is an ordinal} is an ∈-ordinal but not an ε-ordinal. We show first that comprehension
        alone refutes such an asymmetry, in intuitionistic logic. Assume this asymmetry. If V is
        the universal set and Θ(z) says that z omits some ordinal, then the object
                                                         (                       )
                          A = { z | z = V ∨ ord(z) ∨ V ∈ z ∧ (z ∈ z ⊕ Θ(z)) }
        satisfies A ∈ A ↔ A ∈ / A, and the same argument refutes every formula that is asymmetric
        in this way. We then derive the asymmetry of the ordinals, up to exchanging the two
        relations, from mixed extensionality and comprehension without the regularity axiom; this


1      The theory
Language. First-order logic with = and two membership relations ∈ and ε. For a side s (one
     of ∈, ε) we write x ∈s y, let s̄ be the other side, and call Fs (a) = {x : x ∈s a} the s-face
     of a. An object a is regular if F∈ (a) = Fε (a).
Uniform formulas. A formula is uniform if its only membership symbol is ∈. Its s-reading
     φs interprets that symbol as ∈s . Thus φ∈ = φ, and φε is what Holmes calls the dual of
     φ.
ME (mixed extensionality). If F∈ (x) = Fε (y), then x = y.
COMP (comprehension). For every uniform formula φ(x) whose parameters are all regular
     there is A = {x | φ} with
                               Fε (A) = {x : φ∈ (x)},       F∈ (A) = {x : φε (x)},
   that is, Fs (A) = {x : φs̄ (x)} for both sides s: the s-face of A is given by the s̄-reading of
   φ. Comprehension is thus crossed. We write {x | · · · } for objects given by COMP and
   {x : · · · } for classes, such as faces.
REG (regularity). If one face of x is included in the same face of some y whose members on
   both sides are all regular, then x is regular.
DEST is ME + COMP + REG [H05, §2], [HFL, §8.1]. DEST− is ME + COMP.


∗
    Corresponding author: Peter Zhang, peterzhangsg@gmail.com
    © 2026 Bedrock Institute. Licensed under CC BY-NC-SA 4.0.


                                                      1
On the formulation. In [H05], Axiom 2.8 places “there is {x | φ}” before the quantifier over
the parameters. We read it, as Holmes does in his proofs, as “for all regular parameters there
is A”; read literally, the axiom is already inconsistent. Kisielewicz [K98], weakening his theory
of [K89], folds REG into COMP through a condition on parameters: they must be partially
contained in a suitable regular object, where x is partially contained in y if Fs (x) ⊆ Fs (y) for
some side s.† Holmes [H04, §2] states that this is equivalent to the formulation above, which
is the one recorded as open in [HFL, §8.1] and [SEP, §10].


2       Asymmetry and the results
Being an ordinal is expressed by a parameter-free uniform formula ord. Holmes’s definition
[H05, §5] has the clause β ε S, where the parameter S is {x | x has a singleton}; replacing that
clause by “β has a singleton” gives such a formula, and Section 4 gives a variant. Using REG,
Holmes showed that, with the relations suitably named, every ε-ordinal is an ∈-ordinal, and
that the object Ord = {x | ord(x)} is an ∈-ordinal but not an ε-ordinal [H05, Theorem 5.1 and
the discussion after it]. So Ord is an ordinal on one side only. We isolate what is needed.
be the two sides. P is asymmetric from c to b if
      (i) P c (x) implies P b (x);
     (ii) if P b (x), then no b-member y of x has y ∈b y;
    (iii) some W with Fb (W ) = {x : P c (x)} and Fc (W ) = {x : P b (x)} has P b (W ).
By COMP, objects W as in (iii) exist; (iii) asks that one of them satisfy P b . With this naming,
Holmes’s ordinal formula is asymmetric from ε to ∈: (i) and (iii) are his two facts, and (ii)
holds because no ordinal has a self-membered member.
neither ME nor classical logic.
Theorem 1 and the asymmetry of the ordinals together give a contradiction. The asymmetry
can be proved in two ways, and either one suﬀices. First, Holmes’s two facts, proved with
REG, provide it, so Theorem 1 already refutes full DEST. Second, the proof of Theorem 2 does
without REG: ME and COMP alone make the ordinals asymmetric from one side to the other,
and Theorem 1 gives the contradiction. The rest of the paper is arranged as follows. Section 3
proves Theorem 1; Section 4 collects facts about regular objects and ordinals; Section 5 derives
from them the asymmetry of the ordinals and completes the proof of Theorem 2.


3       Comprehension refutes asymmetry
We prove Theorem 1. Let P be asymmetric from c to b, with W as in (iii). Let V = {x | x = x}.
Both faces of V are everything, so V is regular and V ∈s V . Let Θ(z) be ∃u (P (u) ∧ u ∈/ z),
and let                                        (                      )
                   A = { z | z = V ∨ P (z) ∨ V ∈ z ∧ (z ∈ z ⊕ Θ(z)) },


†
    If the condition asks for a regular object with regular members, it matters which parameters the proofs
    use. The proof of Theorem 2 uses only parameters that are regular objects with regular members, with two
    exceptions. One is the universal set V , which can be eliminated: replace z = V by ∀y (y ∈ z) and V ∈ z by
    ∃v (∀y (y ∈ v) ∧ v ∈ z); by ME, V is the only object whose s-face is everything. The other is the object h in
    the proof of Lemma 3, which is regular but need not have regular members; at this one point the proof relies
    on Holmes’s equivalence.


                                                        2
with parameters V and those of P , where ⊕ is exclusive or: z ∈ z ⊕ Θ(z) stands for
(z ∈ z ∧ ¬Θ(z)) ∨ (z ∈/ z ∧ Θ(z)). So z ∈b A iff the c-reading of the condition holds at z, and
z ∈c A iff the b-reading does.
    1. P b (V ) fails by (ii), since V ∈b V ∈b V . P c (W ) fails: otherwise W ∈b W by (iii), against
       (ii) for W .
    2. Θb (A) holds, because W ∈      / b A. Each disjunct fails in the c-reading at W : W ̸= V , since
       P b (W ) and not P b (V ); P c (W ) fails; and V ∈c W would give P b (V ) by (iii).
    3. Θc (A) fails. If P c (u), then P b (u) by (i), so u ∈c A.
    4. At z = A only the last disjunct can hold. V ∈b A and V ∈c A by the first disjunct.
       A ̸= V , since W ∈b V and W ∈       / b A. P b (A) fails by (ii), since V ∈b A and V ∈b V ; so
         c
       P (A) fails by (i).
    5. Hence A ∈b A ↔ A ∈c A and A ∈c A ↔ A ∈             / b A. If A ∈b A, the two give A ∈ / b A; so
       A∈  / b A. Then A ∈c A, and then A ∈b A, a contradiction.
No step uses ME or classical logic.
Remark (Why the diagonal works). Russell’s instance R = {x | x ∈
                                                               / x} gives

                             RεR↔R∈
                                  / R,                 R ∈ R ↔ ¬(R ε R).

Together they give R ∈ R ↔ ¬¬(R ∈ R), which is no contradiction: both equivalences hold
when exactly one of R ∈ R and R ε R is true, so R is merely irregular. For the diagonal
object A, Θb (A) holds and Θc (A) fails, which leaves a single negation: A ∈b A ↔ A ∈c A and
A ∈c A ↔ A ∈  / b A give A ∈b A ↔ A ∈
                                    / b A.


4     Regular objects and ordinals
This section and the next prove Theorem 2; they are the only places that use ME and classical
logic. Three facts about regular objects come first.


Proof. Fs (z) = Fs (g) = Fs̄ (g), so z = g by ME.

parameters. Then σ ∈ ↔ σ ε . In particular, the two readings of a uniform formula with regular
parameters agree at every regular object.

Proof. Let V = {x | x = x} and A = {x | σ}, where x does not occur in σ. Suppose σ s̄ . Then
Fs (A) is everything, which is Fs̄ (V ); so A = V by ME. Hence Fs̄ (A) is everything too, and this
face is nonempty only if σ s .

{y}. Every regular object has singletons on both sides, and every object with singletons on both
sides is regular.

Proof. For the first claim, take {x | x = r} for regular r. For the second, let h be an s-singleton
of y and h′ an s̄-singleton of y. ME gives h = h′ (in one order or the other), so both faces of h
are {y} and h is regular. Let k = {x | ∃u (x ∈ u ∧ u ∈ h)}. Then Fs̄ (k) = Fs (y), so y = k by
ME, and therefore Fs̄ (y) = Fs̄ (k) = Fs (y).

junction of:
 (O1) z ∈ y ∧ y ∈ a → z ∈ a;

                                                   3
 (O2) every member of a satisfies (O1);
 (O3) no member of a is a member of itself;
 (O4) every member y of a has a singleton, i.e. ∃h ∀v (v ∈ h ↔ v = y);
 (O5) for members y, z of a: y ∈ z ∨ y = z ∨ z ∈ y;
 (O6) for every C and every x ∈ a with x ∈/ C, there is z with z = x or z ∈ x, such that z ∈
                                                                                           /C
      and every member of z is in C.
An s-ordinal is an object satisfying ords . In ZF this defines the von Neumann ordinals.
 (1) The s-members of an s-ordinal are s-ordinals.
 (2) No s-ordinal is an s-member of itself.
 (3) If x is an s-ordinal and x ∈ / s C, there is z with z = x or z ∈s x, such that z ∈
                                                                                      / s C and
     Fs (z) ⊆ Fs (C).
 (4) A regular s-ordinal is an s̄-ordinal.
Proof. (1) Let y be a member of a. By (O1) of a, the members of y are members of a; so
(O1) for y is (O2) of a, and (O2)–(O6) for y follow from those of a. (2) By (O3). (3) If
Fs (x) ⊆ Fs (C), take z = x. Otherwise apply (O6) of x to a member of x that is not in C, and
use (O1) of x. (4) By Lemma 2.

Fs (γ) ⊆ Fs (α) such that z ∈s y ∈s γ implies z ∈s γ. Then γ = α or γ ∈s α.
Proof. If Fs (α) ⊆ Fs (γ), then γ = α by Lemma 1. Otherwise pick x ∈s α with x ∈      / s γ, and
apply (O6) of α with C = γ. This gives z ∈s α with z ∈ / s γ and Fs (z) ⊆ Fs (γ). Conversely, let
y ∈s γ. Then y ∈s α, so by (O5) y ∈s z, or y = z, or z ∈s y; the last two would put z in γ. So
Fs (z) = Fs (γ), hence z = γ by Lemma 1, and γ ∈s α.

β ∈s α.
Proof. Let γ = {x | x ∈ α ∧ x ∈ β}. Its s-face and s̄-face are Fs̄ (α) ∩ Fs̄ (β) and Fs (α) ∩ Fs (β),
which are equal because α and β are regular. So γ is regular, and it satisfies the condition
of Lemma 5 by (O1) of α and β. By Lemma 5, γ = α or γ ∈s α, and γ = β or γ ∈s β. If
γ ∈s α and γ ∈s β, then γ ∈s γ, against (O3) for α. The three remaining combinations give
the claim.


5    The ordinals are asymmetric
Theorem 2 follows from Theorem 1 and two propositions.
ord is asymmetric from c to c̄.
Proof. Let b = c̄.
  (i) A c-ordinal is regular, hence a b-ordinal by Lemma 4(4).
 (ii) This is (O3).
(iii) Let W = {x | ord(x)}, so Fb (W ) is the class of c-ordinals and Fc (W ) the class of b-
      ordinals. Then W is a b-ordinal. Its b-members are regular c-ordinals, hence regular
      b-ordinals. Clause by clause:
        • (O1): if z ∈b y ∈b W , then z ∈c y since y is regular; so z is a c-ordinal by Lemma 4(1),
          and z ∈b W ;

                                                 4
        • (O2), (O3): the members are b-ordinals; use Lemma 4(2);
        • (O4): Lemma 3;
        • (O5): Lemma 6;
        • (O6): apply Lemma 4(3) to the member x.

have irregular ordinals.

Proof. Suppose they do.
  1. Cut. If p is an irregular s-ordinal and t a regular s-ordinal whose s-members are regular,
     then t ∈s p. Indeed, a regular s-ordinal z with Fs (z) ⊆ Fs (p) satisfies z = p or z ∈s p
     by Lemma 5 (its condition is (O1) of z), and z = p would make p regular; so z ∈s p. If
     some x ∈s t is not in p, apply (O6) of t with C = p. This gives z ∈s t with z ∈    / s p and
     Fs (z) ⊆ Fs (p), where z is a regular s-ordinal, which is impossible. So Fs (t) ⊆ Fs (p), and
     t ∈s p.
  2. Descent. If there is an irregular s-ordinal α, then there is an irregular s-ordinal p whose
     s-members are all regular.
        • Let D = {x | x has a singleton}. Then Fs (D) is the class of objects with an s̄-
          singleton.
        • The s-members of α have s-singletons by (O4). So, by Lemma 3, an s-member of α
          lies in Fs (D) iff it is regular.
        • If all s-members of α are regular, take p = α. Otherwise some irregular x ∈s α
          satisfies x ∈/ s D. Apply (O6) of α with C = D to get z ∈s α with z ∈ / s D and
          Fs (z) ⊆ Fs (D).
        • The s-members of z are in α and in D, hence regular. And z is irregular, since
          otherwise z ∈s D. By Lemma 4(1), z is an s-ordinal; take p = z.
  3. Conclusion. By Descent, take such a p on side ∈ and such a q on side ε.
        • Each ∈-member x of p is a regular ∈-ordinal, hence an ε-ordinal by Lemma 4(4).
          Its members on either side are its ∈-members, since x is regular; these lie in p by
          (O1), so they are regular. By Cut, x ε q.
        • Symmetrically, every ε-member of q is an ∈-member of p.
        • So F∈ (p) = Fε (q), and p = q by ME. Then Fε (p) = F∈ (p), so p is regular, a
          contradiction.

Proof of Theorem 2. By Proposition 2 and classical logic, some side c has only regular ordinals.
By Proposition 1, ord is asymmetric from c to c̄, which contradicts Theorem 1.

Remark (The instances of COMP used). The proof of Theorem 2 uses only eight instances
of COMP, so ME together with these eight instances is already inconsistent in classical logic.
Here they are, with the object each one gives and where it is used:
  • x = x: the universal set V , in Section 3 and the proof of Lemma 2;
  • x = r with r regular: a singleton of r, in the proof of Lemma 3;
  • ∃u (x ∈ u ∧ u ∈ h): the object k in the proof of Lemma 3;
  • ord(r), with x not free: the object A in the proof of Lemma 2, as used for Lemma 4(4);
  • x ∈ α ∧ x ∈ β: the object γ in the proof of Lemma 6;
  • “x has a singleton”: the object D in the proof of Proposition 2;
  • ord(x): the object W in the proof of Proposition 1;
  • the diagonal formula of Section 3 for P = ord, with parameter V : the object A there.


                                               5
Each has at most two parameters and quantifier rank at most 5, so the contradiction already
lies in a small fragment of comprehension. Section 7 says what this means for the search for
models.



================ PART B ================

3. 三条观察，都是直接的：
   - (P2) ¬¬St(a) **不是**定理（∀x¬¬(¬¬B → B) 是定理，¬¬∀x(¬¬B → B) 不是）。但它是负公式，可以写进负的序数公式。
   - (P3) 打开原则只能对有限个、有名字的对象使用。所以凡是"∀y ∈ a，y 正则"这类全称前提必须直接成立的地方，¬¬ 版本不够；本文的证明安排成在这些地方只需要逐点的 ¬¬ 事实。

### M1　序数公式 κ 及其基本性质

κ(a) 是下列八条的合取（uniform，无参数）：
- (K1) ∀y∀z(¬¬z ∈ y → ¬¬y ∈ a → ¬¬z ∈ a)；
- (K2) ∀y(¬¬y ∈ a → y 满足 K1)；
- (K3) ∀y(¬¬y ∈ a → y ∉ y)；
- (K4) ∀y(¬¬y ∈ a → ¬¬S(y))，S(y) := ∃h∀v(v ∈ h ↔ v = y)；
- (K5) ∀y∀z(¬¬y ∈ a → ¬¬z ∈ a → ¬¬(y ∈ z ∨ y = z ∨ z ∈ y))；
- (K6) ∀C∀x(¬¬x ∈ a → x ∉ C → ¬¬∃z((z = x ∨ z ∈ x) ∧ z ∉ C ∧ ∀w(w ∈ z → ¬¬w ∈ C)))；
- (K7) ¬¬St(a)；
- (K8) ∀y(¬¬y ∈ a → ¬¬St(y))。

K1–K3 与 ι 相同；K4–K6 是论文 O4–O6 的 ¬¬ 形式；K7、K8 是新的。性质：
- (a) **稳定**：¬¬κ^s(a) → κ^s(a)。每条子句都形如 ∀…(… → ¬H) 或 ¬¬H。由 (P1)，W = {x | κ(x)} 的两个面都稳定。
- (b) **成员**（引理 4(1)）：κ^s(a) ∧ ¬¬(y ∈_s a) → κ^s(y)。由 K1，y 的 ¬¬-成员是 a 的 ¬¬-成员；K7 对 y 由 a 的 K8 给出。
- (c) **翻转**（引理 4(4)）：Reg(r) ∧ κ^s(r) → κ^{s̄}(r)。这是论文引理 2 用于句子 κ(r)：A = {x | κ(r)}，V = {x | x = x}，由 ME 得 A = V。

### M2　κ 的引理 4(3)、5、6

稳定性都以假设出现，而且只对有名字的对象。
- **(4(3)) self-wf**：若 κ^s(x)、St_s(x)、x ∉_s C，则 ¬¬∃z((z = x ∨ z ∈_s x) ∧ z ∉_s C ∧ ∀w(w ∈_s z → ¬¬w ∈_s C))。
  证明：设没有这样的 z。则 z := x 不行，只需证 ∀w(w ∈_s x → ¬¬w ∈_s C)。设 w ∈_s x、w ∉_s C；x 的 K6 给出 ¬¬∃z′(…)，目标是 ⊥，打开得 z′。z′ = w 或 z′ ∈_s w，由 K1 与 St_s(x) 得 z′ ∈_s x，于是 z′ 正是所设不存在的 z，矛盾。
- **(5) seg**：设 κ^s(α)、St_s(α)；γ 正则、St_s(γ)、γ 的 s-面正向传递（z ∈_s y ∈_s γ → z ∈_s γ），且 F_s(γ) ⊆ F_s(α)。则 ¬¬(γ = α ∨ γ ∈_s α)。
  证明：设 ¬(γ = α ∨ γ ∈_s α)。先证 F_s(α) ⊆ F_s(γ)：设 x ∈_s α，由 St_s(γ) 只需否定 x ∉_s γ。若 x ∉_s γ，α 的 K6（C = γ）给出 ¬¬∃z(…)；目标 ⊥，打开得 z。
  - z ∈_s α（K1、St_s(α)），z ∉_s γ，且 F_s(z) ⊆ F_s(γ)（由 St_s(γ)）。
  - α 的 K8 给出 ¬¬St_s(z)；目标仍是 ⊥，打开得 St_s(z)。
  - F_s(γ) ⊆ F_s(z)：设 y ∈_s γ，由 St_s(z) 只需否定 y ∉_s z。α 的 K5 给出 ¬¬(y ∈_s z ∨ y = z ∨ z ∈_s y)；y = z 推出 z ∈_s γ，z ∈_s y 由 γ 的传递性也推出 z ∈_s γ，都不行；剩下 y ∈_s z。
  - 于是 F_s(z) = F_s(γ)，由引理 1（γ 正则）z = γ，故 γ ∈_s α，矛盾。

  所以 F_s(α) = F_s(γ)，由引理 1 得 α = γ，矛盾。
- **(6) compare**：α、β 正则，κ^s(α)、κ^s(β)、St_s(α)、St_s(β)，则 ¬¬(α ∈_s β ∨ α = β ∨ β ∈_s α)。
  证明：γ = {x | x ∈ α ∧ x ∈ β}（参数正则），γ 正则，F_s(γ) = F_s(α) ∩ F_s(β) 稳定且正向传递。对 (α, γ) 与 (β, γ) 用 seg，四种情形同论文引理 6；γ ∈_s α ∧ γ ∈_s β 推出 γ ∈_s γ，与 α 的 K3 矛盾。

### M3　κ 的命题 1（Burali-Forti）

对每一对相反的侧 (b, c)：COMP + ME ⊢ᵢ ¬∀x(κ^c(x) → ¬¬Reg(x))。所以 ⊢ᵢ ¬¬∃a(κ^c(a) ∧ ¬Reg(a))，两侧都如此。

证明：设 H：∀x(κ^c(x) → ¬¬Reg(x))。W = {x | κ(x)}，F_b(W) = {x : κ^c(x)}，F_c(W) = {x : κ^b(x)}。验证定理 1 的三个条件（论文 §3 的对角论证是直觉主义的）：
- (i) κ^c(x) → κ^b(x)：由 M1(a) 只需 ¬¬κ^b(x)；H 给出 ¬¬Reg(x)，打开后用 M1(c)。
- (ii) 由 K3。
- (iii) κ^b(W)。每条子句都是负的，所以对每个实例，可以打开所涉成员的 ¬¬ 事实：
  - K1：给定 y、z 与 ¬¬(z ∈_b y)、¬¬(y ∈_b W)，目标 ¬¬(z ∈_b W)，是负目标。打开 ¬¬(y ∈_b W) 得 κ^c(y)，由 H 打开 ¬¬Reg(y)。再打开 ¬¬(z ∈_b y) 得 z ∈_b y，由 Reg(y) 得 z ∈_c y；于是 κ^c(z)（M1(b)，c 侧），即 z ∈_b W。也可以不打开 ¬¬(z ∈_b y)，直接用 Reg(y) 把它搬到 c 侧，得 ¬¬(z ∈_c y)，再用 M1(b)。
  - K2、K3：对 ¬¬(y ∈_b W)，目标分别是 K1^b(y) 与 y ∉_b y，都是负目标。打开得 κ^c(y) 与 Reg(y)，由翻转 M1(c) 得 κ^b(y)；K1^b(y) 就是 κ^b(y) 的 K1，y ∉_b y 由 κ^b(y) 的 K3 用于 y 自身（¬¬(y ∈_b y) 由假设 y ∈_b y 给出）。
  - K4：打开 ¬¬Reg(y)，{x | x = y} 是 b-单元集。
  - K5：对 y、z ∈_b W，目标是 ¬¬(…)。打开 ¬¬Reg(y)、¬¬Reg(z)，以及 K7^c 给出的 ¬¬St_c(y)、¬¬St_c(z)；正则性把 c-面的稳定性搬到 b-面；用 M1(c) 与 M2 的 compare。
  - K6：对 x ∈_b W，打开 ¬¬Reg(x) 与 ¬¬St_c(x)，用 M1(c) 与 self-wf。
  - **K7**：F_b(W) = {x : κ^c(x)} 由 M1(a) 稳定，所以 St_b(W) 直接成立，¬¬St_b(W) 更不必说。
  - K8：对 y ∈_b W，打开 ¬¬Reg(y) 与 ¬¬St_c(y)，得 St_b(y)。

由定理 1 得 ⊥。∎

ME 在这里只经两处进入：M1(c) 的翻转（A = V），与 seg 中的引理 1（被等同的一方 γ 正则）。

### M4　κ 的 Descent

若 κ^s(α) 且 ¬Reg(α)，则 ¬¬∃p(κ^s(p) ∧ ¬Reg(p) ∧ ∀y(¬¬y ∈_s p → ¬¬Reg(y)))。后一个合取项称为 p **¬¬-纯**。

证明：设没有这样的 p。
- α 本身不行，所以 ¬∀y(¬¬y ∈_s α → ¬¬Reg(y))，直觉主义地等价于 ¬¬∃x(¬¬x ∈_s α ∧ ¬Reg(x))。目标 ⊥，打开得 x。
- D = {x | ¬¬S(x)}，F_s(D) = {x : ¬¬S^{s̄}(x)}。对 ¬¬y ∈_s α：K4 给出 ¬¬S^s(y)，若再有 ¬¬S^{s̄}(y)，由论文引理 3 后半得 ¬¬Reg(y)。所以 x ∉_s D。
- α 的 K6（C = D）给出 ¬¬∃z(…)，打开得 z：¬¬z ∈_s α，故 κ^s(z)（M1(b)）；¬Reg(z)，否则 {x | x = z} 是 s̄-单元集，z ∈_s D；对 ¬¬y ∈_s z，有 ¬¬y ∈_s D 与 ¬¬y ∈_s α，故 ¬¬Reg(y)。
- 于是 z 就是所设不存在的 p，矛盾。∎


### M5　κ 的 Cut 与命题 2

**Cut.** 设 κ^s(p)、St_s(p)、¬Reg(p)；t 正则、κ^s(t)、St_s(t)，且 t ¬¬-纯。则 t ∈_s p。
- (inside) 若 z 正则、κ^s(z)、St_s(z)、F_s(z) ⊆ F_s(p)，则 z ∈_s p：由 St_s(p) 只需否定 z ∉_s p；seg（α = p，γ = z）给出 ¬¬(z = p ∨ z ∈_s p)，而 z = p 使 p 正则。
- (sub) F_s(t) ⊆ F_s(p)：设 x ∈_s t，由 St_s(p) 只需否定 x ∉_s p。t 的 K6（C = p）给出 ¬¬∃z(…)；目标 ⊥，依次打开 z、¬¬Reg(z)（t ¬¬-纯）、¬¬St_s(z)（t 的 K8）。于是 z 正则、κ^s(z)、St_s(z)、F_s(z) ⊆ F_s(p)（由 St_s(p)），inside 给出 z ∈_s p，矛盾。
- 再对 t 用 inside。∎

**命题 2.** 设 p：κ^∈(p)、St_∈(p)、¬Reg(p)、¬¬-纯；q：κ^ε(q)、St_ε(q)、¬Reg(q)、¬¬-纯。则 ⊥。
- F_∈(p) ⊆ F_ε(q)：设 x ∈ p，由 St_ε(q) 只需否定 x ∉_ε q。打开 ¬¬Reg(x)（p ¬¬-纯）与 ¬¬St_∈(x)（p 的 K8）。于是 κ^∈(x)（M1(b)），κ^ε(x)（M1(c)），St_ε(x)（正则）。x 的 ε-成员就是它的 ∈-成员，是 p 的 ¬¬-成员，所以 x ¬¬-纯。对侧 ε 用 Cut，得 x ε q。
- 对称地 F_ε(q) ⊆ F_∈(p)。
- 由 ME，p = q；于是 F_ε(p) = F_ε(q) = F_∈(p)，p 正则，矛盾。∎

与论文命题 2 的差别只在两处：p、q 的面稳定性由假设给出；成员的正则性只用 ¬¬ 形式。

### M6　主定理：DEST⁻ ⊢ᵢ ⊥

证明：目标 ⊥。
1. 由 M3（两对侧），打开 ¬¬∃a(κ^∈(a) ∧ ¬Reg(a)) 与 ¬¬∃a′(κ^ε(a′) ∧ ¬Reg(a′))。
2. 由 M4，打开得 ¬¬-纯的非正则 κ^∈-对象 p 与 κ^ε-对象 q。
3. p 的 K7 给出 ¬¬St_∈(p)，q 的 K7 给出 ¬¬St_ε(q)；打开。
4. 由 M5 的命题 2 得 ⊥。∎

推论：DEST ⊢ᵢ ⊥（DEST 含 DEST⁻）。

用到的 COMP 实例共八种，与论文 §5 末的清单逐项对应，但其中三种把 ord 换成了 κ（翻转句 κ(r)、W、对角对象），D 用 ¬¬S（纸面上用论文的 S 也可以：M4 中 D 只经 S^{s̄} 的 ¬¬ 形式使用）：
- V = {x | x = x}；
- {x | x = r}，r 正则（单元集）；
- {x | κ(r)}，r 正则，x 不出现（翻转）；
- γ = {x | x ∈ α ∧ x ∈ β}；
- D = {x | ¬¬S(x)}；
- W = {x | κ(x)}；
- 对角对象，P = κ，参数 V。

论文的数量界照样成立：κ 的量词秩为 4（K6：∀C∀x¬¬∃z…∀w），对角公式为 5（Θ 中的 ∃u 再套 κ(u)），每个实例至多两个参数（γ 的 α、β）。

ME 的用处与论文相同：翻转中的 A = V；引理 1（被等同的一方正则）；引理 3 后半的 h = h′ 与 y = k；命题 2 的 p = q。
