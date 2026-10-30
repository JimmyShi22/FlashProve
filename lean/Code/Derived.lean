-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Derived.lean: what follows from mutual correlated agreement on lines.

The protocols combine words with three kinds of coefficients: a line (1, θ), one independent
coefficient for each word, and the tensor eq(γ, ·). Only the number of bad θ for a line is a
parameter of a code (`Code.MCA` in Code/Agree.lean). This file bounds the other two by it. All
bounds are counts of bad values of the verifier's message; q is the number of elements of the field
E, and `bad` the count for lines.

 * one independent coefficient for each of the words f_i, i ∈ I, with or without a first word of
   coefficient 1 (item (b)):
       (number of bad vectors) · (q - 1) ≤ bad · q^|I|.
 * the coefficients eq(γ, v), v ∈ {0,1}^k, γ ∈ E^k (item (c)):
       (number of bad γ) · q ≤ (c_0 + ... + c_(k-1)) · q^k ,
   where c_j is the count for lines of interleaved words with 2^j times as many rows as the words
   f_v.

A set of positions is large if it omits at most e positions. Part 2 proves the two bounds for any
family K of subspaces of a vector space V: their proofs use only one fact about codes: for every set
S of positions, the words that agree on S with a word of the code form a subspace. K s takes the
role of these words, and s that of a large set S. The parts 1 to 5 and the items (a), (b), (c), (f)
are marked in the section headings.

The letters (a) to (f) number six statements on mutual correlated agreement: (a), (b), (c) and (f)
are in this file, (d) is in Code/Mutual.lean; (e) is not proved in this library (see the head of
that file).
Items (a), (b), (c) are published. The main sources: Bordage, Chiesa, Guan and Manzur
(ePrint 2025/2051, Lemma 7.1) for (b); Diamond and Posen (ePrint 2023/630, Theorem 3.1), Angeris,
Evans and Roh (ePrint 2024/1399, (22)) and Diamond and Gruen (ePrint 2024/1351, Theorem 3.6) for
(c); Arnon, Chiesa, Fenzi and Yogev (ePrint 2024/1586, Lemma 4.13) for (a). For (f) we know a source
for Reed-Solomon codes only. The statements of 5 and, in 3, "MCAFor.cnt_close_line",
"MCAFor.cnt_close_comb_mul" and
"MCAFor.cnt_close_one_comb_mul" in the case of single words are this project's own.
Nothing is assumed beyond the hypotheses of the statements: everything is proved from the
definitions.

Notation:
  `Close D e f` (Code/Third.lean): a proposition: the interleaved word f, with rows indexed by R, is
    close to the interleaved code: on one common set of all but at most e positions every row agrees
    with a word of the code D; far: not close (`¬ Close D e f`);
  eq(z, b), `Alg.eqk z b` (Alg/Mle.lean): an element of the field: ∏_v (z_v if b_v = 1, else
    1 - z_v), for a point z and a vertex b of the cube;
  `liftWord E u` (Code/Third.lean): a vector over the small field F, read over the large field E;
  `extendCode E C` (Code/Third.lean): the extension code: the span over E of the words of a code
    over F;
  n: a natural number, the number of positions (`Fintype.card ι`).
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Module
import Alg.Count
import Alg.Mle
import Code.Third

set_option autoImplicit false

namespace Code

open Finset Prob

/-! ## 1. Counting -/

section Counting

variable {α β : Type}

/-- The pairs with a property, counted by rows and counted by columns. -/
theorem sum_cnt_comm [Fintype α] [Fintype β] (g : α → β → Prop) :
    ∑ a, cnt (g a) = ∑ b, cnt (fun a => g a b) :=
  (Alg.count_prod (fun p : α × β => g p.1 p.2)).symm.trans
    ((Alg.count_equiv (Equiv.prodComm α β) (fun p : β × α => g p.2 p.1)).trans
      (Alg.count_prod (fun p : β × α => g p.2 p.1)))

/-- The elements with a property and those without it are all elements. -/
theorem cnt_add_cnt_not [Fintype α] (P : α → Prop) :
    cnt P + cnt (fun a => ¬ P a) = Fintype.card α := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter, card_filter_add_card_filter_not, card_univ]

/-- Counting pairs in two ways. Let every a with the property T be in at least lo / w pairs, and
every b in at most hi / w pairs.
Then (number of a with T) · lo ≤ (number of b) · hi. -/
theorem cnt_mul_le_of_pairs [Fintype α] [Fintype β] (g : α → β → Prop) (T : α → Prop) (w lo hi : ℕ)
    (hlo : ∀ a, T a → lo ≤ cnt (g a) * w) (hhi : ∀ b, cnt (fun a => g a b) * w ≤ hi) :
    cnt T * lo ≤ Fintype.card β * hi := by
  classical
  calc cnt T * lo = ∑ _a ∈ univ.filter T, lo := by rw [sum_const, smul_eq_mul, cnt_eq_card_filter]
    _ ≤ ∑ a ∈ univ.filter T, cnt (g a) * w := sum_le_sum fun a ha => hlo a (mem_filter.mp ha).2
    _ ≤ ∑ a, cnt (g a) * w := sum_le_sum_of_subset (filter_subset _ _)
    _ = ∑ b, cnt (fun a => g a b) * w := by rw [← sum_mul, ← sum_mul, sum_cnt_comm]
    _ ≤ ∑ _b : β, hi := sum_le_sum fun b _ => hhi b
    _ = Fintype.card β * hi := by rw [sum_const, card_univ, smul_eq_mul]

/-- From the factor q - 1 to the factor 2: if q ≥ 2 and T (q - 1) ≤ M, then T q ≤ 2 M. -/
theorem mul_le_two_mul_of_mul_pred_le {T q M : ℕ} (hq : 2 ≤ q) (h : T * (q - 1) ≤ M) :
    T * q ≤ 2 * M :=
  calc T * q ≤ T * (2 * (q - 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (T * (q - 1)) := Nat.mul_left_comm _ _ _
    _ ≤ 2 * M := Nat.mul_le_mul_left _ h

/-- A proper subspace contains at most a q-th of the vectors. -/
theorem cnt_mem_mul_card_le {E W : Type} [Field E] [AddCommGroup W] [Module E W] [Fintype E]
    [Fintype W] (P : Submodule E W) {x : W} (hx : x ∉ P) :
    cnt (fun w => w ∈ P) * Fintype.card E ≤ Fintype.card W := by
  have hinj : Function.Injective (fun p : {w : W // w ∈ P} × E => p.1.1 + p.2 • x) := by
    rintro ⟨⟨p, hp⟩, z⟩ ⟨⟨p', hp'⟩, z'⟩ h
    have h' : p + z • x = p' + z' • x := h
    have hz : z = z' := by
      by_contra hne
      have h1 : (z - z') • x = p' - p := by
        rw [sub_smul]
        exact sub_eq_sub_iff_add_eq_add.mpr ((add_comm _ _).trans h')
      exact hx ((P.smul_mem_iff (sub_ne_zero.mpr hne)).mp (by rw [h1]; exact P.sub_mem hp' hp))
    subst hz
    have hpp : p = p' := add_right_cancel h'
    subst hpp
    rfl
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := E), Nat.card_eq_fintype_card (α := W)] at h
  exact h

end Counting

/-! ## 2. Families of subspaces -/

section Family

variable {E V σ : Type} [Field E] [AddCommGroup V] [Module E V]

/-- Tables with rows indexed by R, all of whose rows lie in K s. (For codes: interleaved words.) -/
def rows (R : Type) (K : σ → Submodule E V) (s : σ) : Submodule E (R → V) where
  carrier := {f | ∀ a, f a ∈ K s}
  add_mem' := fun hf hg a => (K s).add_mem (hf a) (hg a)
  zero_mem' := fun _ => (K s).zero_mem
  smul_mem' := fun c _ hf a => (K s).smul_mem c (hf a)

@[simp] theorem mem_rows {R : Type} {K : σ → Submodule E V} {s : σ} {f : R → V} :
    f ∈ rows R K s ↔ ∀ a, f a ∈ K s := Iff.rfl

/-- The coefficient vector c is bad for the vectors f_i: for some s the combination ∑ c_i f_i is in
K s, but not all f_i are. -/
def BadFor {I : Type} [Fintype I] (K : σ → Submodule E V) (c : I → E) (f : I → V) : Prop :=
  ∃ s, ∑ i, c i • f i ∈ K s ∧ ∃ i, f i ∉ K s

/-- At most `bad` values of θ are bad for a line: for every pair f₀, f₁, at most `bad` values θ
admit an s such that f₀ + θ f₁ is in K s while f₀ and f₁ are not both in K s. -/
def LineBound [Finite E] (K : σ → Submodule E V) (bad : ℕ) : Prop :=
  ∀ f₀ f₁ : V, cnt (fun θ : E => ∃ s, f₀ + θ • f₁ ∈ K s ∧ ¬ (f₀ ∈ K s ∧ f₁ ∈ K s)) ≤ bad

section Comb

variable {I : Type} [Fintype I]

theorem sum_add_smul (a b : I → E) (f : I → V) :
    ∑ i, (a + b) i • f i = ∑ i, a i • f i + ∑ i, b i • f i := by
  simp only [Pi.add_apply, add_smul, sum_add_distrib]

theorem sum_smul_smul (z : E) (a : I → E) (f : I → V) :
    ∑ i, (z • a) i • f i = z • ∑ i, a i • f i := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum]

/-- The coefficient vectors whose combination of the f_i is in the subspace P. -/
def combIn (P : Submodule E V) (f : I → V) : Submodule E (I → E) where
  carrier := {l | ∑ i, l i • f i ∈ P}
  add_mem' := fun {x y} hx hy => by
    show ∑ i, (x + y) i • f i ∈ P
    rw [sum_add_smul]
    exact P.add_mem hx hy
  zero_mem' := by
    show ∑ i, (0 : I → E) i • f i ∈ P
    simp
  smul_mem' := fun c x hx => by
    show ∑ i, (c • x) i • f i ∈ P
    rw [sum_smul_smul]
    exact P.smul_mem c hx

/-- With a first vector of coefficient 1: (1, a) is bad for (f₀, f) if and only if some K s contains
f₀ + ∑ a_i f_i but not all of f₀ and the f_i. -/
theorem badFor_option_iff (K : σ → Submodule E V) (a : I → E) (f₀ : V) (f : I → V) :
    BadFor K (fun o : Option I => o.elim 1 a) (fun o => o.elim f₀ f)
      ↔ ∃ s, f₀ + ∑ i, a i • f i ∈ K s ∧ ¬ (f₀ ∈ K s ∧ ∀ i, f i ∈ K s) := by
  unfold BadFor
  refine exists_congr fun s => ?_
  rw [Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, one_smul]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨o, ho⟩ ⟨h0, h1⟩
    cases o with
    | none => exact ho h0
    | some i => exact ho (h1 i)
  · intro hn
    by_contra hall
    push Not at hall
    exact hn ⟨hall none, fun i => hall (some i)⟩

/-- Without a first vector: put f₀ = 0, which is in every subspace. -/
theorem badFor_iff_zero_add (K : σ → Submodule E V) (a : I → E) (f : I → V) :
    BadFor K a f ↔ ∃ s, (0 : V) + ∑ i, a i • f i ∈ K s ∧ ¬ ((0 : V) ∈ K s ∧ ∀ i, f i ∈ K s) := by
  unfold BadFor
  refine exists_congr fun s => ?_
  rw [zero_add]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨i, hi⟩ ⟨_, h1⟩
    exact hi (h1 i)
  · intro hn
    by_contra hall
    push Not at hall
    exact hn ⟨(K s).zero_mem, hall⟩

end Comb

/-! ### One independent coefficient for each vector (item (b)) -/

section Independent

variable [Fintype E] {K : σ → Submodule E V} {bad : ℕ} {I : Type} [Fintype I]

/-- Independent coefficients, the core (under `h`). The proof is an average over directions. Call a
pair (a, l) of coefficient vectors good if some K s contains f₀ + ∑ a_i f_i and does not contain
∑ l_i f_i.
If a is bad, as witnessed by s, then some f_i is outside K s, so the l whose combination is in K s
form a proper subspace, and a is in at least (1 - 1/q) q^|I| good pairs. For a fixed direction l and
a fixed base point a, the z with (a + z l, l) good are bad for the line through f₀ + ∑ a_i f_i with
direction ∑ l_i f_i, so there are at most `bad` of them; averaging over the base points, l is in at
most bad · q^|I| / q good pairs. -/
theorem LineBound.cnt_affine_mul (h : LineBound K bad) (f₀ : V) (f : I → V) :
    cnt (fun a : I → E => ∃ s, f₀ + ∑ i, a i • f i ∈ K s ∧ ¬ (f₀ ∈ K s ∧ ∀ i, f i ∈ K s)) *
        (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I := by
  classical
  have hN : Fintype.card (I → E) = Fintype.card E ^ Fintype.card I := Fintype.card_fun
  rw [← hN]
  have hNpos : 0 < Fintype.card (I → E) := Fintype.card_pos
  let good : (I → E) → (I → E) → Prop := fun a l =>
    ∃ s, f₀ + ∑ i, a i • f i ∈ K s ∧ ∑ i, l i • f i ∉ K s
  have hlo : ∀ a : I → E, (∃ s, f₀ + ∑ i, a i • f i ∈ K s ∧ ¬ (f₀ ∈ K s ∧ ∀ i, f i ∈ K s)) →
      Fintype.card (I → E) * (Fintype.card E - 1) ≤ cnt (good a) * Fintype.card E := by
    rintro a ⟨s, hs, hnot⟩
    obtain ⟨i₀, hi₀⟩ : ∃ i, f i ∉ K s := by
      by_contra hall
      push Not at hall
      refine hnot ⟨?_, hall⟩
      have hc : ∑ i, a i • f i ∈ K s := (K s).sum_mem fun i _ => (K s).smul_mem _ (hall i)
      have hsub := (K s).sub_mem hs hc
      rwa [add_sub_cancel_right] at hsub
    have hx : (Pi.single i₀ 1 : I → E) ∉ combIn (K s) f := by
      intro hmem
      change ∑ i, (Pi.single i₀ 1 : I → E) i • f i ∈ K s at hmem
      rw [show ∑ i, (Pi.single i₀ 1 : I → E) i • f i =
          f i₀ by simp [Pi.single_apply, ite_smul]] at hmem
      exact hi₀ hmem
    have h1 := cnt_mem_mul_card_le (combIn (K s) f) hx
    have h2 := cnt_add_cnt_not (fun l : I → E => l ∈ combIn (K s) f)
    have h3 : cnt (fun l : I → E => ¬ l ∈ combIn (K s) f) ≤ cnt (good a) :=
      cnt_mono fun l hl => ⟨s, hs, hl⟩
    rw [Nat.mul_sub_one, Nat.sub_le_iff_le_add]
    calc Fintype.card (I → E) * Fintype.card E
        = cnt (fun l : I → E => l ∈ combIn (K s) f) * Fintype.card E
          + cnt (fun l : I → E => ¬ l ∈ combIn (K s) f) * Fintype.card E := by rw [← h2, add_mul]
      _ ≤ Fintype.card (I → E) + cnt (good a) * Fintype.card E :=
        Nat.add_le_add h1 (Nat.mul_le_mul_right _ h3)
      _ = cnt (good a) * Fintype.card E + Fintype.card (I → E) := Nat.add_comm _ _
  have hhi : ∀ l : I → E,
      cnt (fun a => good a l) * Fintype.card E ≤ bad * Fintype.card (I → E) := by
    intro l
    have e1 : ∀ z : E,
        cnt (fun a : I → E => good (a + z • l) l) = cnt (fun a => good a l) := fun z =>
      Alg.count_equiv (Equiv.addRight (z • l)) (fun a => good a l)
    have e2 : ∀ a : I → E, cnt (fun z : E => good (a + z • l) l) ≤ bad := by
      intro a
      refine (cnt_mono ?_).trans (h (f₀ + ∑ i, a i • f i) (∑ i, l i • f i))
      intro z hz
      obtain ⟨s, hs, hl⟩ := hz
      rw [sum_add_smul, sum_smul_smul, ← add_assoc] at hs
      exact ⟨s, hs, fun hh => hl hh.2⟩
    calc cnt (fun a => good a l) * Fintype.card E
        = ∑ z : E, cnt (fun a : I → E => good (a + z • l) l) := by
          rw [sum_congr rfl fun z _ => e1 z, sum_const, card_univ, smul_eq_mul, mul_comm]
      _ = ∑ a : I → E, cnt (fun z : E => good (a + z • l) l) :=
        sum_cnt_comm fun z a => good (a + z • l) l
      _ ≤ ∑ _a : I → E, bad := sum_le_sum fun a _ => e2 a
      _ = bad * Fintype.card (I → E) := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]
  have key := cnt_mul_le_of_pairs good _ (Fintype.card E) _ _ hlo hhi
  refine Nat.le_of_mul_le_mul_left ?_ hNpos
  rw [Nat.mul_left_comm]
  exact key

/-- Under `h`, with one independent uniform coefficient a_i for each of the vectors
f_i:
(number of bad a) · (q - 1) ≤ bad · q^|I|. As a probability: at most (bad / q) · (1 - 1/q)^(-1). -/
theorem LineBound.cnt_badFor_mul (h : LineBound K bad) (f : I → V) :
    cnt (fun a : I → E => BadFor K a f) * (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I := by
  simp only [badFor_iff_zero_add]
  exact h.cnt_affine_mul 0 f

/-- Under `h`, `LineBound.cnt_badFor_mul` for the coefficients (1, a): the first vector has the
coefficient 1, each other one an independent uniform one. -/
theorem LineBound.cnt_badFor_one_mul (h : LineBound K bad) (f₀ : V) (f : I → V) :
    cnt (fun a : I → E => BadFor K (fun o : Option I => o.elim 1 a) (fun o => o.elim f₀ f)) *
        (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I := by
  simp only [badFor_option_iff]
  exact h.cnt_affine_mul f₀ f

end Independent

/-! ### The coefficients eq(γ, ·) (item (c)) -/

section Tensor

variable [Fintype E]

omit [Fintype E] in
/-- The combination with the coefficients eq((x, γ), ·) of the 2^(k+1) vectors f_v is the
combination with the coefficients eq(γ, ·) of the 2^k vectors f_(0,v) + x (f_(1,v) - f_(0,v)).
Coordinate 0 of a vertex or of a point comes first. -/
theorem sum_eqk_cons_smul {k : ℕ} (x : E) (γ : Fin k → E) (f : (Fin (k + 1) → Bool) → V) :
    ∑ v, Alg.eqk (Fin.cons x γ : Fin (k + 1) → E) v • f v =
      ∑ v : Fin k → Bool, Alg.eqk γ v •
        (f (Fin.cons false v) + x • (f (Fin.cons true v) - f (Fin.cons false v))) := by
  rw [Alg.sum_cube_succ]
  refine sum_congr rfl fun v _ => ?_
  rw [Alg.eqk_cons, Alg.eqk_cons]
  simp only [Bool.false_eq_true, if_false, if_true]
  module

/-- The coefficients eq(γ, ·). Let c j bound the number of bad θ for lines of tables with 2^j rows,
for every j < k. Then for all vectors f_v, v ∈ {0,1}^k: (number of γ ∈ E^k such that (eq(γ, v))_v is
bad) · q ≤ (c 0 + ... + c (k - 1)) · q^k.

The proof is an induction on k. In the step from k to k + 1 write γ = (x, γ'), and let F₀, F₁ be the
tables (f_(0,v))_v and (f_(1,v))_v, of 2^k rows each. Let γ be bad, as witnessed by s. Either all
rows of F₀ + x (F₁ - F₀) lie in K s; then x is bad for the line through F₀ with direction F₁ - F₀,
with the same s, and there are at most c k such x. Or not; then γ' is bad for the rows of F₀ + x (F₁
- F₀), which do not depend on γ', and the induction applies for each x. -/
theorem cnt_badFor_eqk_mul (K : σ → Submodule E V) (c : ℕ → ℕ) :
    ∀ k : ℕ, (∀ j < k, LineBound (rows (Fin j → Bool) K) (c j)) →
      ∀ f : (Fin k → Bool) → V, cnt (fun γ : Fin k → E => BadFor K (Alg.eqk γ) f) * Fintype.card E ≤
        (∑ j ∈ range k, c j) * Fintype.card E ^ k
  | 0, _, f => by
    have h0 : cnt (fun γ : Fin 0 → E => BadFor K (Alg.eqk γ) f) = 0 := by
      refine cnt_false ?_
      rintro γ ⟨s, hs, v, hv⟩
      have hsum : ∑ w, Alg.eqk γ w • f w = f v := by
        rw [Fintype.sum_eq_single v fun w hw => absurd (Subsingleton.elim w v) hw]
        simp [Alg.eqk]
      rw [hsum] at hs
      exact hv hs
    rw [h0]
    simp
  | k + 1, h, f => by
    have ih := cnt_badFor_eqk_mul K c k fun j hj => h j (Nat.lt_succ_of_lt hj)
    let F₀ : (Fin k → Bool) → V := fun v => f (Fin.cons false v)
    let F₁ : (Fin k → Bool) → V := fun v => f (Fin.cons true v)
    let B : E → Prop := fun x =>
      ∃ s,
        F₀ + x • (F₁ - F₀) ∈ rows (Fin k → Bool) K s ∧
        ¬ (F₀ ∈ rows (Fin k → Bool) K s ∧ F₁ - F₀ ∈ rows (Fin k → Bool) K s)
    have hB : cnt B ≤ c k := h k (Nat.lt_succ_self k) F₀ (F₁ - F₀)
    have hstep : ∀ x : E, ¬ B x →
        ∀ γ : Fin k → E, BadFor K (Alg.eqk (Fin.cons x γ : Fin (k + 1) → E)) f →
          BadFor K (Alg.eqk γ) (F₀ + x • (F₁ - F₀)) := by
      rintro x hx γ ⟨s, hs, v, hv⟩
      rw [sum_eqk_cons_smul] at hs
      refine ⟨s, hs, ?_⟩
      by_contra hall
      push Not at hall
      refine hx ⟨s, mem_rows.mpr hall, fun hb => hv ?_⟩
      have h0 := mem_rows.mp hb.1 (Fin.tail v)
      have h1 := (K s).add_mem h0 (mem_rows.mp hb.2 (Fin.tail v))
      have hfv : f v = f (Fin.cons (v 0) (Fin.tail v)) := by rw [Fin.cons_self_tail]
      rw [hfv]
      cases v 0 with
      | false => exact h0
      | true =>
        rw [Pi.sub_apply, add_sub_cancel] at h1
        exact h1
    have key := Alg.count_prod_mul_le
      (fun p : E × (Fin k → E) => BadFor K (Alg.eqk (Fin.cons p.1 p.2 : Fin (k + 1) → E)) f)
      B (Fintype.card E) (c k) (∑ j ∈ range k, c j) (Nat.mul_le_mul_right _ hB)
      (fun x hx => by
        have h1 : cnt (fun γ : Fin k → E => BadFor K (Alg.eqk (Fin.cons x γ : Fin (k + 1) → E)) f) ≤
            cnt (fun γ : Fin k → E => BadFor K (Alg.eqk γ) (F₀ + x • (F₁ - F₀))) :=
          cnt_mono (hstep x hx)
        rw [Fintype.card_fun, Fintype.card_fin]
        exact (Nat.mul_le_mul_right _ h1).trans (ih _))
    have hcnt : cnt (fun γ : Fin (k + 1) → E => BadFor K (Alg.eqk γ) f) =
        Nat.card
          {p : E × (Fin k → E) // BadFor K (Alg.eqk (Fin.cons p.1 p.2 : Fin (k + 1) → E)) f} :=
      (Alg.count_equiv (Fin.consEquiv fun _ : Fin (k + 1) => E)
        (fun γ : Fin (k + 1) → E => BadFor K (Alg.eqk γ) f)).symm
    have hcard : Fintype.card (E × (Fin k → E)) = Fintype.card E ^ (k + 1) := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_succ']
    rw [hcnt, sum_range_succ, add_comm (∑ j ∈ range k, c j), ← hcard]
    exact key

/-- The coefficients eq(γ, ·), with one count for tables of every number of rows: (number of bad
γ) · q ≤ k · bad · q^k. -/
theorem cnt_badFor_eqk_mul_of_forall (K : σ → Submodule E V) {bad : ℕ}
    (h : ∀ (R : Type) [Finite R], LineBound (rows R K) bad) (k : ℕ) (f : (Fin k → Bool) → V) :
    cnt (fun γ : Fin k → E => BadFor K (Alg.eqk γ) f) * Fintype.card E ≤
      k * bad * Fintype.card E ^ k := by
  have h1 := cnt_badFor_eqk_mul K (fun _ => bad) k (fun j _ => h (Fin j → Bool)) f
  rwa [sum_const, card_range, smul_eq_mul] at h1

end Tensor

end Family

/-! ## 3. Codes -/

section Codes

variable {E ι : Type} [Field E] [Fintype ι]

/-- The coefficient vector c is bad for the interleaved words f_i, i ∈ I, with rows indexed by R, at
the radius e:
there is a set S of all but at most e positions on which every row of ∑ c_i f_i agrees with a word
of the code D, while some row of some f_i does not. -/
def Bad {I R : Type} [Fintype I] (D : Submodule E (ι → E)) (e : ℕ) (c : I → E) (f : I → R → ι → E) :
    Prop :=
  ∃ S : Finset ι,
    Fintype.card ι ≤ S.card + e ∧ (∀ a, ∑ i, c i • f i a ∈ agreeOn D S) ∧ ∃ i a, f i a ∉ agreeOn D S

/-- Mutual correlated agreement on lines of interleaved words with the set R of rows: an error
ε_mca ≤ bad / q for the m-interleaved code over E, m = |R|.
`Code.MCA` asks for this with one count for every finite R. -/
def MCAFor [Finite E] (D : Submodule E (ι → E)) (e : ℕ) (R : Type) (bad : ℕ) : Prop :=
  ∀ f₀ f₁ : R → ι → E,
    cnt (fun θ : E =>
        ∃ S : Finset ι,
          Fintype.card ι ≤ S.card + e ∧
          (∀ a, f₀ a + θ • f₁ a ∈ agreeOn D S) ∧
          ¬ ((∀ a, f₀ a ∈ agreeOn D S) ∧ ∀ a, f₁ a ∈ agreeOn D S)) ≤ bad

theorem mca_iff_forall_mcaFor [Finite E] {D : Submodule E (ι → E)} {e bad : ℕ} :
    MCA D e bad ↔ ∀ (R : Type) [Finite R], MCAFor D e R bad := Iff.rfl

theorem MCA.mcaFor [Finite E] {D : Submodule E (ι → E)} {e bad : ℕ}
    (h : MCA D e bad) (R : Type) [Finite R] : MCAFor D e R bad := h R

/-- The family of subspaces that belongs to a code, a radius and a set of rows. It is indexed by the
sets S of all but at most e positions; the subspace of S holds the interleaved words all of whose
rows agree on S with words of the code. -/
def agreeFam (D : Submodule E (ι → E)) (e : ℕ) (R : Type) :
    {S : Finset ι // Fintype.card ι ≤ S.card + e} → Submodule E (R → ι → E) :=
  rows R fun s => agreeOn D s.1

omit [Fintype ι] in
theorem sum_smul_row {I R : Type} [Fintype I] (c : I → E) (f : I → R → ι → E) (a : R) :
    (∑ i, c i • f i) a = ∑ i, c i • f i a := by
  simp only [Finset.sum_apply, Pi.smul_apply]

/-- "Bad" for a code is "bad" for its family of subspaces. This carries the bounds of part 2 over to
codes. -/
theorem bad_iff_badFor {I R : Type} [Fintype I] {D : Submodule E (ι → E)} {e : ℕ}
    {c : I → E} {f : I → R → ι → E} :
    Bad D e c f ↔ BadFor (agreeFam D e R) c f := by
  constructor
  · rintro ⟨S, hS, h1, i, a, h2⟩
    exact ⟨⟨S, hS⟩, fun a => by rw [sum_smul_row]; exact h1 a, i, fun h => h2 (h a)⟩
  · rintro ⟨⟨S, hS⟩, h1, i, h2⟩
    refine ⟨S, hS, fun a => ?_, i, ?_⟩
    · rw [← sum_smul_row]
      exact h1 a
    · by_contra hall
      push Not at hall
      exact h2 hall

/-- Mutual correlated agreement on lines gives the bound for lines of part 2, for the family of
subspaces of the code. -/
theorem MCAFor.lineBound [Finite E] {D : Submodule E (ι → E)} {e bad : ℕ}
    {R : Type} (h : MCAFor D e R bad) :
    LineBound (agreeFam D e R) bad := fun f₀ f₁ =>
  (cnt_mono fun _ ⟨⟨S, hS⟩, h1, h2⟩ => ⟨S, hS, h1, h2⟩).trans (h f₀ f₁)

/-- A table of interleaved words is an interleaved word with more rows. So `h`, for the rows R' × R,
gives the bound for lines of part 2 (`LineBound`) for tables, with the rows R', of interleaved words
with the rows R. -/
theorem MCAFor.lineBound_rows
    [Finite E] {D : Submodule E (ι → E)} {e bad : ℕ} {R' R : Type} (h : MCAFor D e (R' × R) bad) :
    LineBound (rows R' (agreeFam D e R)) bad := fun f₀ f₁ =>
  (cnt_mono fun _ ⟨⟨S, hS⟩, h1, h2⟩ =>
    ⟨S, hS, fun p => h1 p.1 p.2,
      fun hb => h2 ⟨fun a b => hb.1 (a, b), fun a b => hb.2 (a, b)⟩⟩).trans
    (h (fun p => f₀ p.1 p.2) (fun p => f₁ p.1 p.2))

/-! ### Items (b) and (c) for codes -/

section Bounds

variable [Fintype E] {D : Submodule E (ι → E)} {e bad : ℕ} {I R : Type} [Fintype I]

/-- Under `h`, for interleaved words f_i with the rows R and one independent uniform coefficient a_i
for each of them:
(number of bad a) · (q - 1) ≤ bad · q^|I|, that is, a is bad with probability at most (bad / q) (1 -
1/q)^(-1). -/
theorem MCAFor.cnt_bad_mul (h : MCAFor D e R bad) (f : I → R → ι → E) :
    cnt (fun a : I → E => Bad D e a f) * (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I := by
  simp only [bad_iff_badFor]
  exact h.lineBound.cnt_badFor_mul f

/-- Under `h`, `MCAFor.cnt_bad_mul` for the coefficients (1, a): the word f₀ has the coefficient 1,
each of the words f_i an independent uniform one. -/
theorem MCAFor.cnt_bad_one_mul (h : MCAFor D e R bad) (f₀ : R → ι → E) (f : I → R → ι → E) :
    cnt (fun a : I → E => Bad D e (fun o : Option I => o.elim 1 a) (fun o => o.elim f₀ f)) *
        (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I := by
  simp only [bad_iff_badFor]
  exact h.lineBound.cnt_badFor_one_mul f₀ f

/-- Under `h`, independent coefficients cost at most twice the error of a line:
(number of bad a) · q ≤ 2 · bad · q^|I|. -/
theorem MCAFor.cnt_bad_mul_two (h : MCAFor D e R bad) (f : I → R → ι → E) :
    cnt (fun a : I → E => Bad D e a f) * Fintype.card E ≤
      2 * bad * Fintype.card E ^ Fintype.card I := by
  rw [mul_assoc]
  exact mul_le_two_mul_of_mul_pred_le Fintype.one_lt_card (h.cnt_bad_mul f)

/-- `MCAFor.cnt_bad_mul_two` with a first word of coefficient 1. -/
theorem MCAFor.cnt_bad_one_mul_two (h : MCAFor D e R bad) (f₀ : R → ι → E) (f : I → R → ι → E) :
    cnt (fun a : I → E => Bad D e (fun o : Option I => o.elim 1 a) (fun o => o.elim f₀ f)) *
        Fintype.card E ≤
      2 * bad * Fintype.card E ^ Fintype.card I := by
  rw [mul_assoc]
  exact mul_le_two_mul_of_mul_pred_le Fintype.one_lt_card (h.cnt_bad_one_mul f₀ f)

/-- `MCAFor.cnt_bad_mul_two` as a number of vectors: under `h`, at most 2 · bad · q^(|I| - 1) of the
q^|I| vectors a are bad. (If there is no word, |I| - 1 is read as 0; then no vector is bad.) -/
theorem MCAFor.cnt_bad_le (h : MCAFor D e R bad) (f : I → R → ι → E) :
    cnt (fun a : I → E => Bad D e a f) ≤ 2 * bad * Fintype.card E ^ (Fintype.card I - 1) :=
  Alg.le_mul_pow_pred Fintype.card_pos (h.cnt_bad_mul_two f)

theorem MCAFor.cnt_bad_one_le (h : MCAFor D e R bad) (f₀ : R → ι → E) (f : I → R → ι → E) :
    cnt (fun a : I → E => Bad D e (fun o : Option I => o.elim 1 a) (fun o => o.elim f₀ f))
      ≤ 2 * bad * Fintype.card E ^ (Fintype.card I - 1) :=
  Alg.le_mul_pow_pred Fintype.card_pos (h.cnt_bad_one_mul_two f₀ f)

/-- The coefficients eq(γ, ·). Let c j bound the number of bad θ for lines of interleaved words with
2^j · |R| rows, for every j < k. Then for all interleaved words f_v, v ∈ {0,1}^k, with the rows R:
(number of γ ∈ E^k such that (eq(γ, v))_v is bad) · q ≤ (c 0 + ... + c (k - 1)) · q^k. -/
theorem cnt_bad_eqk_mul_sum (c : ℕ → ℕ) (k : ℕ)
    (h : ∀ j < k, MCAFor D e ((Fin j → Bool) × R) (c j)) (f : (Fin k → Bool) → R → ι → E) :
    cnt (fun γ : Fin k → E => Bad D e (Alg.eqk γ) f) * Fintype.card E ≤
      (∑ j ∈ range k, c j) * Fintype.card E ^ k := by
  simp only [bad_iff_badFor]
  exact cnt_badFor_eqk_mul (agreeFam D e R) c k (fun j hj => (h j hj).lineBound_rows) f

/-- Under `h`, for a finite set R of rows, the coefficients eq(γ, ·) on 2^k words cost at
most k times the error of a line: (number of bad γ) · q ≤ k · bad · q^k. -/
theorem MCA.cnt_bad_eqk_mul [Finite R] (h : MCA D e bad) (k : ℕ) (f : (Fin k → Bool) → R → ι → E) :
    cnt (fun γ : Fin k → E => Bad D e (Alg.eqk γ) f) * Fintype.card E ≤
      k * bad * Fintype.card E ^ k := by
  have h1 := cnt_bad_eqk_mul_sum (fun _ => bad) k (fun j _ => h.mcaFor ((Fin j → Bool) × R)) f
  rwa [sum_const, card_range, smul_eq_mul] at h1

/-- `MCA.cnt_bad_eqk_mul` as a number of points: under `h`, for a finite set R of rows, at most
k · bad · q^(k - 1) of the q^k points γ are bad. (For k = 0 the bound is 0.) -/
theorem MCA.cnt_bad_eqk_le [Finite R] (h : MCA D e bad) (k : ℕ) (f : (Fin k → Bool) → R → ι → E) :
    cnt (fun γ : Fin k → E => Bad D e (Alg.eqk γ) f) ≤ k * bad * Fintype.card E ^ (k - 1) :=
  Alg.le_mul_pow_pred Fintype.card_pos (h.cnt_bad_eqk_mul k f)

end Bounds

/-! ### Item (a): what "not bad" gives -/

section NotBad

variable {D : Submodule E (ι → E)} {e : ℕ} {I R : Type} [Fintype I]

/-- If c is not bad and every row of ∑ c_i f_i agrees with the code on the large set S, then so does
every row of every f_i, on the same S.
This is the definition of "bad", in contrapositive form. -/
theorem mem_agreeOn_of_not_bad {c : I → E} {f : I → R → ι → E} (hc : ¬ Bad D e c f) {S : Finset ι}
    (hS : Fintype.card ι ≤ S.card + e) (h : ∀ a, ∑ i, c i • f i a ∈ agreeOn D S) (i : I) (a : R) :
    f i a ∈ agreeOn D S := by
  by_contra hia
  exact hc ⟨S, hS, h, i, a, hia⟩

/-- If c is not bad and ∑ c_i f_i is close to the interleaved code, then the table of all f_i is
close to the interleaved code. So a far table has a far combination, unless c is bad. -/
theorem Close.of_comb_of_not_bad {c : I → E} {f : I → R → ι → E} (hc : ¬ Bad D e c f)
    (h : Close D e fun a => ∑ i, c i • f i a) : Close D e fun p : I × R => f p.1 p.2 := by
  obtain ⟨S, hS, hf⟩ := h
  exact ⟨S, hS, fun p => mem_agreeOn_of_not_bad hc hS hf p.1 p.2⟩

/-- What "not bad" gives. Let the code have minimum distance at least d (`MinDist`), let e < d, and
let c be not bad for the interleaved words f_i. Then the tables u of words of the code that are
close to ∑ c_i f_i are exactly the ∑ c_i U_i, where (U_i)_i is a table of words of the code that is
close to (f_i)_i. -/
theorem close_comb_iff_of_not_bad {d : ℕ} (hd : MinDist D d) (he : e < d) {c : I → E}
    {f : I → R → ι → E} (hc : ¬ Bad D e c f) {u : R → ι → E} (hu : ∀ a, u a ∈ D) :
    (∃ S : Finset ι, Fintype.card ι ≤ S.card + e ∧ ∀ j ∈ S, ∀ a, (∑ i, c i • f i a) j = u a j) ↔
    ∃ U : I → R → ι → E,
      (∀ i a, U i a ∈ D) ∧
      (∃ S : Finset ι, Fintype.card ι ≤ S.card + e ∧ ∀ j ∈ S, ∀ i a, f i a j = U i a j) ∧
      ∀ a, u a = ∑ i, c i • U i a := by
  have hcomb : ∀ (U : I → R → ι → E) (S : Finset ι), (∀ j ∈ S, ∀ i a, f i a j = U i a j) →
      ∀ j ∈ S, ∀ a, (∑ i, c i • f i a) j = (∑ i, c i • U i a) j := by
    intro U S hfU j hj a
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact sum_congr rfl fun i _ => by rw [hfU j hj i a]
  constructor
  · rintro ⟨S, hS, hfu⟩
    have hmem : ∀ i a, f i a ∈ agreeOn D S :=
      mem_agreeOn_of_not_bad hc hS fun a => ⟨u a, hu a, fun j hj => hfu j hj a⟩
    choose U hU hfU using fun i a => mem_agreeOn.mp (hmem i a)
    refine ⟨U, hU, ⟨S, hS, fun j hj i a => hfU i a j hj⟩, fun a => ?_⟩
    refine hd.eq_of_agree (hu a) (D.sum_mem fun i _ => D.smul_mem _ (hU i a)) (S := S)
      (by omega) fun j hj => ?_
    rw [← hfu j hj a]
    exact hcomb U S (fun j hj i a => hfU i a j hj) j hj a
  · rintro ⟨U, -, ⟨S, hS, hfU⟩, huU⟩
    exact ⟨S, hS, fun j hj a => by rw [huU a]; exact hcomb U S hfU j hj a⟩

/-- For a far table, a message of the verifier that yields a close combination yields a bad
coefficient vector. Here c maps the verifier's message to the coefficient vector. -/
theorem cnt_close_comb_le_cnt_bad {Γ : Type} [Finite Γ] (c : Γ → I → E) {f : I → R → ι → E}
    (hf : ¬ Close D e fun p : I × R => f p.1 p.2) :
    cnt (fun g : Γ => Close D e fun a => ∑ i, c g i • f i a) ≤ cnt (fun g : Γ => Bad D e (c g) f) :=
  cnt_mono fun _ hg => by
    by_contra hb
    exact hf (Close.of_comb_of_not_bad hb hg)

end NotBad

/-! ### Far tables: for how many coefficient vectors the combination is close -/

section Far

variable [Fintype E] {D : Submodule E (ι → E)} {e bad : ℕ} {I R : Type} [Fintype I]

omit [Fintype E] [Fintype I] in
/-- Under `h`: if the pair (f₀, f₁) is far from the interleaved code, then f₀ + θ f₁
is close to it for at most `bad` values of θ. -/
theorem MCAFor.cnt_close_line
    [Finite E] (h : MCAFor D e R bad) {f₀ f₁ : R → ι → E} (hf : ¬ Close D e (Sum.elim f₀ f₁)) :
    cnt (fun θ : E => Close D e fun r => f₀ r + θ • f₁ r) ≤ bad :=
  (cnt_mono fun _ ⟨S, hS, hl⟩ =>
    ⟨S, hS, hl, fun hb => hf (close_sumElim_iff.mpr ⟨S, hS, hb.1, hb.2⟩)⟩).trans (h f₀ f₁)

/-- Under `h`: if the table of the words f_i is far from the interleaved code, then
∑ a_i f_i is close to it for a fraction of at most (bad / q) (1 - 1/q)^(-1) of the vectors a. -/
theorem MCAFor.cnt_close_comb_mul
    (h : MCAFor D e R bad) {f : I → R → ι → E} (hf : ¬ Close D e fun p : I × R => f p.1 p.2) :
    cnt (fun a : I → E => Close D e fun r => ∑ i, a i • f i r) * (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I :=
  (Nat.mul_le_mul_right _ (cnt_close_comb_le_cnt_bad (fun a => a) hf)).trans (h.cnt_bad_mul f)

/-- Under `h`: if the table of f₀ and the words f_i is far from the interleaved code,
then f₀ + ∑ a_i f_i is close to it for a fraction of at most (bad / q) (1 - 1/q)^(-1) of the vectors
a. -/
theorem MCAFor.cnt_close_one_comb_mul (h : MCAFor D e R bad) {f₀ : R → ι → E} {f : I → R → ι → E}
    (hf : ¬ Close D e fun p : Option I × R => (p.1.elim f₀ f) p.2) :
    cnt (fun a : I → E => Close D e fun r => f₀ r + ∑ i, a i • f i r) * (Fintype.card E - 1)
      ≤ bad * Fintype.card E ^ Fintype.card I := by
  have h1 := cnt_close_comb_le_cnt_bad
    (D := D) (e := e) (fun (a : I → E) (o : Option I) => o.elim 1 a) (f := fun o => o.elim f₀ f) hf
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, one_smul] at h1
  exact (Nat.mul_le_mul_right _ h1).trans (h.cnt_bad_one_mul f₀ f)

/-- `MCAFor.cnt_close_one_comb_mul` with the factor 2 in place of (1 - 1/q)^(-1). -/
theorem MCAFor.cnt_close_one_comb_mul_two (h : MCAFor D e R bad) {f₀ : R → ι → E}
    {f : I → R → ι → E} (hf : ¬ Close D e fun p : Option I × R => (p.1.elim f₀ f) p.2) :
    cnt (fun a : I → E => Close D e fun r => f₀ r + ∑ i, a i • f i r) * Fintype.card E ≤
      2 * bad * Fintype.card E ^ Fintype.card I := by
  rw [mul_assoc]
  exact mul_le_two_mul_of_mul_pred_le Fintype.one_lt_card (h.cnt_close_one_comb_mul hf)

/-- Under `h`: if the table of the words f_i is far from the interleaved code, then
∑ a_i f_i is close to it for a fraction of at most 2 · bad / q of the vectors a. -/
theorem MCAFor.cnt_close_comb_mul_two
    (h : MCAFor D e R bad) {f : I → R → ι → E} (hf : ¬ Close D e fun p : I × R => f p.1 p.2) :
    cnt (fun a : I → E => Close D e fun r => ∑ i, a i • f i r) * Fintype.card E ≤
      2 * bad * Fintype.card E ^ Fintype.card I :=
  (Nat.mul_le_mul_right _ (cnt_close_comb_le_cnt_bad (fun a => a) hf)).trans (h.cnt_bad_mul_two f)

/-- Far tables: for how many points γ the fold is close. Let c j bound the number of bad θ for lines
of interleaved words with 2^j · |R| rows, for every j < k. If the table of the 2^k words f_v is far
from the interleaved code, then ∑ eq(γ, v) f_v is close to it for a fraction of at most (c 0 + ... +
c (k - 1)) / q of the points γ. -/
theorem cnt_close_eqk_mul_sum (c : ℕ → ℕ) (k : ℕ)
    (h : ∀ j < k, MCAFor D e ((Fin j → Bool) × R) (c j)) {f : (Fin k → Bool) → R → ι → E}
    (hf : ¬ Close D e fun p : (Fin k → Bool) × R => f p.1 p.2) :
    cnt (fun γ : Fin k → E => Close D e fun r => ∑ v, Alg.eqk γ v • f v r) * Fintype.card E ≤
      (∑ j ∈ range k, c j) * Fintype.card E ^ k :=
  (Nat.mul_le_mul_right _ (cnt_close_comb_le_cnt_bad (fun γ : Fin k → E => Alg.eqk γ) hf)).trans
    (cnt_bad_eqk_mul_sum c k h f)

/-- `cnt_close_eqk_mul_sum` with one count for every number of rows (`MCA D e bad`, R finite): a
fraction of at most k · bad / q of the points γ. -/
theorem MCA.cnt_close_eqk_mul [Finite R] (h : MCA D e bad) (k : ℕ) {f : (Fin k → Bool) → R → ι → E}
    (hf : ¬ Close D e fun p : (Fin k → Bool) × R => f p.1 p.2) :
    cnt (fun γ : Fin k → E => Close D e fun r => ∑ v, Alg.eqk γ v • f v r) * Fintype.card E ≤
      k * bad * Fintype.card E ^ k :=
  (Nat.mul_le_mul_right _ (cnt_close_comb_le_cnt_bad (fun γ : Fin k → E => Alg.eqk γ) hf)).trans
    (h.cnt_bad_eqk_mul k f)

/-- `MCA.cnt_close_eqk_mul` as a number of points: at most k · bad · q^(k - 1). -/
theorem MCA.cnt_close_eqk_le [Finite R] (h : MCA D e bad) (k : ℕ) {f : (Fin k → Bool) → R → ι → E}
    (hf : ¬ Close D e fun p : (Fin k → Bool) × R => f p.1 p.2) :
    cnt (fun γ : Fin k → E => Close D e fun r => ∑ v, Alg.eqk γ v • f v r) ≤
      k * bad * Fintype.card E ^ (k - 1) :=
  Alg.le_mul_pow_pred Fintype.card_pos (h.cnt_close_eqk_mul k hf)

end Far

/-! ## 4. Words over the small field (item (f)) -/

section SmallField

variable {F : Type} [Field F] [Algebra F E]

/-- There is an F-linear map from E to F that is the identity on F. -/
theorem exists_form_algebraMap (F E : Type) [Field F] [Field E] [Algebra F E] :
    ∃ φ : E →ₗ[F] F, ∀ x : F, φ (algebraMap F E x) = x := by
  obtain ⟨φ, hφ⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  exact ⟨φ, fun x => LinearMap.congr_fun hφ x⟩

omit [Fintype ι] in
/-- For one word; an interleaved word is treated row by row. A word over F agrees on S with a word
of the extension code if and only if it agrees on S with a word of the code.
(In the proof an F-linear map from E to F that fixes F is applied to every symbol of the word of the
extension code.) -/
theorem liftWord_mem_agreeOn_iff {C : Submodule F (ι → F)} {S : Finset ι} {w : ι → F} :
    liftWord E w ∈ agreeOn (extendCode E C) S ↔ w ∈ agreeOn C S := by
  constructor
  · rintro ⟨u, hu, hwu⟩
    obtain ⟨φ, hφ⟩ := exists_form_algebraMap F E
    refine ⟨fun j => φ (u j), form_comp_mem hu φ, fun j hj => ?_⟩
    show w j = φ (u j)
    rw [← hwu j hj]
    exact (hφ (w j)).symm
  · rintro ⟨u, hu, hwu⟩
    exact ⟨liftWord E u,
      liftWord_mem_extendCode hu,
      fun j hj => congrArg (algebraMap F E) (hwu j hj)⟩

/-- Hence a table over F is close to the interleaved extension code if and
only if it is close to the interleaved code. -/
theorem close_liftWord_iff {C : Submodule F (ι → F)} {e : ℕ} {R : Type} {T : R → ι → F} :
    Close (extendCode E C) e (fun r => liftWord E (T r)) ↔ Close C e T :=
  exists_congr fun _ => and_congr_right fun _ => forall_congr' fun _ => liftWord_mem_agreeOn_iff

/-- For one word; an interleaved word is treated row by row. Let the code have minimum distance at
least d (`MinDist`), and let e < d. A word of the extension code that agrees with a word w over F on
all but at most e positions is itself a word of the code, read over E. -/
theorem exists_liftWord_eq_of_agree {C : Submodule F (ι → F)} {d e : ℕ} (hd : MinDist C d)
    (he : e < d) {w : ι → F} {u : ι → E} (hu : u ∈ extendCode E C) {S : Finset ι}
    (hS : Fintype.card ι ≤ S.card + e) (h : ∀ j ∈ S, liftWord E w j = u j) :
    ∃ u' ∈ C, u = liftWord E u' := by
  obtain ⟨u', hu', hwu'⟩ :=
    liftWord_mem_agreeOn_iff.mp (⟨u, hu, h⟩ : liftWord E w ∈ agreeOn (extendCode E C) S)
  refine ⟨u', hu',
    hd.extendCode.eq_of_agree hu (liftWord_mem_extendCode hu') (S := S) (by omega) fun j hj => ?_⟩
  rw [← h j hj]
  exact congrArg (algebraMap F E) (hwu' j hj)

/-! ## 5. The fold of a table that does not decode; agreement with words of the code -/

/-- Fold of a table that does not decode. Let c j bound the number of bad θ for lines of interleaved
words over E with 2^j rows, for the extension code and every j < k. Let T be a table over F with 2^k
rows that is not within e columns of a table of words of the code C. Then its fold ∑_r eq(γ, r)
T[r], a word over E, is within e positions of a word of the extension code for a fraction of at most
(c 0 + ... + c (k - 1)) / q of the points γ ∈ E^k. -/
theorem cnt_close_fold_mul_sum [Fintype E] {C : Submodule F (ι → F)} {e : ℕ} (c : ℕ → ℕ) (k : ℕ)
    (h : ∀ j < k, MCAFor (extendCode E C) e ((Fin j → Bool) × Unit) (c j))
    {T : (Fin k → Bool) → ι → F} (hT : ¬ Close C e T) :
    cnt (fun γ : Fin k → E =>
          Close (extendCode E C) e fun _ : Unit => ∑ r, Alg.eqk γ r • liftWord E (T r)) *
        Fintype.card E ≤
      (∑ j ∈ range k, c j) * Fintype.card E ^ k :=
  cnt_close_eqk_mul_sum (R := Unit) c k h (f := fun r _ => liftWord E (T r)) fun hc =>
    hT (close_liftWord_iff.mp (hc.comp fun r => (r, ())))

/-- `cnt_close_fold_mul_sum` with one count for every number of rows: a fraction of at most k ·
bad / q of the points γ ∈ E^k. -/
theorem MCA.cnt_close_fold_mul [Fintype E] {C : Submodule F (ι → F)} {e bad : ℕ}
    (h : MCA (extendCode E C) e bad) (k : ℕ) {T : (Fin k → Bool) → ι → F} (hT : ¬ Close C e T) :
    cnt (fun γ : Fin k → E =>
          Close (extendCode E C) e fun _ : Unit => ∑ r, Alg.eqk γ r • liftWord E (T r)) *
        Fintype.card E ≤
      k * bad * Fintype.card E ^ k :=
  h.cnt_close_eqk_mul (R := Unit) k (f := fun r _ => liftWord E (T r)) fun hc =>
    hT (close_liftWord_iff.mp (hc.comp fun r => (r, ())))

/-- `MCA.cnt_close_fold_mul` as a number of points: at most k · bad · q^(k - 1) of the q^k points
γ. -/
theorem MCA.cnt_close_fold [Fintype E] {C : Submodule F (ι → F)} {e bad : ℕ}
    (h : MCA (extendCode E C) e bad) (k : ℕ) {T : (Fin k → Bool) → ι → F} (hT : ¬ Close C e T) :
    cnt (fun γ : Fin k → E =>
        Close (extendCode E C) e fun _ : Unit => ∑ r, Alg.eqk γ r • liftWord E (T r)) ≤
      k * bad * Fintype.card E ^ (k - 1) :=
  Alg.le_mul_pow_pred Fintype.card_pos (h.cnt_close_fold_mul k hT)

end SmallField

section Agreement

variable {D : Submodule E (ι → E)} {e d : ℕ}

/-- Closeness in terms of the number of columns that differ: an interleaved word is close if and
only if it differs from some table of words of the code in at most e columns. -/
theorem close_iff_cnt {R : Type} {f : R → ι → E} :
    Close D e f ↔ ∃ g : R → ι → E, (∀ a, g a ∈ D) ∧ cnt (fun j => ∃ a, f a j ≠ g a j) ≤ e := by
  classical
  constructor
  · intro h
    obtain ⟨g, S, hg, hS, hfg⟩ := h.exists_table
    refine ⟨g, hg, ?_⟩
    have h1 := cnt_add_card_le (P := fun j => ∃ a, f a j ≠ g a j)
      (S := S) fun j hj ⟨a, ha⟩ => ha (hfg j hj a)
    omega
  · rintro ⟨g, hg, hcnt⟩
    refine ⟨univ.filter fun j => ¬ ∃ a, f a j ≠ g a j, ?_, fun a => ⟨g a, hg a, fun j hj => ?_⟩⟩
    · have h1 := cnt_add_cnt_not fun j => ∃ a, f a j ≠ g a j
      rw [← cnt_eq_card_filter]
      omega
    · by_contra hne
      exact (mem_filter.mp hj).2 ⟨a, hne⟩

/-- If the word w is not within e positions of a word of the code, then every word u of the code
agrees with w in fewer than n - e positions. -/
theorem cnt_agree_lt_of_not_close
    {w : ι → E} (h : ¬ Close D e fun _ : Unit => w) {u : ι → E} (hu : u ∈ D) :
    cnt (fun j => u j = w j) + e < Fintype.card ι := by
  classical
  by_contra hcon
  refine h
    ⟨univ.filter fun j => u j = w j, ?_, fun _ => ⟨u, hu, fun j hj => (mem_filter.mp hj).2.symm⟩⟩
  rw [← cnt_eq_card_filter]
  omega

/-- The counting step of `cnt_agree_comb_add_le`. Let w differ from u' in at most e positions, and
let u - u' have at least d non-zero symbols. Then u agrees with w in at most n - d + e positions:
where it does, either w differs from u', or u - u' is zero. -/
theorem cnt_agree_add_le {w u' u : ι → E} (hw : cnt (fun j => w j ≠ u' j) ≤ e)
    (hd : d ≤ cnt (fun j => (u - u') j ≠ 0)) :
    cnt (fun j => u j = w j) + d ≤ Fintype.card ι + e := by
  have h1 : cnt (fun j => u j = w j) ≤ cnt (fun j => w j ≠ u' j ∨ (u - u') j = 0) :=
    cnt_mono fun j hj => by
      by_cases hwj : w j = u' j
      · exact Or.inr (by rw [Pi.sub_apply, hj, hwj, sub_self])
      · exact Or.inl hwj
  have h2 : cnt (fun j => w j ≠ u' j ∨ (u - u') j = 0) ≤
      cnt (fun j => w j ≠ u' j) + cnt (fun j => (u - u') j = 0) :=
    Alg.count_or_le _ _
  have h3 := cnt_add_cnt_not fun j => (u - u') j = 0
  have h4 : cnt (fun j => ¬ (u - u') j = 0) = cnt (fun j => (u - u') j ≠ 0) := rfl
  omega

/-- If two tables agree in a column, then so do their combinations. So the combinations differ in at
most as many positions as the tables have different columns. -/
theorem cnt_comb_ne_le {R : Type} [Fintype R] (T U : R → ι → E) (a : R → E) :
    cnt (fun j => (∑ r, a r • T r) j ≠ (∑ r, a r • U r) j) ≤ cnt (fun j => ∃ r, T r j ≠ U r j) :=
  cnt_mono fun j hj => by
    by_contra hall
    push Not at hall
    refine hj ?_
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact sum_congr rfl fun r _ => by rw [hall r]

/-- Let the table T differ in at most e columns from the table U of words of a code of distance d.
Then for all coefficients a, every word u of the code other than ∑ a_r U_r agrees with the
combination ∑ a_r T_r in at most n - d + e positions. -/
theorem cnt_agree_comb_add_le {R : Type} [Fintype R] (hd : MinDist D d) {T U : R → ι → E}
    (hU : ∀ r, U r ∈ D) (hTU : cnt (fun j => ∃ r, T r j ≠ U r j) ≤ e) (a : R → E) {u : ι → E}
    (hu : u ∈ D) (hne : u ≠ ∑ r, a r • U r) :
    cnt (fun j => u j = (∑ r, a r • T r) j) + d ≤ Fintype.card ι + e :=
  cnt_agree_add_le ((cnt_comb_ne_le T U a).trans hTU)
    (hd _ (D.sub_mem hu (D.sum_mem fun r _ => D.smul_mem _ (hU r))) (sub_ne_zero.mpr hne))

/-- `cnt_agree_comb_add_le` for a generator matrix, over one field. Let every non-zero vector have
an image under G with at least d non-zero symbols, and let the table T differ in at most e columns
from the table with the rows G M_r. Then for all coefficients a and every vector u other than ∑ a_r
M_r, the word G u agrees with ∑ a_r T_r in at most n - d + e positions. -/
theorem cnt_agree_mulVec_add_le {R κ : Type} [Fintype R] [Fintype κ] {G : Matrix ι κ E}
    (hG : ∀ v : κ → E, v ≠ 0 → d ≤ cnt (fun j => G.mulVec v j ≠ 0)) {T : R → ι → E}
    {M : R → κ → E} (hTM : cnt (fun j => ∃ r, T r j ≠ G.mulVec (M r) j) ≤ e) (a : R → E)
    {u : κ → E} (hne : u ≠ ∑ r, a r • M r) :
    cnt (fun j => G.mulVec u j = (∑ r, a r • T r) j) + d ≤ Fintype.card ι + e := by
  have hlin : G.mulVec (∑ r, a r • M r) = ∑ r, a r • G.mulVec (M r) := by
    have h1 := map_sum G.mulVecLin (fun r => a r • M r) univ
    simp only [map_smul, Matrix.mulVecLin_apply] at h1
    exact h1
  refine cnt_agree_add_le (u' := ∑ r, a r • G.mulVec (M r)) ((cnt_comb_ne_le T _ a).trans hTM) ?_
  rw [← hlin, ← Matrix.mulVec_sub]
  exact hG _ (sub_ne_zero.mpr hne)

/-- `cnt_agree_mulVec_add_le` over two fields: the generator matrix G, the table T and the messages
M_r are over F, the coefficients a and the vector u over E. -/
theorem cnt_agree_mulVec_map_add_le {F R κ : Type} [Field F] [Algebra F E] [Fintype R] [Fintype κ]
    {G : Matrix ι κ F} (hG : ∀ v : κ → F, v ≠ 0 → d ≤ cnt (fun j => G.mulVec v j ≠ 0))
    {T : R → ι → F} {M : R → κ → F} (hTM : cnt (fun j => ∃ r, T r j ≠ G.mulVec (M r) j) ≤ e)
    (a : R → E) {u : κ → E} (hne : u ≠ ∑ r, a r • liftWord E (M r)) :
    cnt (fun j => (G.map (algebraMap F E)).mulVec u j = (∑ r, a r • liftWord E (T r)) j) + d ≤
      Fintype.card ι + e := by
  refine cnt_agree_mulVec_add_le (dist_mulVec_map hG) (M := fun r => liftWord E (M r)) ?_ a hne
  refine (cnt_mono ?_).trans hTM
  rintro j ⟨r, hr⟩
  refine ⟨r, fun h => hr ?_⟩
  rw [mulVec_map_liftWord]
  exact congrArg (algebraMap F E) h

end Agreement

end Codes

end Code
