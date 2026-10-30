-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/SubBelow.lean: bounds on round-by-round errors: "every error, as a probability, is at most c"
when the verifier draws from subsets (Ior/Sub.lean).

Definitions, statements (in `Iop.Spec`) and their proofs, in one file.
A list of errors (`Err`, Iop/Rbr.lean) has for each round a count of values of the verifier message,
not a probability. σ (`Samplers`, Iop/Pull.lean) has for each round a map φ : Src → Chal; the
verifier message is φ of a uniform element of Src.
After a restriction the error list has the same counts (`Err.same`), and the sets of verifier
messages are smaller; so, as fractions, the errors of the restricted rounds grow. `Err.Below ε c`
(Iop/InteractiveOracleProof.lean) says: in every round, count ≤ c · (number of verifier messages). These errors are
the entries of a list ε (`Err s`, Iop/Rbr.lean), a variable of each statement that speaks of them:
that a protocol is sound at such a list is no statement of this file; that tie, from ε to `Err.same
σ ε`, is `Spec.know_sub` (Ior/Sub.lean), under `σ.Inj` and `R.red.Know` at ε (that condition itself
asks soundness of the parts one level down: the tie carries soundness, it does not found it).
Where a row or docstring below counts the values that can be drawn, Lean counts Src
(`Fintype.card a.Src`); the two numbers agree where φ is injective (`Samplers.Inj`, Ior/Sub.lean),
which no definition or statement of this file asks of every round (`Function.Bijective a.φ` is one
alternative in `Samplers.Thin` and in `Samplers.Fit`).

Main names:
  `σ.Dense κ`: in every round: (number of all verifier messages) ≤ κ · (number of those that can be
    drawn).
  The rules, by parts of a shape:
  `below_keep`: a part that is not restricted keeps its bound.
  `below_dense`: a part with `σ.Dense κ`: a bound c becomes c · κ.
  `below_app`: two parts in a row, each with the bound c.
  So: the parts whose errors are tight (lists of positions) are not restricted and keep their bound;
    the restricted parts are the algebraic ones, whose errors have room for a factor 2
    [no theorem here].
  A rule that needs no room and no cut into parts:
  `σ.Thin`: in every round the verifier draws from all values, or from all but one, and then the
    number of all values is odd (a field of odd characteristic without 0).
  `below_thin`: then a bound 2^-x, x ≥ 1, on all errors is kept as it is: count · 2^x ≤ (an odd
    number) gives count · 2^x ≤ (that number - 1), because the left side is even.
  `σ.Fit ε x`: round by round one of three: all values are drawn; all but one of an odd number; or
    the count has room for a factor 2 (count · 2^(x+1) ≤ number of all values) and at least half of
    all values can be drawn.
  `below_fit`: then the bound 2^-x, x ≥ 1, is kept.
  When a subset is dense:
  `dense_cnt`: {c // P c} has at least half of all values, if at most half of them fail P.
  `dense_nz`: a field without 0, if the field has at least 2 elements (no hypothesis of the
    statement: every field has).
  `dense_pt`: the points (families of field elements) that are not 0 at v flagged coordinates, if 2
    v ≤ |E|.

Limits: beyond the sentence above that is marked "[no theorem here]", this file says nothing on any
protocol.
Terms: lean/GLOSSARY.md.
-/
import Ior.SubProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- In every round the values that can be drawn are at least the fraction 1 / κ of all. (Lean counts
Src: see the head.) -/
def Samplers.Dense : {s : Shape} → Samplers s → ℝ≥0∞ → Prop
  | [], _, _ => True
  | r :: _, (a, σ), κ =>
    (Fintype.card r.Chal : ℝ≥0∞) ≤ κ * (Fintype.card a.Src : ℝ≥0∞) ∧ Samplers.Dense σ κ

/-- All values, or all but one of an odd number. -/
def Samplers.Thin : {s : Shape} → Samplers s → Prop
  | [], _ => True
  | r :: _, (a, σ) =>
    (Function.Bijective a.φ ∨
      (Fintype.card a.Src + 1 = Fintype.card r.Chal ∧ Odd (Fintype.card r.Chal))) ∧
    Samplers.Thin σ

/-- Round by round: all values; all but one of an odd number; or room for a factor 2 in the count,
and at least half of all values. -/
def Samplers.Fit : {s : Shape} → Samplers s → Err s → ℕ → Prop
  | [], _, _, _ => True
  | r :: _, (a, σ), (e, ε), x =>
      (Function.Bijective a.φ ∨
        (Fintype.card a.Src + 1 = Fintype.card r.Chal ∧ Odd (Fintype.card r.Chal)) ∨
        (e * 2 ^ (x + 1) ≤ Fintype.card r.Chal ∧ Fintype.card r.Chal ≤ 2 * Fintype.card a.Src)) ∧
      Samplers.Fit σ ε x

namespace Spec

/-- Under the hypotheses below, a bound 2^-x is kept as it is. -/
def below_fit : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (ε : Err s) (x : ℕ),
    1 ≤ x → σ.Fit ε x → Err.Below ε (2 ^ x : ℝ≥0∞)⁻¹ → Err.Below (Err.same σ ε) (2 ^ x : ℝ≥0∞)⁻¹

def below_thin : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (ε : Err s) (x : ℕ),
    1 ≤ x → σ.Thin → Err.Below ε (2 ^ x : ℝ≥0∞)⁻¹ → Err.Below (Err.same σ ε) (2 ^ x : ℝ≥0∞)⁻¹

def fit_thin : Prop := ∀ (s : Shape) (σ : Samplers s) (ε : Err s) (x : ℕ), σ.Thin → σ.Fit ε x
def fit_dense : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (ε : Err s) (x : ℕ),
    σ.Dense 2 → Err.Below ε (2 ^ (x + 1) : ℝ≥0∞)⁻¹ → σ.Fit ε x
def fit_app : Prop :=
  ∀ (s t : Shape) (σ : Samplers s) (τ : Samplers t) (ε₁ : Err s) (ε₂ : Err t) (x : ℕ),
    σ.Fit ε₁ x → τ.Fit ε₂ x → (σ.app τ).Fit (Err.app ε₁ ε₂) x
def thin_keep : Prop := ∀ s : Shape, (Samplers.keep s).Thin
def thin_app : Prop :=
  ∀ (s t : Shape) (σ : Samplers s) (τ : Samplers t), σ.Thin → τ.Thin → (σ.app τ).Thin

def below_keep : Prop :=
  ∀ (s : Shape) (ε : Err s) (c : ℝ≥0∞), Err.Below ε c → Err.Below (Err.same (Samplers.keep s) ε) c

def below_dense : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (ε : Err s) (c κ : ℝ≥0∞),
    σ.Dense κ → Err.Below ε c → Err.Below (Err.same σ ε) (c * κ)

def below_half : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (ε : Err s) (c : ℝ≥0∞),
    σ.Dense 2 → Err.Below ε (c / 2) → Err.Below (Err.same σ ε) c

def below_app : Prop :=
  ∀ (s t : Shape) (σ : Samplers s) (τ : Samplers t) (ε₁ : Err s) (ε₂ : Err t) (c : ℝ≥0∞),
    Err.Below (Err.same σ ε₁) c → Err.Below (Err.same τ ε₂) c →
    Err.Below (Err.same (σ.app τ) (Err.app ε₁ ε₂)) c

def dense_keep : Prop := ∀ (s : Shape) (κ : ℝ≥0∞), 1 ≤ κ → (Samplers.keep s).Dense κ
def dense_app : Prop :=
  ∀ (s t : Shape) (σ : Samplers s) (τ : Samplers t) (κ : ℝ≥0∞),
    σ.Dense κ → τ.Dense κ → (σ.app τ).Dense κ
def dense_mono : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (κ κ' : ℝ≥0∞), κ ≤ κ' → σ.Dense κ → σ.Dense κ'

/-- A subset that at most half of all values fail. -/
def dense_cnt : Prop :=
  ∀ (C : Type) [Fintype C] (P : C → Prop) [Fintype {c // P c}], 2 * cnt (fun c => ¬ P c) ≤
      Fintype.card C →
    (Fintype.card C : ℝ≥0∞) ≤ 2 * (Fintype.card {c // P c} : ℝ≥0∞)

def card_nz : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E],
    Fintype.card {c : E // c ≠ 0} = Fintype.card E - 1

def dense_nz : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E],
    (Fintype.card E : ℝ≥0∞) ≤ 2 * (Fintype.card {c : E // c ≠ 0} : ℝ≥0∞)

/-- Points that are not 0 at the flagged coordinates. -/
def dense_pt : Prop :=
  ∀ (E ι : Type) [Field E] [Fintype E] [Fintype ι] [DecidableEq ι] (flag : ι → Bool)
      [Fintype {f : ι → E // ∀ i, flag i = true → f i ≠ 0}],
    2 * Fintype.card {i // flag i = true} ≤ Fintype.card E →
    (Fintype.card (ι → E) : ℝ≥0∞) ≤
      2 * (Fintype.card {f : ι → E // ∀ i, flag i = true → f i ≠ 0} : ℝ≥0∞)

end Spec

theorem below_keep : Spec.below_keep
  | [], _, _, _ => trivial
  | _ :: s, (_, ε), c, h => ⟨h.1, below_keep s ε c h.2⟩

theorem below_dense : Spec.below_dense
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (a, σ), (e, ε), c, κ, hd, h => ⟨by
      calc (e : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞) := h.1
        _ ≤ c * (κ * (Fintype.card a.Src : ℝ≥0∞)) := mul_le_mul' le_rfl hd.1
        _ = c * κ * (Fintype.card a.Src : ℝ≥0∞) := (mul_assoc _ _ _).symm,
          below_dense s σ ε c κ hd.2 h.2⟩

theorem below_half : Spec.below_half := fun s σ ε c hd h => by
  have h1 := below_dense s σ ε (c / 2) 2 hd h
  rwa [ENNReal.div_mul_cancel (by norm_num) (by norm_num)] at h1

theorem below_app : Spec.below_app
  | [], _, _, _, _, _, _, _, h => h
  | _ :: s, t, (_, σ), τ, (_, ε₁), ε₂, c, h, h' => ⟨h.1, below_app s t σ τ ε₁ ε₂ c h.2 h'⟩

theorem dense_keep : Spec.dense_keep
  | [], _, _ => trivial
  | r :: s, κ, h => ⟨by
      calc (Fintype.card r.Chal : ℝ≥0∞) = 1 * (Fintype.card r.Chal : ℝ≥0∞) := (one_mul _).symm
        _ ≤ κ * (Fintype.card r.Chal : ℝ≥0∞) := mul_le_mul' h le_rfl, dense_keep s κ h⟩

theorem dense_app : Spec.dense_app
  | [], _, _, _, _, _, h => h
  | _ :: s, t, (_, σ), τ, κ, h, h' => ⟨h.1, dense_app s t σ τ κ h.2 h'⟩

theorem dense_mono : Spec.dense_mono
  | [], _, _, _, _, _ => trivial
  | _ :: s, (_, σ), κ, κ', hk, h => ⟨h.1.trans (mul_le_mul' hk le_rfl), dense_mono s σ κ κ' hk h.2⟩

/-- "count ≤ 2^-x · N" is "count · 2^x ≤ N". -/
theorem le_inv_pow_iff (a N x : ℕ) :
    (a : ℝ≥0∞) ≤ (2 ^ x : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞) ↔ a * 2 ^ x ≤ N := by
  have h2 : (2 ^ x : ℝ≥0∞) ≠ 0 := by positivity
  have h3 : (2 ^ x : ℝ≥0∞) ≠ ⊤ := by simp
  constructor
  · intro h
    have h1 : (a : ℝ≥0∞) * 2 ^ x ≤ (N : ℝ≥0∞) := by
      calc (a : ℝ≥0∞) * 2 ^ x ≤ (2 ^ x : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞) * 2 ^ x := mul_le_mul' h le_rfl
        _ = (N : ℝ≥0∞) := by
          rw [mul_comm (2 ^ x : ℝ≥0∞)⁻¹, mul_assoc, ENNReal.inv_mul_cancel h2 h3, mul_one]
    exact_mod_cast h1
  · intro h
    have h1 : (a : ℝ≥0∞) * 2 ^ x ≤ (N : ℝ≥0∞) := by exact_mod_cast h
    calc
      (a : ℝ≥0∞) = (2 ^ x : ℝ≥0∞)⁻¹ * ((a : ℝ≥0∞) * 2 ^ x) := by
        rw [mul_comm (a : ℝ≥0∞), ← mul_assoc, ENNReal.inv_mul_cancel h2 h3, one_mul]
      _ ≤ (2 ^ x : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞) := mul_le_mul' le_rfl h1

theorem below_fit : Spec.below_fit
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (a, σ), (e, ε), x, hx, hf, h => ⟨by
      have h1 : e * 2 ^ x ≤ Fintype.card r.Chal := (le_inv_pow_iff _ _ _).1 h.1
      refine (le_inv_pow_iff e (Fintype.card a.Src) x).2 ?_
      rcases hf.1 with hb | ⟨hc, ho⟩ | ⟨hr, hd⟩
      · rw [Fintype.card_of_bijective hb]
        exact h1
      · have hev : Even (e * 2 ^ x) := (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_left e
        have hne : e * 2 ^ x ≠ Fintype.card r.Chal := fun he =>
          (Nat.not_even_iff_odd.2 ho) (he ▸ hev)
        omega
      · have h2 : e * 2 ^ (x + 1) = 2 * (e * 2 ^ x) := by ring
        omega, below_fit s σ ε x hx hf.2 h.2⟩

theorem fit_thin : Spec.fit_thin
  | [], _, _, _, _ => trivial
  | _ :: s, (_, σ), (_, ε), x, h => ⟨h.1.imp id Or.inl, fit_thin s σ ε x h.2⟩

theorem fit_dense : Spec.fit_dense
  | [], _, _, _, _, _ => trivial
  | r :: s, (a, σ), (e, ε), x, hd, h => ⟨Or.inr (Or.inr ⟨(le_inv_pow_iff _ _ _).1 h.1, by
      have h1 : ((Fintype.card r.Chal : ℕ) : ℝ≥0∞) ≤ ((2 * Fintype.card a.Src : ℕ) : ℝ≥0∞) := by
        push_cast
        exact hd.1
      exact_mod_cast h1⟩), fit_dense s σ ε x hd.2 h.2⟩

theorem below_thin : Spec.below_thin := fun s σ ε x hx h =>
  below_fit s σ ε x hx (fit_thin s σ ε x h)

theorem fit_app : Spec.fit_app
  | [], _, _, _, _, _, _, _, h => h
  | _ :: s, t, (_, σ), τ, (_, ε₁), ε₂, x, h, h' => ⟨h.1, fit_app s t σ τ ε₁ ε₂ x h.2 h'⟩

theorem thin_keep : Spec.thin_keep
  | [] => trivial
  | _ :: s => ⟨Or.inl Function.bijective_id, thin_keep s⟩

theorem thin_app : Spec.thin_app
  | [], _, _, _, _, h => h
  | _ :: s, t, (_, σ), τ, h, h' => ⟨h.1, thin_app s t σ τ h.2 h'⟩

theorem dense_cnt : Spec.dense_cnt := by
  classical
  intro C _ P _ h
  have h1 : Fintype.card {c // P c} = cnt P := by rw [cnt_eq_card_filter, Fintype.card_subtype]
  have h2 := cnt_add_cnt_not P
  have h3 : Fintype.card C ≤ 2 * Fintype.card {c // P c} := by omega
  exact_mod_cast h3

theorem card_nz : Spec.card_nz := by
  intro E _ _ _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem dense_nz : Spec.dense_nz := by
  intro E _ _ _
  refine dense_cnt E (fun c => c ≠ 0) ?_
  have h1 : cnt (fun c : E => ¬ c ≠ 0) = 1 := by
    rw [cnt_congr (Q := fun c : E => c = 0) fun c => not_not]
    exact cnt_eq_const 0
  rw [h1]
  exact Fintype.one_lt_card

theorem dense_pt : Spec.dense_pt := by
  classical
  intro E ι _ _ _ _ flag _ h
  refine dense_cnt (ι → E) (fun f => ∀ i, flag i = true → f i ≠ 0) ?_
  have hq : 0 < Fintype.card E := Fintype.card_pos
  -- at one coordinate: the points that are 0 there, times |E|, are all points
  have h1 : ∀ i : ι,
      cnt (fun f : ι → E => f i = 0) * Fintype.card E = Fintype.card (ι → E) := fun i => by
    have e := cnt_pi_coord (A := fun _ : ι => E) i (fun c : E => c = 0)
    rw [cnt_eq_const, one_mul] at e
    exact e
  have h2 : cnt (fun f : ι → E => ¬ ∀ i, flag i = true → f i ≠ 0) ≤
      ∑ i : {i // flag i = true}, cnt (fun f : ι → E => f i.1 = 0) := by
    refine le_trans (le_of_eq (cnt_congr fun f => ?_))
      (cnt_exists_le fun (i : {i // flag i = true}) (f : ι → E) => f i.1 = 0)
    constructor
    · intro hf
      by_contra hn
      exact hf fun i hi h0 => hn ⟨⟨i, hi⟩, h0⟩
    · rintro ⟨i, h0⟩ hf
      exact hf i.1 i.2 h0
  refine Nat.le_of_mul_le_mul_right ?_ hq
  calc
    2 * cnt (fun f : ι → E => ¬ ∀ i, flag i = true → f i ≠ 0) * Fintype.card E ≤
        2 * (∑ i : {i // flag i = true}, cnt (fun f : ι → E => f i.1 = 0)) * Fintype.card E :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
    _ = 2 * ∑ i : {i // flag i = true}, cnt (fun f : ι → E => f i.1 = 0) * Fintype.card E := by
      rw [mul_assoc, Finset.sum_mul]
    _ = 2 * ∑ _i : {i // flag i = true}, Fintype.card (ι → E) := by simp only [h1]
    _ = 2 * Fintype.card {i // flag i = true} * Fintype.card (ι → E) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]
    _ ≤ Fintype.card E * Fintype.card (ι → E) := Nat.mul_le_mul_right _ h
    _ = Fintype.card (ι → E) * Fintype.card E := Nat.mul_comm _ _

end Iop
