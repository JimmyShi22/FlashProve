-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFMatKit.lean: tools for key families with a matrix product with weights.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family (`Fam`, Cb/Req/ReqSpec.lean) has one value at each
vertex of a cube; an index atom (`IdxAtom`) is a tensor form on the index matrix (`IdxAtom.at`). A
key of this kind is (an affine form in cells) + ∑_j (public coefficient) ·
(a product of values of cells) · (an entry of a weight tensor of the layer). The weight tensors of
different layers are different index atoms, so the sum has one monomial for each layer, whose
coefficient is 0 in the other layers.

Main names:
  `blk vx w n c fs ia`: the block: the sum atom
    ∑_{j < 2^w} ∑_{k < n} c k ℓ x i j · ∏ fs(ℓ, x, i, j) · (ia k at the vertex (b, j)),
    b = (ℓ | x | i).
  `gVal g X a j i`: the value of an array at the channel j, as a form; the constant 0 if j is
    beyond the width of the array (a sum over 2^w channels runs beyond it).
  `sum_cut`: for n ≤ N, a sum over range N whose terms vanish from n on is the sum over range n.
  `sum_pick`, `sum_odd`, `sum_half`, each under the bound on ℓ of its statement:
    ∑_k [ℓ = k] f k = f ℓ; ∑_k [ℓ = 2 k + 1] f k = f (ℓ / 2) for odd ℓ, 0 for even ℓ;
    ∑_k [ℓ = k / 2] f k = f (2 ℓ) + f (2 ℓ + 1).

Used for the seven families of Cm/TargetSegFFMat.lean.
Limits: nothing here names a family of the model. This file says nothing on the model's keys
(Cm/TargetSegFFMat.lean).
Terms: lean/GLOSSARY.md.
-/
import Cm.SegHeadExp
import Cm.SegPilotAff
import Cm.SegIdxModelProofs
import Cm.SegIdxRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset
open Ex

/-! ## Sums -/

section Sums
variable {M : Type} [AddCommMonoid M]

theorem sum_cut {n N : ℕ} (h : n ≤ N) (f : ℕ → M) (h0 : ∀ j, n ≤ j → j < N → f j = 0) :
    ∑ j ∈ range N, f j = ∑ j ∈ range n, f j :=
  (sum_subset (range_subset_range.2 h) fun j hj hn =>
    h0 j (Nat.le_of_not_lt fun hlt => hn (mem_range.2 hlt)) (mem_range.1 hj)).symm

theorem sum_pick {n l : ℕ} (hl : l < n) (f : ℕ → M) :
    ∑ k ∈ range n, (if l = k then f k else 0) = f l := by
  rw [sum_ite_eq, if_pos (mem_range.2 hl)]

theorem sum_odd {n l : ℕ} (hl : l < 2 * n) (f : ℕ → M) :
    ∑ k ∈ range n, (if l = 2 * k + 1 then f k else 0) = if l % 2 = 1 then f (l / 2) else 0 := by
  split_ifs with h
  · rw [sum_eq_single (l / 2)]
    · rw [if_pos (by omega)]
    · intro k _ hk
      rw [if_neg (by omega)]
    · intro hn
      exact absurd (mem_range.2 (by omega)) hn
  · exact sum_eq_zero fun k _ => if_neg (by omega)

theorem sum_half {n l : ℕ} (hl : l < n) (f : ℕ → M) :
    ∑ k ∈ range (n * 2), (if l = k / 2 then f k else 0) = f (2 * l) + f (2 * l + 1) := by
  rw [Alg.sum_range_mul_add]
  have h : ∀ a ∈ range n, ∑ b ∈ range 2, (if l = (a * 2 + b) / 2 then f (a * 2 + b) else 0) =
      if l = a then f (2 * a) + f (2 * a + 1) else 0 := fun a _ => by
    rw [sum_range_succ, sum_range_one, show (a * 2 + 0) / 2 = a by omega,
      show (a * 2 + 1) / 2 = a by omega, Nat.add_zero, Nat.mul_comm a 2]
    split_ifs
    · rfl
    · exact add_zero 0
  rw [sum_congr rfl h, sum_pick hl fun a => f (2 * a) + f (2 * a + 1)]

end Sums

/-! ## Runs of variables at a vertex (b, j) -/

/-- outer variables: bits of b -/
theorem num_out {a n v w b j : ℕ} (h : a + n ≤ v) (hj : j < 2 ^ w) :
    Src.num (Src.run a n) (v + w) (b * 2 ^ w + j) = b / 2 ^ (v - a - n) % 2 ^ n := by
  rw [num_run a n (by omega), show v + w - a - n = w + (v - a - n) by omega, pow_add,
    ← Nat.div_div_eq_div_mul, (div_mod_of hj).1]

/-- inner variables: bits of j -/
theorem num_in {a n v w b j : ℕ} (ha : v ≤ a) (h : a + n ≤ v + w) :
    Src.num (Src.run a n) (v + w) (b * 2 ^ w + j) = j / 2 ^ (v + w - a - n) % 2 ^ n := by
  rw [num_run a n h]
  obtain ⟨m, hm⟩ : ∃ m, m = v + w - a - n := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, w = m + (n + r) := ⟨w - m - n, by omega⟩
  rw [← hm, hr, pow_add, pow_add,
    show b * (2 ^ m * (2 ^ n * 2 ^ r)) + j = 2 ^ m * (b * 2 ^ r * 2 ^ n) + j by ring,
    Nat.mul_add_div (Nat.two_pow_pos m), Nat.add_comm, Nat.add_mul_mod_self_right]

/-! ## The block -/

section Kit
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

/-- a function of (ℓ, x, i, j) at the vertex B = b · 2^w + j of the inner cube, b = (ℓ | x | i) -/
def at4 {α : Type} (vx w : ℕ) (f : ℕ → ℕ → ℕ → ℕ → α) (B : ℕ) : α :=
  f (dec3 vx (B / 2 ^ w)).1 (dec3 vx (B / 2 ^ w)).2.1 (dec3 vx (B / 2 ^ w)).2.2 (B % 2 ^ w)

theorem at4_eq {α : Type} (vx w : ℕ) (f : ℕ → ℕ → ℕ → ℕ → α) (b : ℕ) {j : ℕ} (hj : j < 2 ^ w) :
    at4 vx w f (b * 2 ^ w + j) = f (dec3 vx b).1 (dec3 vx b).2.1 (dec3 vx b).2.2 j := by
  unfold at4
  rw [(div_mod_of hj).1, (div_mod_of hj).2]

/-- the product of the values of forms that are given as functions of (ℓ, x, i, j) -/
def cellsE (vx w : ℕ) : List (ℕ → ℕ → ℕ → ℕ → CForm E) → Ex0 X E
  | [] => Ex.con 1
  | f :: l => aff0 (at4 vx w f) * cellsE vx w l

/-- The block: a sum atom over w further variables, with one monomial for each of n index atoms. -/
def blk (vx w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → E)
    (fs : List (ℕ → ℕ → ℕ → ℕ → CForm E)) (ia : ℕ → IdxAtom E) : Ex1 X E :=
  sumA (2 + vx + 10) w
    (Ex.pSum n fun k => Ex.sc (fun _ B => at4 vx w (c k) B) (cellsE vx w fs * idx0 (ia k)))

variable (Φ : IdxFmt F) (x₀ : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)

theorem val_cellsE (vx w V B : ℕ) (fs : List (ℕ → ℕ → ℕ → ℕ → CForm E)) :
    Ex0.val Φ x₀ W A (cellsE vx w fs) V B = (fs.map fun f => (at4 vx w f B).val A).prod := by
  induction fs with
  | nil => simp [cellsE, Ex0.val]
  | cons f l ih =>
    unfold Ex0.val at ih ⊢
    rw [cellsE, ev_mul, ih, List.map_cons, List.prod_cons]
    simp [aff0, Atom0.val]

/-- The value of a block at the vertex b = (ℓ | x | i). -/
theorem val_blk (vx w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → E) (fs : List (ℕ → ℕ → ℕ → ℕ → CForm E))
    (ia : ℕ → IdxAtom E) (b : ℕ) :
    Ex1.val Φ x₀ W A (blk vx w n c fs ia) (2 + vx + 10) b =
      ∑ j ∈ range (2 ^ w), ∑ k ∈ range n, c k (dec3 vx b).1 (dec3 vx b).2.1 (dec3 vx b).2.2 j *
        ((fs.map fun f => (f (dec3 vx b).1 (dec3 vx b).2.1 (dec3 vx b).2.2 j).val A).prod *
          (ia k).at Φ W (vtx (2 + vx + 10 + w) (b * 2 ^ w + j))) := by
  unfold blk sumA Ex1.val
  rw [ev_one, val_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  unfold Ex0.val
  rw [ev_pSum]
  refine sum_congr rfl fun k _ => ?_
  rw [ev_sc, ev_mul, at4_eq vx w (c k) b hj']
  have h1 := val_cellsE Φ x₀ W A vx w (2 + vx + 10 + w) (b * 2 ^ w + j) fs
  unfold Ex0.val at h1
  rw [h1]
  congr 2
  · exact congrArg List.prod (List.map_congr_left fun f _ => by rw [at4_eq vx w f b hj'])
  · simp [idx0, Atom0.val]

theorem all_cellsE {Q : Atom0 E → Prop} (vx w : ℕ) {fs : List (ℕ → ℕ → ℕ → ℕ → CForm E)}
    (h : ∀ f ∈ fs, Q (.cell (at4 vx w f))) :
    Ex.All Q (cellsE (X := X) vx w fs) := by
  induction fs with
  | nil => exact All.con 1
  | cons f l ih =>
    exact All.mul (All.one (h f List.mem_cons_self))
      (ih fun f' hf' => h f' (List.mem_cons_of_mem _ hf'))

/-- a block is well formed if its index atoms have their law on the inner cube -/
theorem wf_blk {vx w n : ℕ} (c : ℕ → ℕ → ℕ → ℕ → ℕ → E) (fs : List (ℕ → ℕ → ℕ → ℕ → CForm E))
    {ia : ℕ → IdxAtom E} (h : ∀ k < n, (ia k).OK Φ (2 + vx + 10 + w)) :
    Ex.All (fun a : Atom X E => a.WF Φ (2 + vx + 10)) (blk vx w n c fs ia) :=
  All.one (wf_sum Φ
    (All.pSum fun k hk =>
      All.sc _ (All.mul (all_cellsE vx w fun _ _ => trivial) (All.one (h k hk)))))

/-- every place that a block reads is a place of one of its forms, at indices in range -/
theorem places_blk {vx w n : ℕ} (c : ℕ → ℕ → ℕ → ℕ → ℕ → E) {fs : List (ℕ → ℕ → ℕ → ℕ → CForm E)}
    (ia : ℕ → IdxAtom E) {P : Cb.Place → Prop}
    (h : ∀ f ∈ fs, ∀ l < 2 ^ 2, ∀ x < 2 ^ vx, ∀ i < 2 ^ 10, ∀ j < 2 ^ w, AllPl P (f l x i j)) :
    Ex.All (fun a : Atom X E => ∀ q ∈ a.places (2 + vx + 10), P q) (blk vx w n c fs ia) := by
  refine All.one
    (poly_places
      (All.pSum fun k _ =>
        All.sc _ (All.mul (all_cellsE vx w fun f hf => places_cell0 fun B hB => ?_)
            (All.one (places_idx0 _ _)))))
  have hb : B / 2 ^ w < 2 ^ (2 + vx + 10) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w), ← pow_add]
    exact hB
  exact h f hf _ (dec3_lt hb).1 _ (dec3_lt hb).2.1 _ (dec3_lt hb).2.2
    _ (Nat.mod_lt _ (Nat.two_pow_pos w))

end Kit

/-! ## Values of arrays inside a sum -/

section GVal
variable {E : Type} [Field E] (g : ℕ)

/-- the value of the array X at the channel j; the constant 0 beyond the width of the array -/
def gVal (X : FFSeg.Arr) (a j i : ℕ) : CForm E := if j < X.width DF then cVal g X a j i else cK 0

theorem val_gVal (A : ℕ → ℕ → ℕ → E) (X : FFSeg.Arr) (a j i : ℕ) :
    (gVal g X a j i : CForm E).val A =
      if j < X.width DF then FFSeg.val (tA g A) X a j i else 0 := by
  unfold gVal
  rw [val_ite, val_cVal, val_cK]

theorem inFF_gVal {X : FFSeg.Arr} {a j i : ℕ} (ha : a < X.cnt DF) (hi : i < DF.T) :
    InFF g (gVal g X a j i : CForm E) :=
  AllPl.ite (fun hj => inFF_cVal g ha hj hi) fun _ => AllPl.cK _

end GVal

end Cm.Seg
