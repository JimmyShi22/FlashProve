-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBoxAH.lean.
The calls' lookups of attention and of the head: their shares of the public record with the boxes'
bounds written, and the cells of the counts' bits inside the boxes.

Fo.Pub2.lookPubA and Fo.Pub2.lookPubHX leave the bounds of the boxes of cells letters: at the bound
0 all cells would be one entry. Here the bounds are numbers of the plan: the largest number of rows
and of columns over the plan's list of matrices (Fo.Pub2.boxR, boxC), the number of the last matrix
that the names reach, and the plan's number of slots.

Main names:
  `getD_boxR`, `getD_boxC`: a matrix of the list, by its number, has at most boxR rows and boxC
    columns.
  `lookPubA1 rdA a St`: lookPubA at nR := boxR a.seam.tl.mats, nC := boxC a.seam.tl.mats.
  `lookPubA1_ok`: where Verify.publicOf returns X, at a member a of X.A: Fo.Pub2.LookPubOK of it, at
    the first slot 0.
  `lookPubA1_in`: there the cell of bit j below 32 of the count of row t below 2^kT of call c below
    NC has its matrix's number, its row and its column inside the box's bounds. The bounds are
    written as numbers; that they are those of `lookPubA1`'s type of entries is read off its
    definition (OnBytes/Tie/Pv/Lookup/Ends/FoLookPubA.lean). So by Fo.Pub2.cellJ_inj two such cells
    with different rows or columns are different entries. No statement here draws that, and none
    says that different (t, c, j) give different (row, column): a law on FoNums.cellRC that is
    stated nowhere.
  `lookPubH1 rdH X rq wR wC`, `lookPubH1_ok`, `lookPubH1_in`: the like at the head, over lookPubHX;
    the bounds wR, wC of the box of the weights' cells stay letters.
Limits: one to one is said inside the bounds alone. Nothing is said of the cells that the keys read,
nor of how many slots the lookup takes against the plan's number of slots: so of the slots no one to
one follows here. Nothing on the layers' lookup. No statement uses the two records yet.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoBox
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPub0
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubHX
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPub

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model OnBytes.Ends

theorem getD_boxR (mats : Array TMat) (i : ℕ) : (mats.getD i {}).m ≤ boxR mats := by
  by_cases h : i < mats.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    exact le_boxR (Array.getElem_mem_toList h)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

theorem getD_boxC (mats : Array TMat) (i : ℕ) : (mats.getD i {}).k ≤ boxC mats := by
  by_cases h : i < mats.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    exact le_boxC (Array.getElem_mem_toList h)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

/-- From a matrix with one block of 2^lm rows and at least the planes' columns. -/
theorem cell_in_box (h : FoNums.Sh) {lm t c j : ℕ} (mats : Array TMat) (i : ℕ) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (hm : (mats.getD i {}).m / 2 ^ lm = 1)
    (hk : planeCols h lm ≤ (mats.getD i {}).k) (ht : t < 2 ^ h.kT) (hc : c < h.NC) (hj : j < 32) :
    (FoNums.cellRC h lm (t, c, j)).1 ≤ boxR mats ∧
      (FoNums.cellRC h lm (t, c, j)).2 ≤ boxC mats := by
  obtain ⟨a, b⟩ := cellRC_lt h h5 hlm ht hc hj
  have m1 : 2 ^ lm ≤ (mats.getD i {}).m := by
    by_contra hn
    rw [Nat.div_eq_of_lt (by omega)] at hm
    cases hm
  have m2 := getD_boxR mats i
  have k2 := getD_boxC mats i
  have k1 : h.NC * 2 ^ (h.kT + 5 - lm) ≤ (mats.getD i {}).k := hk
  omega

/-! ### attention -/

/-- The record at attention, the bounds written. -/
def lookPubA1 {M₀ : Type} (rdA : M₀ → IxA → Cb.Gl.E) (a : Attention.Plan) (St : Type) :
    LookPub M₀ St :=
  lookPubA rdA a (boxR a.seam.tl.mats) (boxC a.seam.tl.mats) St

section
variable {M₀ : Type} {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem lookPubA1_ok (rdA : M₀ → IxA → Cb.Gl.E) (h : Verify.publicOf pol KL layout = .ok X)
    (g : ℕ) (a : Attention.Plan) (hg : X.A[g]? = some a) (St : Type) :
    LookPubOK (lookPubA1 rdA a St) (a.S.calls.map (·.call)) a.fs.pub a.lid a.S.cf.lmb 0 maskJ
      (cellJ (a.S.cf.NAs + 2)) :=
  lookPubA_ok0 rdA h g a hg _ _ St

theorem lookPubA1_in (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) {t c j : ℕ} (ht : t < 2 ^ a.fs.kT) (hc : c < a.fs.NC) (hj : j < 32) :
    a.S.cf.NAs + 2 ≤ a.S.cf.NAs + 4 ∧
      (FoNums.cellRC a.fs a.S.cf.lmb (t, c, j)).1 ≤ boxR a.seam.tl.mats ∧
      (FoNums.cellRC a.fs a.S.cf.lmb (t, c, j)).2 ≤ boxC a.seam.tl.mats := by
  have k := lookPubA_ok0 (M₀ := Unit) (fun _ _ => 0) h g a hg 0 0 Unit
  have p := Fo.PlaneMat.public_planeMatAB h g a hg
  simp only [planeMatAB, Bool.and_eq_true, decide_eq_true_eq] at p
  exact ⟨by omega, cell_in_box a.fs a.seam.tl.mats _ k.lm5 k.lmT p.1.2 p.2 ht hc hj⟩

/-! ### the head -/

/-- The record at the head, the bounds of its own matrices' box written. -/
def lookPubH1 (rdH : M₀ → IxH → Cb.Gl.E) (X : Verify.Public) {St : Type}
    (rq : St → Head.Covered × Array ℕ) (wR wC : ℕ) : LookPub M₀ St :=
  lookPubHX rdH X rq X.H.tl.mats.size (boxR X.H.tl.mats) (boxC X.H.tl.mats) wR wC X.H.ns

theorem lookPubH1_ok (rdH : M₀ → IxH → Cb.Gl.E) (h : Verify.publicOf pol KL layout = .ok X)
    {St : Type} (rq : St → Head.Covered × Array ℕ) (wR wC : ℕ) :
    LookPubOK (lookPubH1 rdH X rq wR wC) X.HLy.cl X.HLy.fs.pub X.hS.LIDB X.hS.lmbH 0 maskH
      (cellH (X.hS.NHf + 2)) :=
  lookPubHX_ok rdH h rq _ _ _ wR wC _

theorem lookPubH1_in (h : Verify.publicOf pol KL layout = .ok X) {t c j : ℕ}
    (ht : t < 2 ^ X.HLy.fs.kT) (hc : c < X.HLy.fs.NC) (hj : j < 32) :
    X.hS.NHf + 2 ≤ X.H.tl.mats.size ∧
      (FoNums.cellRC X.HLy.fs X.hS.lmbH (t, c, j)).1 ≤ boxR X.H.tl.mats ∧
      (FoNums.cellRC X.HLy.fs X.hS.lmbH (t, c, j)).2 ≤ boxC X.H.tl.mats := by
  have k := lookPubHX_ok (M₀ := Unit) (St := Unit) (fun _ _ => 0) h (fun _ => (default, #[]))
    0 0 0 0 0 0
  have p := Fo.PlaneMat.public_planeMatHB h
  simp only [planeMatHB, Bool.and_eq_true, decide_eq_true_eq] at p
  refine ⟨?_, cell_in_box X.HLy.fs X.H.tl.mats _ k.lm5 k.lmT p.1.2 p.2 ht hc hj⟩
  by_contra hn
  have e : X.H.tl.mats.getD (X.hS.NHf + 1 + 1) {} = {} := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl
  have p2 := p.1.2
  rw [e] at p2
  simp at p2

end

end Fo.Pub2
