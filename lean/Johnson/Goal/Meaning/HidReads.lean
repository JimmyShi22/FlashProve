-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidReads.lean: what the smallness test's relation says of a witness's list: the
committed reads are the weighted sums of the list's entries.

The smallness test's relation before its random draw (relIn, Cb/Pv/Tail/Block.lean) says of each
column three things: there are small cells; the committed symbols are their packing; THE COMMITTED
READS ARE THE WEIGHTED SUMS OF THESE CELLS. Johnson/Goal/Meaning/HidBaseTie.lean carries the first
two to a witness's list (BaseSegF). This file carries the third: it is what a payer needs who holds
a law on the reads and wants it of the list.

Main names:
  ownAtF_of_e   FROM THE EQUATION ALONE, Λ.sym m = symAt (s k) (seat k) (msgF k): the list of
    sub-proof k is the total form of cellsOf Λ m. By the make: it holds at symbols that pack nothing
    too, and is no gift of the test. (ownAtF_of_relIn, Johnson/Goal/Meaning/HidBaseTie.lean, states
    the same under premises that it does not need.)
  tab_ownAtF   UNDER relIn, Size.Uniq AND THE EQUATION: Λ.tab m μ r c = the sum over the rows i of
    Λ.w x μ r i times the cast of ownAtF s seat msgF k μ i c. Here the relation and the inequalities
    bite.
  small_ownOf_all   by the make, at every family y of symbols: every entry of ownOf s y k is below
    2^18 in absolute value, where the shift is not 0 and twice the shift is at most 2^18.
  sum_met_base_run, sum_met_base_closed   the guard with BaseSeg at all 25 sub-proofs (sum_met_base,
    Johnson/Goal/Meaning/HidBaseMember.lean) at the closed records: under ClosedAt; and from the
    three premises on the files alone.

What is not claimed. The equation; that Λ.tab and Λ.w are what a run's messages and the verifier's
weights are: both are letters of the test's block here. relIn of any run. The program does not
import this file.
-/
import Johnson.Goal.Meaning.HidBaseTie
import Johnson.Goal.Meaning.HidBaseMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open Cb.Pv.Tail (Size Syms Letters relIn)

section Tie
variable {s : ℕ → Size} {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {k : ℕ} {msgF : ℕ → Msgs}

/-- **From the equation alone**: the list of sub-proof k is the total form of the test's cellsOf. -/
theorem ownAtF_of_e (Λ : Letters Cb.Gl.E (s k)) {m : Λ.M}
    (e : Λ.sym m = symAt (s k) (seat k) (msgF k)) :
    ownAtF s seat msgF k = mzTot (Cb.Pv.Tail.cellsOf Λ m) := by
  show mzTot (Rows.mzAt (symAt (s k) (seat k) (msgF k))) = mzTot (Cb.Pv.Tail.cellsOf Λ m)
  rw [← e]
  rfl

/-- **The committed reads are the weighted sums of the list's entries.** -/
theorem tab_ownAtF (Λ : Letters Cb.Gl.E (s k)) (p : ℕ) [CharP Cb.Gl.E p] (U : (s k).Uniq p)
    {x : Λ.X} {m : Λ.M} (R : relIn Λ x m) (e : Λ.sym m = symAt (s k) (seat k) (msgF k))
    (μ : Fin (s k).NM) (r : Fin ((s k).nr μ)) (c : Fin ((s k).k μ)) :
    Λ.tab m μ r c = ∑ i : Fin ((s k).m μ),
      Λ.w x μ r i * ((ownAtF s seat msgF k μ.val i.val c.val : ℤ) : Cb.Gl.E) := by
  rw [(Cb.Pv.Tail.cellsOK_cellsOf Λ p U R).2.2 μ c r]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ownAtF_of_e Λ e]
  unfold mzTot
  rw [dif_pos μ.isLt, dif_pos c.isLt, dif_pos i.isLt]

end Tie

/-- **By the make**, at every family of symbols: every entry of the list is small. -/
theorem small_ownOf_all {s : ℕ → Size} (y : ∀ k, Syms Cb.Gl.E (s k)) {k : ℕ}
    (h0 : (0 : ℤ) < ((s k).beta : ℤ)) (h2 : 2 * ((s k).beta : ℤ) ≤ 2 ^ 18) (a r c : ℕ) :
    |ownOf s y k a r c| < 2 ^ 18 := by
  unfold ownOf mzTot
  split_ifs with h hc hr
  · exact lt_of_lt_of_le (small_mzAt _ h0 _ _ _) h2
  · simp
  · simp
  · simp

/-- The guard with BaseSeg, at the library's own sizes of the closed records, under ClosedAt. -/
theorem sum_met_base_run {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) {tl : ℕ → Model.HTailF2}
    (c : ClosedAt X tl) :
    ∃ (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs),
      (∀ k < 25, BaseSeg (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg k) ∧
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
        (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
          (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g)
        (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
          (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g + 1))) ∧
      HeadPlain pp i x (headStream X
        (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
          (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg 24)) :=
  sum_met_base hZ hR h i x T (follows_run h (Hd.core_of_scope hZ hR h) c) (fun _ _ => rfl)
    (fun _ _ => rfl)

/-- **From the three premises on the files alone, at the closed records, at messages that are a
packing.** -/
theorem sum_met_base_closed {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (funs : ℕ → Array Model.HFun) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs),
      (∀ k < 25, BaseSeg (sizesClosed X funs) (seatBy f X (sizesClosed X funs)) msg k) ∧
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
        (ownAt (sizesClosed X funs) (seatBy f X (sizesClosed X funs)) msg (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g)
        (ownAt (sizesClosed X funs) (seatBy f X (sizesClosed X funs)) msg (2 * g + 1))) ∧
      HeadPlain pp i x
        (headStream X (ownAt (sizesClosed X funs) (seatBy f X (sizesClosed X funs)) msg 24)) :=
  ⟨_, _, sum_met_base_run hZ hR h _ _ (Policy.TrueGuards.some_true (lawful_of_read hR) pp.pol)
    (closedAt_closedRec h (Hd.core_of_scope hZ hR h) funs)⟩

end Meaning

#print axioms Meaning.ownAtF_of_e
#print axioms Meaning.tab_ownAtF
#print axioms Meaning.small_ownOf_all
#print axioms Meaning.sum_met_base_run
#print axioms Meaning.sum_met_base_closed
