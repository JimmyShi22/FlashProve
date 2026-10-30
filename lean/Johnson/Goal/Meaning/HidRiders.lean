-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidRiders.lean: two small turns: the member of the fifteen clauses at the
closed records; and smallness by the make in the forms in which hidden values bear their lists.

Main names:
  twelve_met_run   twelve_met (Johnson/Goal/Meaning/HidTwelveMet.lean) at the library's own sizes of
    the closed records, under ClosedAt.
  twelve_met_closed   from the three premises on the files alone, at every choice of the lists of
    tables: some index, request and msg with BaseSeg at all 25 sub-proofs, OwnG, OwnA and
    Hd.HeadOrdLB at the lists, at the sizes of closedRec X funs. THE REQUEST IS THE LIBRARY's
    some_true: THE ALL-ZERO WEIGHTS, all tokens 0, r = 1,023, e = 1,024, y = 0: it has no counted
    position. "From the files alone" is bought with the zero model: that a true request exists at
    other weights is shown nowhere here.
  small_mgOf, smallM_mgOf   by the make: every entry of the list mgOf yl (ownOf s y) g, in which
    hidden values bear a group's list, is below 2^18 in absolute value; so SmallM holds of it.
  small_maOf, attSmall_maOf   the same for maOf X (ownOf s y) g and AttSmall.

What is not claimed. What the heads of Johnson/Goal/Meaning/HidTwelveMet.lean and
Johnson/Goal/Meaning/HidFamilyParts.lean disclaim: the messages and seats are made up; smallness at
these lists says nothing of a witness. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidTwelveMet
import Johnson.Goal.Meaning.HidReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Layer (Lay matIx)
open Cb.Pv.Tail (Size Syms)

/-- The member at the library's own sizes of the closed records, under ClosedAt. -/
theorem twelve_met_run {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) {tl : ℕ → Model.HTailF2}
    (c : ClosedAt X tl) :
    ∃ msg : Msgs,
      (∀ k < 25, BaseSeg (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy seat0 X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg k) ∧
      (∀ g < 12, OwnG X i x (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy seat0 X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g)) g) ∧
      (∀ g < 12, OwnA (Hd.shapeA X g) (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy seat0 X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g + 1))) ∧
      Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x
        (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
          (seatBy seat0 X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg 24) :=
  twelve_met hZ hR h i x T (follows_run h (Hd.core_of_scope hZ hR h) c) (fun _ _ => rfl)
    (fun _ _ => rfl)

/-- **From the three premises on the files alone, at the closed records**: at the library's true
request at the all-zero weights. -/
theorem twelve_met_closed {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (funs : ℕ → Array Model.HFun) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (msg : Msgs),
      (∀ k < 25, BaseSeg (sizesClosed X funs) (seatBy seat0 X (sizesClosed X funs)) msg k) ∧
      (∀ g < 12, OwnG X i x
        (ownAt (sizesClosed X funs) (seatBy seat0 X (sizesClosed X funs)) msg (2 * g)) g) ∧
      (∀ g < 12, OwnA (Hd.shapeA X g)
        (ownAt (sizesClosed X funs) (seatBy seat0 X (sizesClosed X funs)) msg (2 * g + 1))) ∧
      Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x
        (ownAt (sizesClosed X funs) (seatBy seat0 X (sizesClosed X funs)) msg 24) :=
  ⟨_, _, twelve_met_run hZ hR h _ _ (Policy.TrueGuards.some_true (lawful_of_read hR) pp.pol)
    (closedAt_closedRec h (Hd.core_of_scope hZ hR h) funs)⟩

section Small
variable {s : ℕ → Size} (y : ∀ k, Syms Cb.Gl.E (s k))
  (h0 : ∀ k < 25, (0 : ℤ) < ((s k).beta : ℤ)) (h2 : ∀ k < 25, 2 * ((s k).beta : ℤ) ≤ 2 ^ 18)
include h0 h2

/-- **By the make**: every entry of the list in which hidden values bear a group's list is small. -/
theorem small_mgOf (yl : Lay) {g : ℕ} (hg : g < 12) (a r c : ℕ) :
    |mgOf yl (ownOf s y) g a r c| < 2 ^ 18 := by
  unfold mgOf
  split
  · exact small_ownOf_all y (h0 _ (by omega)) (h2 _ (by omega)) _ r c
  · exact small_ownOf_all y (h0 _ (by omega)) (h2 _ (by omega)) _ r c

theorem smallM_mgOf (yl : Lay) {g : ℕ} (hg : g < 12) : SmallM yl (mgOf yl (ownOf s y) g) :=
  fun _ r c _ => small_mgOf y h0 h2 yl hg _ r c

/-- The same for an attention sub-proof's list. -/
theorem small_maOf (X : Model.Verify.Public) {g : ℕ} (hg : g < 12) (a r c : ℕ) :
    |maOf X (ownOf s y) g a r c| < 2 ^ 18 := by
  unfold maOf
  split
  · exact small_ownOf_all y (h0 _ (by omega)) (h2 _ (by omega)) _ r c
  · exact small_ownOf_all y (h0 _ (by omega)) (h2 _ (by omega)) _ r c

theorem attSmall_maOf (X : Model.Verify.Public) {g : ℕ} (hg : g < 12) :
    AttSmall (Hd.shapeA X g) (maOf X (ownOf s y) g) :=
  fun _ _ => small_maOf y h0 h2 X hg _ _ _

end Small

end Meaning

#print axioms Meaning.twelve_met_run
#print axioms Meaning.twelve_met_closed
#print axioms Meaning.small_mgOf
#print axioms Meaning.smallM_mgOf
#print axioms Meaning.small_maOf
#print axioms Meaning.attSmall_maOf
