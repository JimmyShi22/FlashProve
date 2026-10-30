-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidSumClosed.lean: the guard of the sum, from the files alone, at the closed
records.

sum_met_some (Johnson/Goal/Meaning/HidSumGuard.lean) meets the three premises of means_follows from
the three premises on the files alone, at the library's own sizes of the plans' OPEN records, at
which no smallness test stands. sum_met_run meets them at the closed records under ClosedAt, and
closedAt_core (Johnson/Goal/Meaning/HidOpen.lean) meets ClosedAt in scope. This file joins the two
halves.

Main names:
  closedRec X funs k   what closeFuns returns on the record that the check of sub-proof k closes, at
    the list of tables funs k.
  sum_met_closed   from InScope, readFiles and publicOf alone, at every choice of the lists of
    tables: some index, request, f and msg meet G, At and H at the library's own sizes of the closed
    records.
  means_met_closed   so Means holds there at the witness's hidden values, for every token.

What is not claimed. What the heads of Johnson/Goal/Meaning/HidSumGuard.lean and
Johnson/Goal/Meaning/HidClosed.lean disclaim: the messages are made up; that openAt is the record
which a run closes is read in the checks' text; that some files are in scope, and that publicOf
returns at them, are evaluations, no theorems. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidSumGuard
import Johnson.Goal.Meaning.HidOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf layerShape)
open Cb.Pv.Tail (Size)

/-- What closeFuns returns on the record that the check of sub-proof k closes. -/
def closedRec (X : Model.Verify.Public) (funs : ℕ → Array Model.HFun) (k : ℕ) : Model.HTailF2 :=
  { openAt X k with funClosed := true, funs := funs k }

/-- The library's own sizes of the closed records. -/
def sizesClosed (X : Model.Verify.Public) (funs : ℕ → Array Model.HFun) (k : ℕ) : Size :=
  (OnBytes.Tie.Pv.Tail.sizeOf (closedRec X funs k)).size

/-- **From the three premises on the files alone, at the closed records.** -/
theorem sum_met_closed {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (funs : ℕ → Array Model.HFun) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs),
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
        (ownAt (sizesClosed X funs) (seatBy f X (sizesClosed X funs)) msg (2 * g)) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g)
        (ownAt (sizesClosed X funs) (seatBy f X (sizesClosed X funs)) msg (2 * g + 1))) ∧
      HeadPlain pp i x
        (headStream X (ownAt (sizesClosed X funs) (seatBy f X (sizesClosed X funs)) msg 24)) :=
  ⟨_, _, sum_met_run hZ hR h _ _ (Policy.TrueGuards.some_true (lawful_of_read hR) pp.pol)
    (closedAt_core h (Hd.core_of_scope hZ hR h) funs)⟩

/-- So Means holds there at the witness's hidden values. -/
theorem means_met_closed {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (funs : ℕ → Array Model.HFun) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs),
      ∀ tok, Means X pp i x
        (hidAt X (sizesClosed X funs) (seatBy f X (sizesClosed X funs)) tok msg) := by
  obtain ⟨i, x, f, msg, G, At, H⟩ := sum_met_closed hZ hR h funs
  have C := Hd.core_of_scope hZ hR h
  exact ⟨i, x, f, msg, fun tok =>
    means_follows h C (follows_run h C (closedAt_core h C funs)) f tok msg G At H⟩

end Meaning

#print axioms Meaning.sum_met_closed
#print axioms Meaning.means_met_closed
