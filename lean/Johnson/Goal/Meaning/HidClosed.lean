-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidClosed.lean: the records at which the smallness tests stand have the plans'
lists and numbers of matrices; so the sum means_closed holds at them.

follows_closed and means_closed (Johnson/Goal/Meaning/HidPlanNM.lean) have a premise e on a family
tl of 25 records: each has the list of matrices and the number of matrices of the plan's record. The
smallness test of a sub-proof stands at the record that the verifier's check closes in the run
(closeFuns, OnBytes/Model/Tail.lean). This file pays e for these.

Which record is closed, by the checks' own text. A group of layers (OnBytes/Model/Layer.lean) and
the head (OnBytes/Model/Head.lean) close the plan's own record, hp.tl. An attention sub-proof
(OnBytes/Model/Attention.lean: run) closes what Seam.start returns: the plan's record with two
fields set (funClosed := false, foldDrawn := 0).

Main names:
  startRec tl   the plan's record with these two fields set.
  openAt X k   the record that the check of sub-proof k closes: startRec (tlAt X k) at an attention
    sub-proof, tlAt X k at a group of layers and at the head.
  ClosedAt X tl   each tl k, k < 25, is what closeFuns returns on openAt X k, at some list of
    tables.
  e_of_closed   ClosedAt gives the premise e (by the library's closeFuns_keeps).
  follows_run, means_run   so, in scope, the library's sizes at the closed records follow the plans,
    and the sum holds at them.
  closedAt_met   ClosedAt can be met where the records that the checks close are open.

What is not claimed. THAT openAt IS THE RECORD WHICH A RUN CLOSES IS READ IN THE CHECKS' TEXT, NOT
PROVED: the checks are programs in the chain's monad, and no statement on their runs is made here.
What Johnson/Goal/Meaning/HidPlanNM.lean's head names as owed stays owed, but for e, which this file
pays from ClosedAt. The full size alone. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidPlanNM

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model (HTailF2)
open OnBytes.Model.Verify (publicOf layerShape)

/-- The record that Seam.start returns of a plan's record. -/
def startRec (tl : HTailF2) : HTailF2 := { tl with funClosed := false, foldDrawn := 0 }

/-- The record that the check of sub-proof k closes. -/
def openAt (X : Model.Verify.Public) (k : ℕ) : HTailF2 :=
  if k % 2 = 1 then startRec (tlAt X k) else tlAt X k

/-- Each record is what closeFuns returns on the record that the check closes. -/
def ClosedAt (X : Model.Verify.Public) (tl : ℕ → HTailF2) : Prop :=
  ∀ k < 25, ∃ funs, (openAt X k).closeFuns funs = some (tl k)

/-- **The closed records have the plans' lists and numbers of matrices.** -/
theorem e_of_closed {X : Model.Verify.Public} {tl : ℕ → HTailF2} (c : ClosedAt X tl) :
    ∀ k < 25, (tl k).NM = (tlAt X k).NM ∧ (tl k).mats = (tlAt X k).mats := by
  intro k hk
  obtain ⟨funs, h⟩ := c k hk
  obtain ⟨-, a, b⟩ := closeFuns_keeps h
  unfold openAt at a b
  by_cases ho : k % 2 = 1
  · rw [if_pos ho] at a b
    exact ⟨b, a⟩
  · rw [if_neg ho] at a b
    exact ⟨b, a⟩

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- In scope the library's sizes at the closed records follow the plans. -/
theorem follows_run (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {tl : ℕ → HTailF2}
    (c : ClosedAt X tl) : Follows X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size :=
  follows_closed h C (e_of_closed c)

/-- **The sum at the closed records.** -/
theorem means_run (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {tl : ℕ → HTailF2}
    (c : ClosedAt X tl) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) {pp : Inst.Model.ScalesAndPolicy} {i : Cm.Idx}
    {x : Inst.Model.Instance Inst.Model.ppref} (tok : Fin Inst.Model.ppref.V) (msg : Msgs)
    (G : ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
      (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g)) i.mat x)
    (At : ∀ g < 12, AttOrd (Hd.shapeA X g)
      (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X
      (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg 24))) :
    Means X pp i x (hidAt X (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
      (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) tok msg) :=
  means_closed h C (e_of_closed c) f tok msg G At H

end Core

/-- ClosedAt can be met where the records that the checks close are open (ho): such a record closes
at every list of tables. At an attention sub-proof ho holds by startRec's text; at a group of layers
and at the head it is the plan's own field funClosed: false in scope by open_of_core,
Johnson/Goal/Meaning/HidOpen.lean. -/
theorem closedAt_met (X : Model.Verify.Public) (ho : ∀ k < 25, (openAt X k).funClosed = false)
    (funs : ℕ → Array Model.HFun) :
    ClosedAt X fun k => { openAt X k with funClosed := true, funs := funs k } := by
  intro k hk
  refine ⟨funs k, ?_⟩
  unfold HTailF2.closeFuns
  rw [ho k hk]
  rfl

end Meaning

#print axioms Meaning.e_of_closed
#print axioms Meaning.follows_run
#print axioms Meaning.means_run
#print axioms Meaning.closedAt_met
