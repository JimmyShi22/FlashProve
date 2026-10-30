-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/MarksAtSmall.lean

What it proves. At the small made-up chain of SharedSmall.lean (P3): the premises on the plan and on
the fall-back that MarksAtDoor.lean's theorems ask are met, with the fall-back fallU P3 sentU3
(ShapeBehind.lean). So at P3, at the state on entry to the test on G_u that doorOf makes with that
fall-back, at every input and whatever precedes the test, whatever the readers of the key and of the
columns are: the three tests stTidyB, stPlainB and claimsB hold, and the shape is the term
doorU (endOf P3 sentU3).

Names.
  threeB, three_iff   the three tests as one Bool.
  sameDoor, fallSpoiled, denseSpoiled   tools of the guards.
  planOk_bs3   each of the eight blocks' tests on the plan passes at P3.
  three_fallU_small   the three tests hold at fallU P3 sentU3: by the kernel's evaluation.
  three_small_U, shape_small_U   the two theorems at P3.
  The guards evaluate the three tests and the shape at the honest values of PubAtSmallDoor.lean, at
  the old fall-back, and at states that are spoiled on purpose.

What the guards show. At the honest rounds and columns the state that doorOf gives at the test on
G_u passes the three tests and has the term's shape; the one at the test on G_omega passes the three
tests (its shape is not looked at here). The state that holds the plan's public part
and nothing else fails the first test. fallU P3 sentU3 with one member's mark "sampled" struck fails
the first test; with a written-out variable laid into a row of the honest state the second test
fails: so the tests can fail.

Limits. One small made-up plan. The theorems are also true of the fall-back: they do not tell a fold
that failed from one that returned, and they are no statement that the state on entry is the
verifier's. doorU and doorOmega of NearAtHead.lean are not turned: they still fall back to
stateOfPub (the jobs of JobShared.lean take the state function as an argument). Nothing at the test
on G_omega but one guard. It stands over files that are not in the library yet, as MarksBehind.lean
does. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.MarksAtDoor
import Johnson.Desc.ProofFile.Honest.K12.PubAtSmallDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.SharedSmall
open OnBytes (TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.enter)
open VerifiableInference.Desc.Ground.Sh (stTidyB stPlainB)
open Desc.K14 (St blocks first)
open ProofFile.Honest.Sh (claimsB testSh)
open ProofFile.Honest.K12.Light.SharedToy (fr)

variable {W X : Type}

/-- The three tests as one Bool. -/
def threeB (t : T12) : Bool := stTidyB t.st && stPlainB t.st && claimsB t

theorem three_iff (t : T12) : threeB t = true ↔ Three t := by
  unfold threeB
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.tidy, h.plain⟩, h.claims⟩⟩

/-- Each of the eight blocks' tests on the plan passes at P3. -/
theorem planOk_bs3 : ∀ b ∈ bs3, b.planOk = true := by
  have h : (bs3.all fun b => b.planOk) = true := by decide +kernel
  exact fun b hb => List.all_eq_true.1 h b hb

/-- The three tests hold at the fall-back that is made of the term. -/
theorem three_fallU_small : Three (fallU P3 sentU3) :=
  (three_iff _).1 (by decide +kernel)

/-- **The three tests at the door of the test on G_u, at P3**, with the fall-back made of the
term. -/
theorem three_small_U (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W)
    (fr : Front X) :
    Three (doorOf bs3 (fun w => first P3.codes (key w)) (Seat.enter (·.gU) (·.firstMask)) cols
      (fallU P3 sentU3) w fr) :=
  three_door_U P3 bs3 blocks_P3 planOk_bs3 splits_P3 sentU3 withU_P3 key cols _ three_fallU_small
    w fr

/-- **The shape there is one term.** -/
theorem shape_small_U (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W)
    (fr : Front X) :
    testSh (doorOf bs3 (fun w => first P3.codes (key w)) (Seat.enter (·.gU) (·.firstMask)) cols
      (fallU P3 sentU3) w fr) = Desc.K14.Shape.doorU (endOf P3 sentU3) :=
  shape_door_U_fall P3 bs3 blocks_P3 splits_P3 sentU3 withU_P3 key cols w fr

/-! ## Guards -/

/-- Two shapes at a door are the same: the core, the group, the mask; nothing is passed. -/
def sameDoor (a b : ProofFile.Honest.Sh.TestSh) : Bool :=
  decide (a.core = b.core) && a.g == b.g && a.mask == b.mask &&
    (match a.pass, b.pass with
      | .nothing, .nothing => true
      | _, _ => false)

/-- fallU with the mark "sampled" struck from its first message. -/
def fallSpoiled : T12 :=
  { fallU P3 sentU3 with
    st := { (fallU P3 sentU3).st with
      oracles := (fallU P3 sentU3).st.oracles.modify 0 fun x => { x with sampled := false } } }

/-- A state with a written-out variable laid into the first term of the first open row of its first
group. -/
def denseSpoiled (t : T12) : T12 :=
  { t with
    st := { t.st with
      groups := t.st.groups.modify 0 fun G =>
        { G with rows := G.rows.modify 0 fun r =>
          { r with terms := r.terms.modify 0 fun u => { u with v := u.v.pushDense 1 } } } } }

-- at the honest values the fold returns (PubAtSmallDoor.lean), and the state passes the three
#guard threeB (doorAtU colsU () fr)
#guard sameDoor (testSh (doorAtU colsU () fr)) (Desc.K14.Shape.doorU (endOf P3 sentU3))
#guard threeB (doorAtOmega colsO () frO)
-- the term's own state
#guard threeB (fallU P3 sentU3)
#guard sameDoor (testSh (fallU P3 sentU3)) (Desc.K14.Shape.doorU (endOf P3 sentU3))
-- the old fall-back fails the first test, and has another shape
#guard !stTidyB (stateOfPub (pubBehind P3 sentU3, 0)).st
#guard !sameDoor (testSh (stateOfPub (pubBehind P3 sentU3, 0)))
  (Desc.K14.Shape.doorU (endOf P3 sentU3))
-- the tests can fail
#guard !stTidyB fallSpoiled.st
#guard stPlainB (doorAtU colsU () fr).st && !stPlainB (denseSpoiled (doorAtU colsU () fr)).st
-- with another word in a column the fold returns, and marks and shape stay
#guard threeB (doorAtU colsTurned () fr) &&
  sameDoor (testSh (doorAtU colsTurned () fr)) (Desc.K14.Shape.doorU (endOf P3 sentU3))

end ProofFile.Honest.K12.Light.SharedSmall

#print axioms ProofFile.Honest.K12.Light.SharedSmall.threeB
#print axioms ProofFile.Honest.K12.Light.SharedSmall.three_iff
#print axioms ProofFile.Honest.K12.Light.SharedSmall.planOk_bs3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.three_fallU_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.three_small_U
#print axioms ProofFile.Honest.K12.Light.SharedSmall.shape_small_U
#print axioms ProofFile.Honest.K12.Light.SharedSmall.sameDoor
#print axioms ProofFile.Honest.K12.Light.SharedSmall.fallSpoiled
#print axioms ProofFile.Honest.K12.Light.SharedSmall.denseSpoiled
