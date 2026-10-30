-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3RowScope.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot): ITS ROW UNDER
THE FOUR COMMON PREMISES (the goals' scope on the three public files · their reading · the public
part's return · the blank ground's return): FOUR OF ITS HYPOTHESES FALL. A joining of proved laws.
  `public_of_plain`: the reader's return off the public part's and the ground's
    (`IM.ground_publicK`, `ProofFile.Law.blankBy_W`).
  `setting_ref`: a closed fact: the setting at the goals' reference lines is the written one.
    `setting_ref_control`: a negative test.
  `ReadsLeft Z`: the eight hypotheses of `ReadsEq Z` (K3RowPaid.lean) that are left: links · calls ·
    digits · before · laid · key · quiet · caller.
  `readsEq_of_scope`: p4 and groups by `Meaning.scope_plans`; setting by
    `Meaning.HeadS.frame_in_scope`.
  `k3_row_scope`: **((K3Lot.lot Z).blocks G).map skel = k3RowsW.**
WHICH "SCOPE". hS is `VerifierAndGoals.InScope` of the three public files: the goals' own premise. No opening
of the maker and no test on the proof file's description is spent. WHERE THE WEIGHT GOES: the public
part's return is a premise: the calls' tables' cost stands there.
Limits. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3RowPaid
import Johnson.IMR.PureJoin
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Goal.Meaning.HeadShapeScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (quietAt)
open VerifiableInference.Desc.First.Look (lookAt beforeAt laidAt padKeyAt)
open ProofFile.Sk (skel)

/-- The reader's return, off the public part's and the blank ground's. -/
theorem public_of_plain {pol lay KL : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    publicOf pol KL (some lay) = .ok Z.p.X := by
  rw [← ProofFile.Law.blankBy_W hG]
  exact IM.ground_publicK hZ hG

/-- The setting at the goals' reference lines is the written one. -/
theorem setting_ref : Params.settingOf VerifierAndGoals.Lines.frameRef = setW := by decide +kernel

/-- A negative test: with the lines' security level one higher the setting is another. -/
theorem setting_ref_control :
    Params.settingOf { VerifierAndGoals.Lines.frameRef with sec := VerifierAndGoals.Lines.frameRef.sec + 1 } ≠
      setW := by
  decide +kernel

/-- **The hypotheses that are left.** -/
structure ReadsLeft (Z : ProofFile.Pub) : Prop where
  links : Z.first.shape.link.length = 25
  calls : ∀ i < 25, ∃ x, lookAt Z.p.X i false = some x ∧ viewOf true x = viewW i false
  digits : ∀ i < 25, ∃ x, lookAt Z.p.X i true = some x ∧ viewOf false x = viewW i true
  before : ∀ i < 25, ∀ d, beforeAt Z.first.codes Z.first.shape i d = some (beforeW i d)
  laid : ∀ i < 25, ∀ d, laidAt Z.p.X i d = some (pubW (sortOf i) d)
  key : ∀ i < 25, ∀ d, padKeyAt Z.p.X i d = some true
  quiet : ∀ i < 25, ∀ d, (quietAt Z.p.X i d).isSome = quietW i d
  caller : ∀ i < 25, (K3Lot.readersAt Z.p.X i).isSome = callerW i

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

theorem readsEq_of_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL (some lay) = .ok Z.p.X) (R : ReadsLeft Z) : ReadsEq Z :=
  { links := R.links
    p4 := (Meaning.scope_plans hS hR hX).1
    groups := (Meaning.scope_plans hS hR hX).2.1
    setting := by rw [Meaning.HeadS.frame_in_scope hS hR hX]; exact setting_ref
    calls := R.calls, digits := R.digits, before := R.before, laid := R.laid, key := R.key
    quiet := R.quiet, caller := R.caller }

/-- **THE LOT's ROW UNDER THE FOUR COMMON PREMISES.** -/
theorem k3_row_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (R : ReadsLeft Z) (G : ProofFile.Ground) :
    ((K3Lot.lot Z).blocks G).map skel = k3RowsW :=
  k3_row_public (public_of_plain hZ hG) (readsEq_of_scope hS hR (public_of_plain hZ hG) R) G

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.public_of_plain
#print axioms Johnson.AtFull.Lots.K3.setting_ref
#print axioms Johnson.AtFull.Lots.K3.setting_ref_control
#print axioms Johnson.AtFull.Lots.K3.readsEq_of_scope
#print axioms Johnson.AtFull.Lots.K3.k3_row_scope
