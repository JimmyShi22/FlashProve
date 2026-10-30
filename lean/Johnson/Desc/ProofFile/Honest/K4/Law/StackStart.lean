-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackStart.lean: CONDITIONAL.

What is here. THE START OF THE BATCHED SUMCHECK OF THE FEED-FORWARD LAYERS' ROUNDS: the verifier's
start form (`joinStart`, OnBytes/Desc/First/K4/Hear.lean; `startOf`,
Johnson/Road/FormsKeysStart.lean) is worth the reading of the total of the honest job's cube, FROM
FOUR NAMED SENTENCES. The total is the sum of the products of the two long vectors' entries; the
vectors are made of panels, each of the first or of the second pass. Definitions, one statement on
the total, and the joining of the four. Statements and proofs.

THE FOUR. (1) the total is the first pass's sum plus the second's (a law on tables: the panels'
places are apart). (2) the second pass's sum is the second weight times the second token sumcheck's
summand at its end point on the values as sent (panel by panel, the same factors). (3) the form that
the second token sumcheck leaves is worth that summand (TermsTop.lean). (4) `JoinWorth`: THE FIRST
PASS IS THE LOOKUP's JOIN: the start form without its last term is worth the first pass's sum.

  `passSum`   the sum of the products of the two sides over the panels of one pass
  `JoinWorth`   **the hypothesis on the first pass**
  `stack_total_read`   the total as a sum over the places
  `stack_sigma`   **the start form's worth**, from the four

Limits. At the reading `Reading.gl`. ALL FOUR ARE PREMISES HERE: none is shown in this file.
`JoinWorth` crosses into the lookup's own rounds and into the keys' arithmetic: the library cuts its
left side in three (`start_parts`, Johnson/Road/FormsKeysStart.lean); of a law of the library on the
whole (`whole_holds`, Johnson/Road/Rows/LayerEnds34.lean) the docstring of `OwnBack.stack`
(Johnson/Road/K4/W/Join.lean) says that it stands at the library's full-size structure alone (taken
from that docstring; not checked here). No example is known. No property is claimed.
-/
import Johnson.Desc.K4.Honest.Stack
import Johnson.Desc.K4.Honest.Law.Cube
import Johnson.Road.FormsKeysStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.Model (Reading Aff World Tsc)
open OnBytes.Road (padOf startOf startOf_value)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw

/-- **The sum, over the panels of pass c, of the products of the panel's two sides** as the honest
side lays them (`panelTabs`). A panel whose sides are not made counts 0. -/
noncomputable def passSum (D : StackData) (c : ℕ) : Cb.Gl.E :=
  ((D.bl.toList.filter fun b => b.claim == c).map fun b =>
    match panelTabs D.S (fun a => valAff? D.S.v D.R (fun _ => zeroE) a) D.om D.F D.hZ D.hR b with
    | some x => ∑ i ∈ Finset.range (b.ni * b.ny),
        Reading.gl.val (x.1.getD i zeroE) * Reading.gl.val (x.2.getD i zeroE)
    | none => 0).sum

/-- **THE FIRST PASS IS THE LOOKUP's JOIN.** parts: the calls' factors that `joinStart` makes. The
left side: the calls' factors under the lookup's weights, plus the padding trees' public number,
less the hidden claimed sum of the second token sumcheck, less what the form that the lookup's end
leaves is worth. THE RIGHT SIDE HOLDS D's FIRST WEIGHT AS A FACTOR IN EVERY PANEL, THE LEFT SIDE HAS
NONE: so it can hold on an honest run only where that weight reads 1, as the first of the powers
of an element does; H, parts and D are free of each other here. This defines a hypothesis; the
definition claims nothing. -/
def JoinWorth (H : OnBytes.Model.Layer.Heard) (tT : Tsc) (parts : List Aff) (Wd : World Cb.Gl.E)
    (D : StackData) : Prop :=
  (parts.zipIdx.map fun x =>
      Reading.gl.val (H.fo.e.getD x.2 zeroE) * x.1.value Reading.gl Wd).sum +
    Reading.gl.val (padOf H) - Wd.slot tT.sCl - H.fo.cEnd.value Reading.gl Wd = passSum D 0

/-- The total of the job's cube: the sum over the places of the products of the two long vectors'
entries. -/
theorem stack_total_read (D : StackData) :
    Reading.gl.val (jobStackOn D).cube.total =
      ∑ n ∈ Finset.range (2 ^ D.S.Q.hp.lamS),
        Reading.gl.val (D.SA.getD n zeroE) * Reading.gl.val (D.SB.getD n zeroE) := by
  rw [total_plain Reading.gl _ rfl]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [termsAt_read]
  show Reading.gl.val oneE * (Reading.gl.val (D.SA.getD n zeroE) *
    Reading.gl.val (D.SB.getD n zeroE)) + 0 = _
  rw [Reading.gl.one, one_mul, add_zero]

/-- **The start form is worth the total**, from the four. sT: the second token sumcheck's summand at
its end point on the values as sent. om: the verifier's two weights; D's are meant to be the same:
no premise says so: h2 and h4 bear it. -/
theorem stack_sigma (H : OnBytes.Model.Layer.Heard) (om : Array E) (parts : List Aff) {tT : Tsc}
    (hT : H.tT = some tT) (Wd : World Cb.Gl.E) (D : StackData) (sT : E)
    (h1 : Reading.gl.val (jobStackOn D).cube.total = passSum D 0 + passSum D 1)
    (h2 : passSum D 1 = Reading.gl.val (om.getD 1 zeroE) * Reading.gl.val sT)
    (h3 : H.KT.value Reading.gl Wd = Reading.gl.val sT) (h4 : JoinWorth H tT parts Wd D) :
    (startOf H om parts).value Reading.gl Wd = Reading.gl.val (jobStackOn D).cube.total := by
  unfold JoinWorth at h4
  rw [startOf_value Reading.gl Wd H om parts hT, h1, h2, h3, h4]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stack_total_read
#print axioms ProofFile.Honest.K4.stack_sigma
