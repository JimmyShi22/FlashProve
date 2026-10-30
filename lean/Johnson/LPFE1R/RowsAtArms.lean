-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFE1R/RowsAtArms.lean: IN SCOPE, WHERE THE PROOF FILE's PIN ON WHAT WAS MADE ACCEPTS AND
THE PLANNER RETURNS AT THE FILES' OWN DIGEST: THE SECOND READING OF THE THREE PUBLIC FILES IS THE
ONE CLOSED TERM `rowsW` (Johnson/LPFE1R/RowsAtWritten.lean), IF THE 26 LINKS' ARMS ARE THE WRITTEN
ONES. One definition with code, and theorems. A law file; no running text imports it.
  `armsB X`         the test: (List.range 26).map (armOf X) = armsW: 26 small structures of numbers.
  `links_W`, `groups_W`   two closed facts on the written sizes: 25 links, 26 groups.
  `rows_at_arms`    InScope W · ProofFile.pubPlain secondHashFunction W.pol W.lay W.KL = .ok Z · madePinnedAt … =
                    true · Verify.planned W.pol W.KL (some W.lay) = .ok p · armsB Z.made.p.X = true
                    ⊢ Johnson.G.sendRowsOf W.pol W.lay W.KL = rowsW.
  `returns_at_arms`   so, where the closed Bool rowsWB holds, the second reading returns.
How: rows_of_made (Johnson/Desc/First/Link/Law/RowsOfMade.lean) · made_in_scope
(Johnson/Goal/Numbers/MadeInScope.lean): all sizes and all seven lists of rounds are the written
ones · rowsFrom_four · rowsFrom_congr · twelve groups of layers in scope
(H2K.Sizes.public_at_scope).

Limits. armsB IS ASKED BY NOTHING THAT THE VERIFIER RUNS, AND IS SHOWN AT NO FILES HERE (an
evaluator's print has the 26 arms as one value at six sets of public files, five of them in scope).
rowsWB = true IS A PREMISE OF returns_at_arms: an evaluation has it true; Lean's kernel refused the
closed Bool (stuck, no timeout). `rowsWB_true` (Johnson/AtFull/Rows/Rows.lean) proves rowsWB = true
out of 80 smaller closed facts; this file does not import it. "planned returns" is a premise; `planned_of_theLive` (Johnson/Desc/First/Link/Law/RowsRunLaws.lean) gives it where protocolDataWellFormedAt secondHashFunction accepts.
Nothing on the second clause of the named condition rowsRead (one shape has one radius). Nothing on
soundness or on hiding.

-/
import Johnson.LPFE1R.RowsAtWritten
import Johnson.Desc.First.Link.Law.RowsOfMade
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G (sendRowsOf)
open Johnson.G.MadeFree (Free Hung freeOf)
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.PlanWritten.Joined (writtenMade made_in_scope)

/-- The 26 links' arms are the written ones. -/
def armsB (X : OnBytes.Model.Verify.Public) : Bool :=
  decide ((List.range 26).map (armOf X) = armsW)

theorem links_W : writtenMade.sized.proof.request.link.length = 25 := by decide +kernel

theorem groups_W : (reqGroups writtenMade.sized.proof.request).toList.length = 26 := by
  decide +kernel

theorem arm_at {X : OnBytes.Model.Verify.Public} (h : armsB X = true) (j : Nat) (hj : j < 26) :
    armOf X j = armAtW j := by
  have e : (List.range 26).map (armOf X) = armsW := of_decide_eq_true h
  unfold armAtW
  rw [← e, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- **The second reading is the one closed term.** -/
theorem rows_at_arms {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {p : OnBytes.Model.Verify.Planned}
    (hp : OnBytes.Model.Verify.planned W.pol W.KL (some W.lay) = .ok p)
    (ha : armsB Z.made.p.X = true) : sendRowsOf W.pol W.lay W.KL = rowsW := by
  have hm : freeOf Z.made.p.chains.made = writtenMade :=
    made_in_scope hW (show ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z from h) hy
  have e1 : Z.made.p.chains.made.sized = writtenMade.sized := congrArg Free.sized hm
  have e2 : Z.made.p.chains.made.key = writtenMade.key := congrArg Free.key hm
  have e3 : Z.made.p.chains.made.proof = writtenMade.proof := congrArg Free.proof hm
  have e4 : Z.made.p.chains.made.entry = writtenMade.entry := congrArg Free.entry hm
  obtain ⟨_, _, _, _, _, _, _, hX, _⟩ := OnBytes.Model.Verify.planned_parts hp
  have eX := (made_tie h hp).1
  have hN : Z.made.p.X.NGr = 12 := by
    rw [← eX]
    exact (H2K.Sizes.public_at_scope hW hX).groups
  rw [rows_of_made h hp, e1, links_W, hN]
  unfold rowsW
  rw [rowsFrom_four (c := Z.made.p.chains.made) (c' := writtenMade.at Hung.none) e1 e2 e3 e4]
  exact rowsFrom_congr _ _ _ fun j hj => arm_at ha j (by
    have := groups_W
    exact this ▸ hj)

/-- So the second reading returns, where the closed Bool holds. -/
theorem returns_at_arms {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {p : OnBytes.Model.Verify.Planned}
    (hp : OnBytes.Model.Verify.planned W.pol W.KL (some W.lay) = .ok p)
    (ha : armsB Z.made.p.X = true) (K : rowsWB = true) :
    (sendRowsOf W.pol W.lay W.KL).toOption.isSome = true := by
  rw [rows_at_arms hW h hy hp ha]
  exact K

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.links_W
#print axioms VerifiableInference.Desc.LinkJoin.groups_W
#print axioms VerifiableInference.Desc.LinkJoin.rows_at_arms
#print axioms VerifiableInference.Desc.LinkJoin.returns_at_arms
