-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K11RoundsNamed.lean: THE SECOND ROW OF THE MERGE's LOT (`K11.lot`), IN THE
FORM "a block's rounds are the written table's list at the written name of the block's place": the
last step from the core (Johnson/AtFull/Desc/Lots/K11Rounds.lean, K11RoundsScope.lean) to the form
that the law `ProofFile.Sk.Full.rows_by_place`
(Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean) takes. Statements and proofs; two closed facts by
Lean's kernel.

What it says.
  `name_placeW`: by the kernel: that file's `nameW` gives "H:9" at the place
    ⟨1, some 24, 9, .K11⟩. `name_23`: a negative test: at the place one segment earlier it gives the
    empty name: no written place is there.
  `k11_row_at`: THE ROW, under the core's three hypotheses by field: for every block b of the lot:
    `b.rounds = listAt (nameW b.place)`. `k11_row_scope`: THE ROW IN THE GOALS' SCOPE: the three are
    paid. `k11_row_scope_or`: the same with "b has no round, or" in front: to the letter what
    `ProofFile.Sk.Lst listAt (nameW b.place) b.rounds`
    (Johnson/Desc/ProofFile/Law/Skel/SkelLists.lean, which is not imported) unfolds to; always by
    the right arm.

Limits. hS, hR, hZ AND hG STAY PREMISES: that any public files meet them together is shown nowhere
here. May be idle: no example of the head is shown in this file; two, at storedPublicFiles and at zGap alone,
are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are worth.
`nameW` reads the written list of places `spotsW` (Full/Data.lean): that a description's own places
are these is another's row.
The
limits of K11Rounds.lean and K11RoundsScope.lean hold here too. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K11RoundsScope
import Johnson.Desc.ProofFile.Law.Skel.Full.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K11Rounds

open Johnson.AtFull.Rounds (listAt)
open ProofFile.Sk.Full (nameW)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

set_option maxRecDepth 1000000 in
/-- **The written name at the merge's place is "H:9".** -/
theorem name_placeW : nameW placeW = "H:9" := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one segment earlier no written place is there. -/
theorem name_23 : nameW ⟨1, some 23, 9, .K11⟩ = "" := by decide +kernel

/-- **THE ROW, under three hypotheses by field.** -/
theorem k11_row_at {Z : ProofFile.Pub} {G : ProofFile.Ground} (hb : G.built.size = 25)
    (hk : G.W.layers.wsLay.lk = 18)
    (hw : (OnBytes.Params.settingOf G.W.P.frame).workOf .field .request = 0) :
    ∀ b ∈ (K11.lot Z).blocks G, b.rounds = listAt (nameW b.place) := by
  intro b hbm
  obtain ⟨h1, h2⟩ := k11_rounds_at hb hk hw b hbm
  rw [h1, name_placeW]
  exact h2

/-- **THE ROW IN THE GOALS' SCOPE.** -/
theorem k11_row_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ b ∈ (K11.lot Z).blocks G₀, b.rounds = listAt (nameW b.place) :=
  k11_row_at (IM.ground_gets hS hR hZ hG).1
    (LT28.K11Tests.m0lk_in_scope hS (IM.ground_publicK hZ hG)).2 (work_scope hS hR hZ hG)

/-- The same, with "no round, or" in front. -/
theorem k11_row_scope_or (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ b ∈ (K11.lot Z).blocks G₀, b.rounds = [] ∨ b.rounds = listAt (nameW b.place) :=
  fun b hb => Or.inr (k11_row_scope hS hR hZ hG b hb)

end Johnson.AtFull.Lots.K11Rounds

#print axioms Johnson.AtFull.Lots.K11Rounds.name_placeW
#print axioms Johnson.AtFull.Lots.K11Rounds.name_23
#print axioms Johnson.AtFull.Lots.K11Rounds.k11_row_at
#print axioms Johnson.AtFull.Lots.K11Rounds.k11_row_scope
#print axioms Johnson.AtFull.Lots.K11Rounds.k11_row_scope_or
