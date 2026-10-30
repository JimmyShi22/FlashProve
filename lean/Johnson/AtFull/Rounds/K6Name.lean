-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K6Name.lean.
WHAT IT DOES NOT SHOW. No soundness. A JOINING OF ONE CALL AND ONE CLOSED FACT. WHERE THE LOT
HAS NO BLOCK THE ROW HOLDS FOR NOTHING (P4.k6Hear gives none where P4.headBefore Z G = none):
that there is just one block is not shown here, and wants two premises more. It pays none of hS,
hR, hZ, hG, and no example in this file shows that these four can be met together; whether the
head's member at storedPublicFiles (AtFullSide.Top.headMember_zFull, whose own Limits say what it is worth)
gives them was not examined for this file. THAT THE PLACES OF ANY PROOF FILE ARE THE WRITTEN
ONES (B.spots = spotsW: the premise h₁ of ProofFile.Sk.Full.rows_by_place) IS NOT SAID HERE: k6_nameW
speaks of a written list alone (spotsW, Johnson/Desc/ProofFile/Law/Skel/Full/Data.lean), which
by that file's head Lean's evaluator printed off the makers themselves: no independent witness.
WHAT A CALLER MUST STILL BRING: that P4.k6Lot Z is one of its seat's lots; hG at its own B.G₀;
h₁. What the written table of rounds is worth: as the head of Johnson/AtFull/Rounds/K6.lean
says.
WORDS, OBJECT, LETTERS. As in K6.lean: the lot P4.k6Lot Z: the output head's own rounds, at "H:4"
(the kind K6). nameW a: the name of the first written place at a, the empty name where there is none
(Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean). isNameB: Johnson/AtFull/Rounds/K7Name.lean.
USER. The premise w of ProofFile.Sk.Full.rows_by_place at Q := Lst listAt, at this lot. The batchings'
premise is not touched here: k6_no_batch (K6.lean) pays it at this lot.
WHAT IT IS. k6_nameW, BY LEAN's KERNEL: the written name at K6's place in segment 24 is "H:4".
k6_row_lists: Lst listAt (nameW b.place) b.rounds AT EACH BLOCK OF THE LOT, FROM THE SCOPE, THE
READING AND THE TWO RETURNS ALONE: K6.lean's k6_lists_at at N := nameW: no premise on a name.
THE LOOK-UP CAN FAIL, AT EACH FIELD OF THE PLACE ALONE: k6_nameW_not23 (the segment),
k6_nameW_notK7 (the kind), k6_nameW_notPiece, k6_nameW_notChain, k6_nameW_notOut (no segment); AT
THE TWO WRITTEN PLACES BESIDE, which bear other names: k6_nameW_notBefore (piece 3, the kind K3),
k6_nameW_notBehind (piece 5, the kind K1); AND AT THE NAME: k6_nameW_notOther (K6's own place does
not bear "H:3"). k6_nameW_none23, k6_nameW_noneK7: at the first two the look-up gives the empty
name: so no written place with a name stands there.

-/
import Johnson.AtFull.Rounds.K6
import Johnson.AtFull.Rounds.K7Name

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open ProofFile.Sk (Lst)
open ProofFile.Sk.Full (nameW)
open VerifiableInference.Desc (Place)

set_option maxRecDepth 1000000 in
/-- **The written name at K6's place in segment 24 is "H:4"**: the test says yes. -/
theorem k6_nameW_yes : isNameB ⟨1, some 24, 4, .K6⟩ "H:4" = true := by
  decide +kernel

/-- The same as an equation. -/
theorem k6_nameW : nameW ⟨1, some 24, 4, .K6⟩ = "H:4" :=
  eq_of_beq (k6_nameW_yes : (nameW ⟨1, some 24, 4, .K6⟩ == "H:4") = true)

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at the segment alone. -/
theorem k6_nameW_not23 : isNameB ⟨1, some 23, 4, .K6⟩ "H:4" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at the kind alone. -/
theorem k6_nameW_notK7 : isNameB ⟨1, some 24, 4, .K7⟩ "H:4" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at the piece alone. -/
theorem k6_nameW_notPiece : isNameB ⟨1, some 24, 3, .K6⟩ "H:4" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at the chain alone. -/
theorem k6_nameW_notChain : isNameB ⟨2, some 24, 4, .K6⟩ "H:4" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at a place outside the segments. -/
theorem k6_nameW_notOut : isNameB ⟨1, none, 4, .K6⟩ "H:4" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written place in front bears another name. -/
theorem k6_nameW_notBefore : isNameB ⟨1, some 24, 3, .K3⟩ "H:4" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written place behind bears another name. -/
theorem k6_nameW_notBehind : isNameB ⟨1, some 24, 5, .K1⟩ "H:4" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- K6's own place does not bear the name of the place in front. -/
theorem k6_nameW_notOther : isNameB ⟨1, some 24, 4, .K6⟩ "H:3" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At K6's place in segment 23 the look-up gives the empty name. -/
theorem k6_nameW_none23 : isNameB ⟨1, some 23, 4, .K6⟩ "" = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At the same numbers under the kind K7 the look-up gives the empty name. -/
theorem k6_nameW_noneK7 : isNameB ⟨1, some 24, 4, .K7⟩ "" = true := by
  decide +kernel

/-- **THE LOT's ROW, FROM THE SCOPE, THE READING AND THE TWO RETURNS ALONE.** -/
theorem k6_row_lists {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    ∀ b ∈ (P4.k6Lot Z).blocks G, Lst listAt (nameW b.place) b.rounds :=
  k6_lists_at hS hR hZ hG nameW k6_nameW

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.k6_nameW_yes
#print axioms Johnson.AtFull.Rounds.k6_nameW
#print axioms Johnson.AtFull.Rounds.k6_nameW_not23
#print axioms Johnson.AtFull.Rounds.k6_nameW_notK7
#print axioms Johnson.AtFull.Rounds.k6_nameW_notPiece
#print axioms Johnson.AtFull.Rounds.k6_nameW_notChain
#print axioms Johnson.AtFull.Rounds.k6_nameW_notOut
#print axioms Johnson.AtFull.Rounds.k6_nameW_notBefore
#print axioms Johnson.AtFull.Rounds.k6_nameW_notBehind
#print axioms Johnson.AtFull.Rounds.k6_nameW_notOther
#print axioms Johnson.AtFull.Rounds.k6_nameW_none23
#print axioms Johnson.AtFull.Rounds.k6_nameW_noneK7
#print axioms Johnson.AtFull.Rounds.k6_row_lists
