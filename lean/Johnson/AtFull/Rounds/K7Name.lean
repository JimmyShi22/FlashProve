-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Rounds/K7Name.lean.
WHAT IT DOES NOT SHOW. No soundness. NO EXAMPLE OF THE HEAD IS SHOWN IN THIS FILE; two, at storedPublicFiles and
at zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what
they are worth. A JOINING OF
ONE CALL AND ONE CLOSED FACT. It pays none of hS, hR, hZ, hG. THAT THE PLACES OF ANY PROOF FILE ARE
THE WRITTEN ONES (B.spots = spotsW: the premise h₁ of ProofFile.Sk.Full.rows_by_place) IS NOT SAID HERE:
h1_nameW speaks of a written list alone (spotsW, Johnson/Desc/ProofFile/Law/Skel/Full/Data.lean),
which by that file's head Lean's evaluator printed off the makers themselves: no independent
witness. WHAT ITS USER MUST STILL BRING: that h1Lot is one of its seat's lots; hG at its own
B.G₀ (so that its seat's links are pureRoad's, and baseOf's return); h₁. What the written table of
rounds is worth: as the head of Johnson/AtFull/Rounds/K7.lean says.
WORDS, OBJECT, LETTERS. As in K7.lean: the lot h1Lot: the one block at "H:1", the next token's place
(K7). nameW a: the name of the first written place at a, the empty name where there is none
(Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean).
USER. The premise w of ProofFile.Sk.Full.rows_by_place at Q := Lst listAt, at this lot. The batchings'
premise (hK, wK) is not touched here: h1_no_batch (K7.lean) pays it at this lot.
WHAT IT IS. h1_nameW, BY LEAN's KERNEL: the written name at K7's place in segment 24 is "H:1".
h1_row_lists: THE LOT's SECOND ROW: Lst listAt (nameW b.place) b.rounds AT EACH BLOCK OF THE LOT,
FROM THE SCOPE, THE READING AND THE TWO RETURNS ALONE: no spot, no list of spots, no premise on a
name.
THE LOOK-UP (isNameB: yes and no's on one function) CAN FAIL, AT EACH FIELD OF THE PLACE ALONE:
h1_nameW_not23 (the segment), h1_nameW_notK6 (the kind), h1_nameW_notPiece, h1_nameW_notChain,
h1_nameW_notOut (no segment); and h1_nameW_notBeside (the written place beside, piece 2 of the kind
K2, which bears another name). h1_nameW_none23, h1_nameW_noneK6: at the first two the look-up gives
the empty name: so no written place with a name stands there.

-/
import Johnson.AtFull.Rounds.K7
import Johnson.Desc.ProofFile.Law.Skel.Full.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open ProofFile.Sk (Lst)
open ProofFile.Sk.Full (nameW)
open VerifiableInference.Desc (Place)
open Johnson.AtFull.Lots (h1Lot)

/-- The written name at the place a is n. -/
def isNameB (a : Place) (n : String) : Bool := nameW a == n

set_option maxRecDepth 1000000 in
/-- **The written name at K7's place in segment 24 is "H:1"**: the test says yes. -/
theorem h1_nameW_yes : isNameB ⟨1, some 24, 1, .K7⟩ "H:1" = true := by
  decide +kernel

/-- The same as an equation. -/
theorem h1_nameW : nameW ⟨1, some 24, 1, .K7⟩ = "H:1" :=
  eq_of_beq (h1_nameW_yes : (nameW ⟨1, some 24, 1, .K7⟩ == "H:1") = true)

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at the segment. -/
theorem h1_nameW_not23 : isNameB ⟨1, some 23, 1, .K7⟩ "H:1" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at the piece: the place beside bears another name. -/
theorem h1_nameW_notBeside : isNameB ⟨1, some 24, 2, .K2⟩ "H:1" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at the kind. -/
theorem h1_nameW_notK6 : isNameB ⟨1, some 24, 1, .K6⟩ "H:1" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at the piece alone. -/
theorem h1_nameW_notPiece : isNameB ⟨1, some 24, 2, .K7⟩ "H:1" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at the chain alone. -/
theorem h1_nameW_notChain : isNameB ⟨2, some 24, 1, .K7⟩ "H:1" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The look-up can fail, at a place outside the segments. -/
theorem h1_nameW_notOut : isNameB ⟨1, none, 1, .K7⟩ "H:1" = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At K7's place in segment 23 the look-up gives the empty name. -/
theorem h1_nameW_none23 : isNameB ⟨1, some 23, 1, .K7⟩ "" = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At the same numbers under the kind K6 the look-up gives the empty name. -/
theorem h1_nameW_noneK6 : isNameB ⟨1, some 24, 1, .K6⟩ "" = true := by
  decide +kernel

/-- **THE LOT's SECOND ROW, FROM THE SCOPE, THE READING AND THE TWO RETURNS ALONE.** -/
theorem h1_row_lists {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    ∀ b ∈ h1Lot.blocks G, Lst listAt (nameW b.place) b.rounds :=
  h1_lists_at hS hR hZ hG nameW h1_nameW

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.h1_nameW_yes
#print axioms Johnson.AtFull.Rounds.h1_nameW
#print axioms Johnson.AtFull.Rounds.h1_nameW_not23
#print axioms Johnson.AtFull.Rounds.h1_nameW_notBeside
#print axioms Johnson.AtFull.Rounds.h1_nameW_notK6
#print axioms Johnson.AtFull.Rounds.h1_nameW_notPiece
#print axioms Johnson.AtFull.Rounds.h1_nameW_notChain
#print axioms Johnson.AtFull.Rounds.h1_nameW_notOut
#print axioms Johnson.AtFull.Rounds.h1_nameW_none23
#print axioms Johnson.AtFull.Rounds.h1_nameW_noneK6
#print axioms Johnson.AtFull.Rounds.h1_row_lists
