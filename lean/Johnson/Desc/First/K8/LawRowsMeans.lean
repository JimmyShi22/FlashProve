-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawRowsMeans.lean: THE SMALLNESS TEST, ITS FIRST HALF: THE ROW ON WHAT A YES
MEANS, WITH THE SEAT'S OWN READINGS HELD.

WHY THIS FILE. The row `K08LawHearing` (Johnson/Desc/First/K8/LawRowsText.lean) holds the kind's
TEXT: strike one of its tests and the proofs break. It does not hold three of the SEAT's readings at
the first chain's carried record (Johnson/Desc/First/K8/AtS.lean): its first conjunct is general in
the seat, and its conjuncts at that seat go one way, from a yes, and speak of tests (d), (e), (f)
and of the writing alone. It was shown by Lean: with (a) "the list of tables is closed", (b) "no
count of batched rows is owed" and (c) "no matrix is drawn yet" all made idle in the seat, the four
rows stayed proved. Here the row gains what holds them:
  `HearMeansAtRecord`: a closed proposition: AT THE CARRIED RECORD the decision says yes on one
    round, and hands on s', IF AND ONLY IF `MeansAtS p s r s'`
    (Johnson/Desc/First/K8/HearMeans.lean): a link is open with the smallness test's record tl; tl's
    list of tables is closed; no count is owed; tl's field for the matrix is empty and no draw is
    counted; tl's numbers are the place's; and s' is s with the round's entries and the first
    columns laid into tl. IN THE RECORD'S OWN FIELDS: no reading of the seat is named in it.
  `HearOneRound`: a yes is on one round alone.
  `K08LawHearingAtRecord` := `K08LawHearing` ∧ `HearMeansAtRecord` ∧ `HearOneRound`, with a theorem
    of just that type.
Nothing is proved anew: `decide_atS_iff`, `decide_one`, `k08LawHearing`, with their arguments bound.
Limits. What the fields MEAN is not said: that the list which is closed is the right one; that the
count which is owed is the right count. The decision, not the step: that the frame asks the round's
shape in front of the decision is the first conjunct's (`HearLaw`).

-/
import Johnson.Desc.First.K8.LawRowsText
import Johnson.Desc.First.K8.HearMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model

/-- At the carried record a yes of the decision means, in the record's own fields, just this. -/
def HearMeansAtRecord : Prop :=
  ∀ (Cl : Type) (p : Par) (s s' : S) (r : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [r] gs = .ok s' ↔ MeansAtS p s r s'

theorem hearMeansAtRecord : HearMeansAtRecord := fun _ p s s' r gs => decide_atS_iff p s s' r gs

/-- A yes is on one round alone. -/
def HearOneRound : Prop :=
  ∀ (Cl : Type) (p : Par) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s rs gs = .ok s' → ∃ r, rs = [r]

theorem hearOneRound : HearOneRound := fun _ p s s' rs gs h => decide_one atS p s s' rs gs h

/-- **The row on what a yes means, with the seat's own readings held.** -/
def K08LawHearingAtRecord : Prop := K08LawHearing ∧ HearMeansAtRecord ∧ HearOneRound

theorem k08LawHearingAtRecord : K08LawHearingAtRecord :=
  ⟨k08LawHearing, hearMeansAtRecord, hearOneRound⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.hearMeansAtRecord
#print axioms VerifiableInference.Desc.First.K8.hearOneRound
#print axioms VerifiableInference.Desc.First.K8.k08LawHearingAtRecord
