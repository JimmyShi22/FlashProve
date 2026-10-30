-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyFitsWritten.lean: the kind "the code switch" (K2): AT THE
WRITTEN PLACES AND SEGMENTS, A KEPT COPY AND THE MESSAGE THAT IT REPEATS FIT: at each of the 24
switches that have a switch in front, at each of their 34 kept copies: eleven of the public premises
that `msgOff_copy_is_senders` (Honest/K2/Law/MsgOffCopy.lean) asks on shapes, codes and numbers, two
of the eleven in part. PUBLIC DATA ALONE. Three definitions: the pairs, the test at one copy, the
test at all. Five statements with their proofs: closed facts, four of them controls.

  `copyPairs`               a switch, the switch in front of it, the segment between
  `copyFitsAt`              THE TEST at one copy: eleven clauses; f bends the copy's shape
  `copyFitsAll`             the test at every copy of every pair
  `copyFits_written`        IT ACCEPTS: with the two counts beside it
  `copyFits_rejects_rows`   it rejects where every copy's shape is given a main row more
  `copyFits_rejects_code`   it rejects where every copy's shape is given the next code's number
  `copyFits_rejects_bare`   it rejects where every copy's shape is left no main row
  `copyFits_rejects_field`  it rejects where every copy's shape is laid over the extension field

The eleven, with the premise's name there: n lies in front of the sender's last message (hn₀) · the
repeated message has the copy's shape (hs) · so has the group's kept shape number i (hsk) · the
segment's code has the copy's code's length (hell) · the copy has a main row (hm) · its pad fits the
row (hpad) · the group's member n and the repeated message agree on the field (hdeg) · i is below
the number of the group's kept shapes (ha') · the segment's first sending is the sender's (hSent) ·
just one segment lies between the two links (of hS: its length) · the two places' lists of codes
agree in every code's two lengths (of hc: what the laws read).

Limits. FIVE CLOSED FACTS BY EVALUATION IN LEAN's KERNEL, at the closed lists `placesW`, `segsW` of
Honest/K2/Law/PlacesWritten.lean: not carried to the head's own lists here. THE COUNTS STAND IN THE
SAME STATEMENT. A TEST, NOT THE PREMISES: that it gives hn₀ … hSent in their own form at a member of
the list is not proved here. hS AND hc ARE TRIED IN PART ALONE: the length of what lies between; the
codes' lengths. hSz (the segment's sizes are the sender's) is not tried: `Sizes` has no decidable
equality. NOT TRIED EITHER: hw, hn; h3, hbare, ha1 (these three: `copy_shape_ok`,
Honest/K2/Law/KeptCopyShape.lean). THE TWO COPIES AT LINK 1 HAVE NO SWITCH IN FRONT: not spoken of.
THE CONTROLS ARE WEAK: each of the four changes the copy's shape and leaves the repeated message's
and the group's kept shape as they are: so hs and hsk are false at all four, whatever the other
clauses say: THE FOUR SHOW THAT THESE TWO CLAUSES CAN REJECT, AND NO MORE: hn₀, hell, hm, hpad,
hdeg, ha', hSent and the two in part have no control of their own. Nothing on the book, the data,
the challenges or a run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.GroupMembers
import Johnson.Desc.ProofFile.Honest.K2.Law.PadPlaces
import Johnson.Desc.K2.Honest.Carry.OfRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- A switch p₀, the switch p behind it, and the segment between: for each written place that has a
place with the link in front. -/
def copyPairs : List (SwitchPlace × SwitchPlace × SegmentPub) :=
  placesW.filterMap fun p =>
    match placesW.find? (fun q => q.link + 1 == p.link), segsW[p.link - 1]? with
    | some p₀, some S => some (p₀, p, S)
    | _, _ => none

/-- **A PUBLIC TEST**, at the kept copy number i of p. f: the identity; or what bends the copy's
shape, for a control. -/
def copyFitsAt (f : OnBytes.OracleShape → OnBytes.OracleShape) (p₀ p : SwitchPlace)
    (S : SegmentPub) (i : Nat) : Bool :=
  let M := membersOfSeg S true
  let n := VerifiableInference.Desc.K2.Honest.keptNo M i
  let sC := f ((switchSent p.sizes p.others).getD (1 + i) default).shape
  let s₀ := ((switchSent p₀.sizes p₀.others).getD n default).shape
  let kept := (M.filter (·.kept)).map (·.shape)
  let ell := (p.sizes.codes.base.getD sC.code default).ell
  decide (n < (switchSent p₀.sizes p₀.others).size - 1) && s₀ == sC && kept.getD i {} == sC &&
    (S.sizes.codes.base.getD S.sizes.code default).ell == ell && decide (0 < sC.mainRows) &&
    decide ((K1.stepsOf p.sizes.codes sC none).pad ≤ ell) &&
    (((VerifiableInference.Desc.K2.Honest.shapeOf M n).mainDeg == 3) == (s₀.mainDeg == 3)) &&
    decide (i < kept.length) && S.sent.headD #[] == switchSent p₀.sizes p₀.others &&
    ((segsW.take p.link).drop p₀.link).length == 1 &&
    ((p₀.sizes.codes.base.toList.map fun c => (c.ell, c.r)) ==
        (p.sizes.codes.base.toList.map fun c => (c.ell, c.r)) &&
      (p₀.sizes.codes.mask.toList.map fun c => (c.ell, c.r)) ==
        (p.sizes.codes.mask.toList.map fun c => (c.ell, c.r)))

/-- The test at every kept copy of every pair. -/
def copyFitsAll (f : OnBytes.OracleShape → OnBytes.OracleShape) : Bool :=
  copyPairs.all fun x =>
    (List.range x.2.1.sizes.kept.length).all fun i => copyFitsAt f x.1 x.2.1 x.2.2 i

/-- **The test accepts at the written places**: 24 pairs, with 34 kept copies. -/
theorem copyFits_written :
    copyPairs.length = 24 ∧ (copyPairs.map fun x => x.2.1.sizes.kept.length).sum = 34 ∧
      copyFitsAll id = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **Four controls.** A main row more at every copy's shape. -/
theorem copyFits_rejects_rows :
    copyFitsAll (fun s => { s with mainRows := s.mainRows + 1 }) = false := by
  decide +kernel

/-- The next code's number at every copy's shape. -/
theorem copyFits_rejects_code : copyFitsAll (fun s => { s with code := s.code + 1 }) = false := by
  decide +kernel

/-- No main row at any copy's shape. -/
theorem copyFits_rejects_bare : copyFitsAll (fun s => { s with mainRows := 0 }) = false := by
  decide +kernel

/-- Every copy's shape over the extension field. -/
theorem copyFits_rejects_field : copyFitsAll (fun s => { s with mainDeg := 3 }) = false := by
  decide +kernel

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.copyPairs
#print axioms ProofFile.Honest.K2.Law.copyFitsAt
#print axioms ProofFile.Honest.K2.Law.copyFitsAll
#print axioms ProofFile.Honest.K2.Law.copyFits_written
#print axioms ProofFile.Honest.K2.Law.copyFits_rejects_rows
#print axioms ProofFile.Honest.K2.Law.copyFits_rejects_code
#print axioms ProofFile.Honest.K2.Law.copyFits_rejects_bare
#print axioms ProofFile.Honest.K2.Law.copyFits_rejects_field
