-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: ON PUBLIC DATA ALONE, UNDER THE HEAD `P5J.AtMgA`: no prover and no filling is read.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupDrawWritten.lean: the kind "lookup" (K3): the closed
test `lookupDrawTest` (Honest/K3/Term/LookupSiteFits.lean) accepts at the three written lists, by
Lean's kernel; six controls, in which it refuses; and the law `siteFits` at every site without a
closed test as a hypothesis. No definition.

Terms. Honest/K3/GLOSSARY.md. The written cut is `cutFirstFull` (358 rows;
Johnson/Desc/Ok/PlanWritten/CutLit.lean); the written list of places is `spotsWritten` (282 places;
Johnson/AtFull/Desc/SpotsWritten.lean); the written entries are `P5T.esFull.1` (48,293 entries;
Johnson/P5T/PlanSeatsFull.lean).

What is shown.
  `lookupDrawWritten`: by Lean's kernel: the test accepts at the three written lists.
  `lookupDrawWrittenRefusesShiftedEntries`: a control, by Lean's kernel: without the first of the
    written entries, so that each entry has the number before its own, the test refuses.
  `lookupDrawWrittenRefusesAnotherName`, `lookupDrawWrittenRefusesNoTrits`: controls, by Lean's
    kernel, at link 0: with entry number 1220 under another name, or with no trits, it refuses.
  `lookupDrawWrittenRefusesALongerRow`: a control, by Lean's kernel: with two rounds in place of one
    in the written cut's seventh row ("G0:5") the test refuses.
  `lookupDrawWrittenRefusesATwinRow`: a control, by Lean's kernel, at link 0: with that row twice it
    refuses.
  `lookupDrawWrittenRefusesLinkTwentyFive`: a control, by Lean's kernel: at link 25 it refuses.
  `lookupSiteFits`: THE LAW: under the head, at every site of `lookSites Zp`:
    `siteFits cF.blocksInOrder s = true`.

Hypotheses that remain. `h`: `P5J.AtMgA`.

Whether the law is empty. As in Honest/K3/Term/LookupBaseWritten.lean. The second clause of
`siteFits` passes idly at a site that names no round; every site on the digits names one
(`siteOnTheDigitsNamesARound`, Honest/K3/Term/LookupSiteFits.lean).

Limits. The closed facts stand at written lists: that these are what the planner makes of any public
files is said under the head alone. Six controls. The full size alone. On public data alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSiteFits
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBaseWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (cutFirstFull)
open Johnson.AtFull.Desc (spotsWritten)
open ProofFile.Honest.K3.Law (siteFits)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
/-- **The closed fact**, by Lean's kernel: the test accepts the three written lists. -/
theorem lookupDrawWritten : lookupDrawTest cutFirstFull spotsWritten P5T.esFull.1 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: every entry one number earlier: refused. -/
theorem lookupDrawWrittenRefusesShiftedEntries :
    lookupDrawTest cutFirstFull spotsWritten (P5T.esFull.1.drop 1) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel, at link 0: entry number 1220 under another name: refused. -/
theorem lookupDrawWrittenRefusesAnotherName :
    lookupDrawTestAt cutFirstFull spotsWritten
      (P5T.esFull.1.modify 1220 fun e => { e with name := "BAT" }) 0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel, at link 0: entry number 1220 with no trits: refused. -/
theorem lookupDrawWrittenRefusesNoTrits :
    lookupDrawTestAt cutFirstFull spotsWritten
      (P5T.esFull.1.modify 1220 fun e => { e with trits := 0 }) 0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel, at link 0: the row "G0:5" twice: refused. -/
theorem lookupDrawWrittenRefusesATwinRow :
    lookupDrawTestAt (cutFirstFull.take 7 ++ cutFirstFull.drop 6) spotsWritten P5T.esFull.1 0 =
      false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: two rounds in the row "G0:5": refused. -/
theorem lookupDrawWrittenRefusesALongerRow :
    lookupDrawTest (cutFirstFull.modify 6 fun row => (row.1, row.2.1, 2, row.2.2.2)) spotsWritten
      P5T.esFull.1 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: at link 25 the test refuses. -/
theorem lookupDrawWrittenRefusesLinkTwentyFive :
    lookupDrawTestAt cutFirstFull spotsWritten P5T.esFull.1 25 = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE PUBLIC TEST `siteFits` ACCEPTS AT EVERY SITE.** Conditional on the head. -/
theorem lookupSiteFits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) : siteFits cF.blocksInOrder s = true :=
  lookupSiteFitsOfWritten lookupBaseWritten lookupDrawWritten h s hs

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupDrawWritten
#print axioms ProofFile.Honest.K3.Term.lookupDrawWrittenRefusesShiftedEntries
#print axioms ProofFile.Honest.K3.Term.lookupDrawWrittenRefusesAnotherName
#print axioms ProofFile.Honest.K3.Term.lookupDrawWrittenRefusesNoTrits
#print axioms ProofFile.Honest.K3.Term.lookupDrawWrittenRefusesATwinRow
#print axioms ProofFile.Honest.K3.Term.lookupDrawWrittenRefusesALongerRow
#print axioms ProofFile.Honest.K3.Term.lookupDrawWrittenRefusesLinkTwentyFive
#print axioms ProofFile.Honest.K3.Term.lookupSiteFits
