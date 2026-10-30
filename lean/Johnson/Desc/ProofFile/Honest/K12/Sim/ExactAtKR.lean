-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactAtKR.lean: `exact_plan` (Sim/ExactPlan.lean) at the
written place of the key file's test on the ranges, at the full size (`piKRFull`,
Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean): the frame's own sentence `exact` at that test's
second member, with every tie on public numbers paid by the kernel's own evaluation; four ties on
the two jobs' public letters are asked. It is stated at a state on entry that is made of the plan's
public part, not shown to be the verifier's. What is left is the condition `OnPlan` at the part's
entry and the bound `budOpened`. No job is laid here: J and Js are letters. No property is claimed:
whether a run of the key file's chain meets `OnPlan` is not shown. General in the face φ (`Face`),
the side σ and the numbers chain and firstTree, and in the two jobs J and Js as far as the four ties
leave them free. Sim/ExactFreeKR.lean and Sim/ExactSide.lean call `pubTies_KR`;
Sim/ExactFirstKR.lean calls `count_KRs` and `tables_KR`. Statements and proofs.

Terms. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean with Side.lean next to it. `exact` is a
field of its structure `Good` (Side.lean); `ExactMember`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean) is that field's text at one member, and "the
sentence" is that proposition. A side (`Side`) has a sub-protocol and a list of the prover's parts
(`Part`), each paired with a term of type `Sim`. A member (`Member`) is one part with its number in
the list, its declared rounds and that term; the second member is `restMember J Js` (Sim/Row.lean).
`On` and `bud` are the last two parameters of `Good`: a condition at a part's start, and which
positions may be read at given challenges; the condition `OnPlan` and the bound `budOpened`
(Sim/ExactPlan.lean) are put for them. A place (`P12`) holds the numbers of a proximity test, among
them its list of stages; a written place is a `P12` written out as a closed term. A job J
(`TestJob`, Test.lean, one folder up) is what a caller supplies for its test, and the simulators'
job Js (`SimJob`, Sim/Sims.lean) is what a caller says of its test to the simulators. A letter is a
free parameter, or a field that the caller fills. A tie is a condition that a statement takes as a
hypothesis; the public ties are the eight fields of `PubTies` (Sim/ExactPlan.lean): two on the jobs'
fields (`place`, `own`) and six on public numbers. Paid: proved. Asked: taken as a hypothesis. Laid:
built. A member of a condition is a choice of values at which it holds. The door is the test's
entry. The fresh table is the first fold's; a job says that it has come earlier where
`J.fresh.isNone = false`.

  `exact_at_KR`: the statement: under the four hypotheses below: `ExactMember φ σ chain firstTree`
    at `On` := `onPlan φ J Js codesKeyFull chain firstTree`, at `bud` := `budOpened J.p.nums.stages`
    and at the member `restMember J Js`; at a state on entry that is made of the plan's public part,
    not shown to be the verifier's
  `pubTies_KR`: the public ties hold: at a job at that place whose fresh table has come earlier, and
    a simulators' job at the same place that says the same. In Lean: `PubTies J Js codesKeyFull`
    under the same four hypotheses; `codesKeyFull` (Johnson/Desc/K12/Law/PlacesKeyFull.lean) is the
    key file's table of codes
  `count_KRs`: the place has as many declared rounds (`laidOf`, Johnson/Desc/K12/Law/ReadsK.lean) as
    `firstLen` and `restLen` add up to at its stages. `count_KR` (TermLen.lean, one folder up) is
    another statement: on the number of rounds that `testAll` lists
  `rounds_KR`: at the place's stages `restLen` is 2 + `lenFrom` from the second stage (`stN`) on
  `tables_KR`: `tablesFitB J` passes at every job J with `J.p = piKRFull` and
    `J.fresh.isNone = false`

By what. `exact_at_KR` is `exact_plan` (Sim/ExactPlan.lean) at `pubTies_KR`. `pubTies_KR` has its
fields `place` and `own` from hp, ho and hfr. The six others are `reach_KR_full` (Sim/ReachAt.lean),
`planB_KR` (AtKeyRanges.lean), `formPubB_KR` (FormPubAt.lean), `count_KRs` and `rounds_KR`, each
after rewriting by hJ, and `tables_KR`. Each of the six is proved by `decide +kernel`, an evaluation
in Lean's kernel; `tables_KR` first unfolds `tablesFitB` (FitsAll.lean) and `depthAt` (Test.lean)
and rewrites by hJ and hfr. The definitions that the statements name: `firstLen` (Parts.lean),
`restLen` (HalfSteps.lean), `lenFrom` (TermLen.lean), `stN` (PlanB.lean). The files named in this
paragraph without a folder are one folder up.

Hypotheses. `exact_at_KR` has four, next to those inside `ExactMember`; `pubTies_KR` has the same
four:
  `hJ : J.p = piKRFull`: the job is at the written place
  `hfr : J.fresh.isNone = false`: the job says that the first fold's fresh table has come earlier
  `hp : Js.p = J.p`: the simulators' job is at the same place
  `ho : Js.own = false`: the simulators' job says the same of the table

Limits.
- It is stated at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: the job's state on entry is a field of the free parameter J, and nothing here compares
  it with a verifier's state; the clause `door` of `OnPlan` compares it with the field of the same
  name of Js.
- Those of Sim/ExactPlan.lean: `OnPlan` is asked and has no member here: so the sentence counts
  nothing yet. Among it: the two jobs' letters for the verifier's state at the door agree; the
  prover's data; one clause that still speaks of the part's own challenges.
- `OnPlan` has no value that meets it in the library yet, at this place or at any other: see the
  limits of Sim/ExactPlan.lean.
- It is shown at no job that is played.
- `budOpened` is narrower than `budRest`. `budRest` is in Sim/Row.lean; how the two differ is said
  in the limits of Sim/ExactPlan.lean.
- Some of the place's numbers are a print's word: for these the print of a run of Lean's evaluator
  is trusted. The limits of Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean name them.
- The second member alone.
- One of the numbers that are a print's word is the first switch's declared opening (the field
  `first` of `piKRFull.nums`): the clause "one tree" of `reachB` (Sim/Reach.lean) rests on it here.
- At the level of oracle messages: no root, salt or hash. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactPlan
import Johnson.Desc.ProofFile.Honest.K12.Sim.ReachAt
import Johnson.Desc.ProofFile.Honest.K12.AtKeyRanges

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open H2K.Member (piKRFull codesKeyFull)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

theorem count_KRs : (laidOf piKRFull).length =
    firstLen piKRFull.nums.stages + restLen piKRFull.nums.stages := by decide +kernel

theorem rounds_KR : restLen piKRFull.nums.stages =
    2 + lenFrom (stN piKRFull) (piKRFull.nums.stages.drop 2) := by decide +kernel

/-- Each declared oracle message has the depth and the width of the tree that the term sends. In
Lean: `tablesFitB J` passes at every job J at `piKRFull` with `J.fresh.isNone = false`. The term is
`testAll`; the test takes the depths and widths from `depthAt` and `widthsOf`, which read the stages
and `J.fresh.isNone`. -/
theorem tables_KR (J : TestJob W X) (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false) :
    tablesFitB J = true := by
  unfold tablesFitB depthAt
  rw [hJ, hfr]
  decide +kernel

/-- The public ties hold. In Lean: `PubTies J Js codesKeyFull`, under hJ, hfr, hp and ho. -/
theorem pubTies_KR (J : TestJob W X) (Js : SimJob Pb) (hJ : J.p = piKRFull)
    (hfr : J.fresh.isNone = false) (hp : Js.p = J.p) (ho : Js.own = false) :
    PubTies J Js codesKeyFull :=
  ⟨hp, by rw [ho, hfr], by rw [hJ]; exact reach_KR_full, by rw [hJ]; exact planB_KR,
    by rw [hJ]; exact formPubB_KR, by rw [hJ]; exact count_KRs, by rw [hJ]; exact rounds_KR,
    tables_KR J hJ hfr⟩

/-- **The frame's sentence at the second member of the key file's test on the ranges.** It is stated
at a state on entry that is made of the plan's public part, not shown to be the verifier's. Under
hJ, hfr, hp and ho, at `On` := `onPlan` and `bud` := `budOpened`. `OnPlan` is asked and has no
member here: so the sentence counts nothing yet. -/
theorem exact_at_KR (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (chain firstTree : ℕ) (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false) (hp : Js.p = J.p)
    (ho : Js.own = false) :
    ExactMember φ σ chain firstTree (onPlan φ J Js codesKeyFull chain firstTree)
      (budOpened J.p.nums.stages) (restMember J Js) :=
  exact_plan φ σ J Js codesKeyFull chain firstTree (pubTies_KR J Js hJ hfr hp ho)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.count_KRs
#print axioms ProofFile.Honest.K12.rounds_KR
#print axioms ProofFile.Honest.K12.tables_KR
#print axioms ProofFile.Honest.K12.pubTies_KR
#print axioms ProofFile.Honest.K12.exact_at_KR
