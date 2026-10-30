-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactFirstKR.lean: `exact_first` (Sim/ExactFirst.lean) at the
written place of the key file's test on the ranges, at the full size (`piKRFull`,
Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean): the frame's own sentence `exact` at that test's first
member, at every `On` and every `bud`, with every tie on public numbers paid by the kernel's own
evaluation. It is stated at a state on entry that is made of the plan's public part, not shown to be
the verifier's. It is shown at no job that is played. Asked of the two jobs' public letters alone:
both stand at the place; both say that the fresh table has come earlier. Nothing is asked of a run.
General in the face φ (`Face`), the side σ (`Side`), the two jobs J and Js and the numbers chain and
firstTree. Sim/ExactSide.lean calls `exact_first_KR`. Statements and proofs.

What it is worth: little by itself: see Sim/ExactFirst.lean's head: the same 2k + 1 coefficients
are shown elsewhere in a run, and nothing here speaks of that.

Terms. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean with Side.lean next to it. `exact` is a
field of its structure `Good` (Side.lean); `ExactMember`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean) is that field's text at one member, and "the
sentence" is that proposition. `On` and `bud` are the last two parameters of `Good`: a condition at
a part's start, and which positions may be read at given challenges. A job J (`TestJob`,
Johnson/Desc/ProofFile/Honest/K12/Test.lean) is what a caller supplies for its test, and the
simulators' job Js (`SimJob`, Sim/Sims.lean) is what it says of the test to the simulators. `J.p`
(`P12`) holds the test's parameters; a written place is a `P12` written out as a closed term. The
first member is `firstMember J Js` (Sim/Row.lean): the test's first rounds, with the first part and
its simulator's form (`firstSim`, Sim/Sims.lean). A letter is a free parameter, or a field that the
caller fills. A tie is a condition that a statement takes as a hypothesis; the public ties are the
five fields of `FirstPub` (Sim/ExactFirst.lean). Asked: taken as a hypothesis. Paid: proved. Laid:
built.

  `exact_first_KR`: the statement: `ExactMember φ σ chain firstTree On bud (firstMember J Js)`,
    under the four hypotheses below; at a state on entry that is made of the plan's public part, not
    shown to be the verifier's
  `firstPub_KR`: the public ties hold: `FirstPub J Js`, under the same four hypotheses

By what. `firstPub_KR` takes the fields `place` and `own` from hp and ho, `form` from `formPubB_KR`
(Johnson/Desc/ProofFile/Honest/K12/FormPubAt.lean), `enough` from `count_KRs` and `tables` from
`tables_KR` (both in Sim/ExactAtKR.lean). Each of these three ends in `decide +kernel`, an
evaluation in Lean's kernel. `exact_first_KR` is `exact_first` (Sim/ExactFirst.lean) at hfr and
`firstPub_KR`.

Hypotheses. Both theorems have the same four; `exact_first_KR` has them next to those inside
`ExactMember`:
  `hJ : J.p = piKRFull`: the job is at the written place
  `hfr : J.fresh.isNone = false`: the job says that the first fold's fresh table has come earlier
  `hp : Js.p = J.p`, `ho : Js.own = false`: the simulators' job is at the same place and says the
    same of the table

Limits.
- It is stated at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: the job's state on entry is a field of the free parameter J (`TestJob`), and nothing
  here compares it with a verifier's state.
- Those of Sim/ExactFirst.lean.
- J and Js are letters: no job is laid here; as nothing is asked of a run, the sentence holds of
  whatever job is laid at the place with these public letters.
- Who sent the table that has come earlier is not named: hfr says only that `J.fresh` is not `none`.
- It is the sentence at one member, not the field `exact` at a side: σ is a free parameter, and that
  a side has this member is not stated here.
- Some of the place's numbers are a print's word: for these the print of a run of Lean's evaluator
  is trusted (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean, Limits, which names them).
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactAtKR

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open H2K.Member (piKRFull)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

/-- The public ties hold. The fields `form`, `enough` and `tables` come from evaluations in Lean's
kernel; `place` and `own` are hp and ho. -/
theorem firstPub_KR (J : TestJob W X) (Js : SimJob Pb) (hJ : J.p = piKRFull)
    (hfr : J.fresh.isNone = false) (hp : Js.p = J.p) (ho : Js.own = false) : FirstPub J Js :=
  ⟨hp, ho, by rw [hJ]; exact formPubB_KR, by rw [hJ, count_KRs]; exact Nat.le_add_right _ _,
    tables_KR J hJ hfr⟩

/-- **The frame's sentence at the first member of the key file's test on the ranges, at every On and
bud.** At a state on entry that is made of the plan's public part, not shown to be the verifier's.
It is shown at no job that is played: J and Js are free parameters. -/
theorem exact_first_KR (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop) (hJ : J.p = piKRFull)
    (hfr : J.fresh.isNone = false) (hp : Js.p = J.p) (ho : Js.own = false) :
    ExactMember φ σ chain firstTree On bud (firstMember J Js) :=
  exact_first φ σ J Js chain firstTree On bud hfr (firstPub_KR J Js hJ hfr hp ho)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.firstPub_KR
#print axioms ProofFile.Honest.K12.exact_first_KR
