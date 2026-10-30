-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastXAt.lean: THE PREMISE hX OF `LLT25.own3_at_top`
(Johnson/LLT25R/LastTop.lean) AT THE
ONE X: X := `Sh.X (Sh.planAt Z N G) 12`, the shared table's constant's tests in the promise's slot
at the shared chain's last border. A JOIN OF FILES OF Johnson/LLT25R/ AND Johnson/Desc/K14/Law/: two
equations by unfolding, three calls.
  `x_blind` · `tests_blind`: neither `Sh.X (Sh.planAt Z N G)` nor `Sh.Tests (Sh.planAt Z N G)`
    reads the letter G (the IOP as written in Lean): so the premise is one at the description pulled
    back and at the one not pulled back.
  `xSamples_of_tests`: **`XSamples (p14At Z).codes (p14At Z).S (Sh.X (Sh.planAt Z N G) 12)`** FROM
    ONE PREMISE, `Sh.Tests (Sh.planAt Z N G)` ("all the named tests on the parameters say true": an
    equation of Bools). It is `Sh.omega_sampled_at`
    (Johnson/Desc/K14/Law/SharedConstLastAt.lean); what is new is that Lean takes that conclusion
    for `XSamples` (its `seatY` unfolds to the written seat).
  `xSamples_laid`: the same at EVERY G from `Sh.LaidAt o pol lay KL F Z N x` (F the verifier's own).
  `xSamples_in_scope`: the same at every G from the nine premises of `Sh.tests_in_scope`: THE DOOR's
    TWO PINS (hs · hf) ARE AMONG THEM.
Limits. `XSamples` is a sentence "wherever X says yes": it is true of an X that never says yes; that
X says yes at a reached last state of the shared chain is `Sh.X_reached_in_scope`,
not here (`x_blind` carries it to any G). OWED BY NOBODY YET among the nine: hs · hf · hl.
(Where this and lean/THEOREM.md differ, the page holds.)
A caller
whose letters Z and N are tied to the files by no binder brings pub and places, or carries the named
tests. Nothing on soundness.
-/
import Johnson.LLT25R.LastSeedO
import Johnson.Desc.K14.Law.SharedConstLastAt
import Johnson.Desc.K14.Law.SharedConstLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open OnBytes OnBytes.Params
open VerifiableInference.Desc (FileDescription)
open ToldDesc (p14At)
open Desc.K14.Law
open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)

variable {Xi Xi' : Type} (Z : ProofFile.Pub) (N : H2U.Places4) (G : FileDescription Xi) (G' : FileDescription Xi')

/-- **The tests in the slot do not read the description.** -/
theorem x_blind : Sh.X (Sh.planAt Z N G) = Sh.X (Sh.planAt Z N G') := rfl

/-- **The named tests on the parameters do not read the description.** -/
theorem tests_blind : Sh.Tests (Sh.planAt Z N G) = Sh.Tests (Sh.planAt Z N G') := rfl

/-- **hX at the one X, from the named tests.** -/
theorem xSamples_of_tests (hT : Sh.Tests (Sh.planAt Z N G)) :
    XSamples (p14At Z).codes (p14At Z).S (Sh.X (Sh.planAt Z N G) 12) :=
  fun d h => Sh.omega_sampled_at Z N G hT d h

/-- **hX at the one X, at every description, from "the verifier's own value is laid".** -/
theorem xSamples_laid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {x : LinSized} (L : Sh.LaidAt o pol lay KL F Z N x) :
    XSamples (p14At Z).codes (p14At Z).S (Sh.X (Sh.planAt Z N G) 12) :=
  xSamples_of_tests Z N G (tests_blind Z N F G ▸ Sh.tests_laid L)

/-- **hX at the one X, at every description, in the goals' scope, under the door's two pins.** -/
theorem xSamples_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {x : LinSized}
    (hW : VerifierAndGoals.InScope W = true) (made : ProofFile.onlineDescription o W.pol W.lay W.KL = .ok F)
    (ok : F.planOk = true) (pub : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (places : H2U.placesOfMade Z.made = .ok N)
    (hs : VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hx : realSized = some (x, codesFull2)) :
    XSamples (p14At Z).codes (p14At Z).S (Sh.X (Sh.planAt Z N G) 12) :=
  xSamples_laid Z N G (Sh.laid_in_scope hW made ok pub places hs hf hl hx)

end LLT25

#print axioms LLT25.x_blind
#print axioms LLT25.tests_blind
#print axioms LLT25.xSamples_of_tests
#print axioms LLT25.xSamples_laid
#print axioms LLT25.xSamples_in_scope
