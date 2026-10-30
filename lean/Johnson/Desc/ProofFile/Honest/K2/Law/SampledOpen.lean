-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SampledOpen.lean: the kind "the code switch" (K2): WHEREVER THE
PROOF FILE's DESCRIPTION IS RETURNED, AT EVERY PLACE OF THE KIND's LOT EVERY MESSAGE OF THE SWITCH's
SENDING THAT HAS A MAIN ROW IS SAMPLED: the premise of `noWord_places`
(Honest/K2/Law/SampledAtPlan.lean), paid. Statements with their proofs; no definition.

  `noWord_places_first`   from the test on the shape in the ground's record "first": the planner's
                 sizes that the lot reads bear that shape (`P1K2.prep_is`,
                 Johnson/P1K2R/P2AtTable.lean)
  `noWord_open`  where the description is returned and opened (`IM.Open`,
                 Johnson/IMR/SeatOpen.lean), at the records without a request: the test has been
                 passed (`P1K2.hok_open`, Johnson/P1K2R/DebtsConst.lean; `IM.Open.first`)

Limits. At the format's second hash function as the library's seats take it. Where the planner's sizes are
not tied to the chain's, or the table of steps has a word that is not known, the lot has no place,
and the sentence is idle. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SampledAtPlan
import Johnson.P1K2R.P2AtTable
import Johnson.P1K2R.DebtsConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

/-- From the test on the shape in the ground's record "first". -/
theorem noWord_places_first {Z : Pub} {G : Ground}
    (h : OnBytes.reqShapeOk G.first.shape = true) :
    ∀ p ∈ switchPlaces Z G, NoWord (switchSent p.sizes p.others) :=
  noWord_places fun P hP => by
    rw [(P1K2.prep_is hP).2.2]
    exact h

/-- **Wherever the proof file's description is returned.** -/
theorem noWord_open {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ p ∈ switchPlaces Z Bs.G₀, NoWord (switchSent p.sizes p.others) :=
  noWord_places_first (by
    rw [O.first]
    exact P1K2.hok_open O)

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.noWord_places_first
#print axioms ProofFile.Honest.K2.noWord_open
