-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstLaid.lean: THE ONE PREMISE OF THE COUNTED FORM AT THE SHARED TABLE:
"the verifier's own value is laid": Sh.LaidAt, one structure of six equations and facts that tie the
letters F, Z, N, x of the constant's parameters (Sh.planAt Z N F,
Johnson/Desc/K14/Law/SharedConstAt.lean) to the three files.

  Sh.LaidAt o pol lay KL F Z N x    made: F is the IOP as written in Lean that the verifier makes of
                       its files · ok: the verifier's own test on it accepts · pub: Z is the public
                       value that the road makes of the files · places: N are the places off Z ·
                       sized: x is the typed size · written: Written Z x
  Sh.tests_laid        **LaidAt … → Sh.Tests (planAt Z N F)**: all the named tests on the parameters
  Sh.laid_in_scope     LaidAt in the goals' scope: the field `written` from
                       written_in_scope (Johnson/Goal/Numbers/WrittenInScope.lean), under the door's
                       two pins and "the written data are laid"
  Sh.tests_in_scope    so the named tests there
  Sh.codes_first_in_scope    in scope the shared chain's parameters' codes are the first chain's
                       (both are the written codes)
WHAT IS NOT HERE. No law. That a yes of the verifier gives the premises of laid_in_scope.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstDoor
import Johnson.Goal.Numbers.WrittenInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Sh
open ProofFile ToldDesc
open OnBytes OnBytes.Params
open VerifiableInference.Desc (FileDescription)
open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)

/-- **The verifier's own value is laid**: the shared table's reading of the one premise of the
counted form. (The first table's P5J.LaidAt (LaidOpens.lean) is that premise for every kind: when
it lies among this file's imports, one lemma from it to this structure is owed. The field `written`
stays until Written is had from the goals' scope.) -/
structure LaidAt (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (N : H2U.Places4) (x : LinSized) : Prop where
  made : onlineDescription o pol lay KL = .ok F
  ok : F.planOk = true
  pub : pureRoad.pub o pol lay KL = .ok Z
  places : H2U.placesOfMade Z.made = .ok N
  sized : realSized = some (x, codesFull2)
  written : Written Z x

/-- **All the named tests on the parameters, from the one premise.** -/
theorem tests_laid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {N : H2U.Places4} {x : LinSized} (L : LaidAt o pol lay KL F Z N x) :
    Tests (planAt Z N F) := by
  obtain ⟨Z', N', hZ, hN, hc⟩ := chainOk_descPure L.made L.ok
  obtain rfl : Z' = Z := Except.ok.inj (hZ.symm.trans L.pub)
  obtain rfl : N' = N := Except.ok.inj (hN.symm.trans L.places)
  exact tests_at L.sized L.written L.places F hc

/-- **LaidAt in the goals' scope.** -/
theorem laid_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {N : H2U.Places4} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {x : LinSized}
    (hW : VerifierAndGoals.InScope W = true) (made : onlineDescription o W.pol W.lay W.KL = .ok F)
    (ok : F.planOk = true) (pub : pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (places : H2U.placesOfMade Z.made = .ok N)
    (hs : VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hx : realSized = some (x, codesFull2)) : LaidAt o W.pol W.lay W.KL F Z N x :=
  ⟨made, ok, pub, places, hx, written_in_scope hW pub hs hf hl hx⟩

/-- **All the named tests on the parameters, in the goals' scope.** -/
theorem tests_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {N : H2U.Places4} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {x : LinSized}
    (hW : VerifierAndGoals.InScope W = true) (made : onlineDescription o W.pol W.lay W.KL = .ok F)
    (ok : F.planOk = true) (pub : pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (places : H2U.placesOfMade Z.made = .ok N)
    (hs : VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hx : realSized = some (x, codesFull2)) : Tests (planAt Z N F) :=
  tests_laid (laid_in_scope hW made ok pub places hs hf hl hx)

/-- **In scope the shared chain's parameters' codes are the first chain's.** -/
theorem codes_first_in_scope {Xi : Type} {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {x : LinSized}
    (hW : VerifierAndGoals.InScope W = true) (pub : pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hs : VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hx : realSized = some (x, codesFull2)) (N : H2U.Places4) (G : FileDescription Xi) :
    (planAt Z N G).Q.codes = Z.first.codes :=
  (written_in_scope hW pub hs hf hl hx).codes.trans (first_codes_in_scope hW pub hf).symm

end Desc.K14.Law.Sh

#print axioms Desc.K14.Law.Sh.tests_laid
#print axioms Desc.K14.Law.Sh.tests_in_scope
#print axioms Desc.K14.Law.Sh.codes_first_in_scope
