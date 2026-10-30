-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsWhole.lean: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre» (Johnson/Desc/Sound/SmpPlaces.lean): THE LAST CALL: THE DEBT AT THE ONE NUMBER THAT STAYED (354, the proximity test) IS LAID IN: k12_debt (Johnson/IMR/SendsK12.lean, over sends_atFinish, Johnson/Desc/K12/Coin/SendsAtFinish.lean), UNDER TWO PREMISES ON THE
PLAN THAT ARE K12's FILES' TO SHOW: hp · ho. SO ALL 358 NUMBERS STAND: 357 OUTRIGHT, ONE UNDER hp · ho. Compiled with the whole library.
  debts_whole       SendDebts 0 Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c (ProofFile.startS Z p), in scope, under hp · ho.
  seats_whole       THE FIELD's OWN Bool AND placesAre, BEHIND THE FIRST k SUB-PROTOCOLS, k ≤ 358.
PREMISES THAT STAY, BY NAME: hp : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made)).planOk = true · ho : (H2U.p12OfMade Z.made).nums.ownMask = false · hu : the first state bears no mark · hB : the plan's test sendsAreB (a run is said to have evaluated it at three sets of public files: not held by this file's writer; in scope, by theorem: its planner's half
is not here; the rest is typed by nobody) · hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some Ld (what names the tables' Ld).
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
No soundness.
-/
import Johnson.IMR.SendsFences
import Johnson.IMR.SendsK12

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (snAt)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts)
open H2K.JointK H2K.Out
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **ALL 358.** -/
theorem debts_whole (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Blk').planOk = true)
    (ho : (H2U.p12OfMade Z.made).nums.ownMask = false) :
    SendDebts 0 Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c (ProofFile.startS Z p) :=
  debts_354 hS hR O p (k12_debt hp ho)

/-- **THE FIELD's OWN Bool, AND placesAre.** -/
theorem seats_whole (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Blk').planOk = true)
    (ho : (H2U.p12OfMade Z.made).nums.ownMask = false)
    (hu : (ProofFile.startS Z p).failed = none) {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hB : VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    (hLd : VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some Ld)
    {k : ℕ} (hk : k ≤ 358) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    VerifiableInference.Desc.K12.Door.atFirstSeats Ld out.1 = true ∧
      VerifiableInference.Desc.placesAre Ld.places out.1.st out.1.book = true :=
  seats_354 hS hR O p (k12_debt hp ho) hu hB hLd hk hf

end

end IM

#print axioms IM.debts_whole
#print axioms IM.seats_whole
