-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsFinal.lean, OVER ANOTHER SET OF THIS PROJECT's LEAN FILES: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre» (Johnson/Desc/Sound/SmpPlaces.lean): Johnson/IMR/SendsWhole.lean's TWO PREMISES ON THE PLAN AT 354 ARE LAID IN, BY LEMMAS OF K12's FILES, CALLED (Johnson/Desc/K12/Law/OwnMaskAtLast.lean; it needs that set of files alone): ho: p12OfMade_own (no premise) · hp: planOk_of_retype, from
«THE SUB-PROTOCOL NUMBER 354 OF THE FLAT LIST PASSES ITS TEST ON THE PLAN», drawn from blocksOk c.blocksInOrder = true.
  hp_of_planOk      in scope: blocksOk c.blocksInOrder = true ⟹ (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made)).planOk = true.
  debts_final       SendDebts 0 Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c (ProofFile.startS Z p): ALL 358 NUMBERS, in scope, under blocksOk c.blocksInOrder = true ALONE.
  seats_final       THE FIELD's OWN Bool AND placesAre, BEHIND THE FIRST k SUB-PROTOCOLS, k ≤ 358.
  seats_planOk      the same from F.planOk = true (Johnson/IMR/PlanOkFlat.lean's
                    blocksOk_of_planOk). (hp_of_planOk's kin: planOk_at_open [not in this library]:
                    from F.planOk, by another road; not called here.)
PREMISES THAT STAY, BY NAME: hpl : blocksOk c.blocksInOrder = true (every sub-protocol of the flat list
passes its test on the plan and is shaped; from F.planOk = true by blocksOk_of_planOk; spent at 354
alone) · hu : the first state bears no mark · hB : the plan's test sendsAreB (a run is said to have
evaluated it at three sets of public files: not held by this file's writer; in scope, by theorem:
its planner's half is not here; the rest is
typed by nobody) · hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some Ld (what names the tables' Ld).
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
No soundness.
-/
import Johnson.IMR.SendsWhole
import Johnson.IMR.PlanOkFlat
import Johnson.Desc.K12.Law.OwnMaskAtLast

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Door (snAt)
open H2K.JointK H2K.Out
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The proximity test's own test on the plan, from the description's. -/
theorem hp_of_planOk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : VerifiableInference.Desc.blocksOk c.blocksInOrder = true) :
    (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Blk').planOk = true := by
  obtain ⟨-, ⟨b, b', e1, -, rfl, hla⟩, -⟩ := back_of O
  have hix := (back_numbers hS hR O).1 1 b e1
  have h1 := List.all_eq_true.1 hpl _ (List.mem_of_getElem? hix)
  rw [Bool.and_eq_true] at h1
  have h2 : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := h1.1
  rw [Bool.and_eq_true, alone_planOk hla] at h2
  exact H2K.Made.planOk_of_retype _ h2.1

/-- **ALL 358.** -/
theorem debts_final (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub)
    (hpl : VerifiableInference.Desc.blocksOk c.blocksInOrder = true) :
    SendDebts 0 Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c (ProofFile.startS Z p) :=
  debts_whole hS hR O p (hp_of_planOk hS hR O hpl) (H2K.Made.p12OfMade_own _)

/-- **THE FIELD's OWN Bool, AND placesAre.** -/
theorem seats_final (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub)
    (hpl : VerifiableInference.Desc.blocksOk c.blocksInOrder = true)
    (hu : (ProofFile.startS Z p).failed = none) {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hB : VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    (hLd : VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some Ld)
    {k : ℕ} (hk : k ≤ 358) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    VerifiableInference.Desc.K12.Door.atFirstSeats Ld out.1 = true ∧
      VerifiableInference.Desc.placesAre Ld.places out.1.st out.1.book = true :=
  seats_whole hS hR O p (hp_of_planOk hS hR O hpl) (H2K.Made.p12OfMade_own _) hu hB hLd hk hf

/-- **… FROM THE DESCRIPTION's OWN TESTS ON THE PLAN.** -/
theorem seats_planOk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub)
    (hF : F.planOk = true)
    (hu : (ProofFile.startS Z p).failed = none) {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hB : VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    (hLd : VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some Ld)
    {k : ℕ} (hk : k ≤ 358) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    VerifiableInference.Desc.K12.Door.atFirstSeats Ld out.1 = true ∧
      VerifiableInference.Desc.placesAre Ld.places out.1.st out.1.book = true :=
  seats_final hS hR O p (blocksOk_of_planOk O hF) hu hB hLd hk hf

end

end IM

#print axioms IM.seats_planOk
#print axioms IM.hp_of_planOk
#print axioms IM.debts_final
#print axioms IM.seats_final
