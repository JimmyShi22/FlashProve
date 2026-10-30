-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSeatChain.lean: THE SHARED CHAIN OF EVERY IOP AS WRITTEN IN LEAN THAT
onlineDescription MAKES (a FileDescription; our files call it a description), UNDER ITS TESTS ON THE PLAN: it is
kind K14's chainOf at the letters that the road has made; its sub-protocols pass their tests; it
tells the oracle messages that chainOf tells. For three binders of the ledger's tops
(Johnson/Desc/K14/Law/LedgerLaid.lean): hp, hG, and the letters ch, Q, tests.

  eight_ok            hp from "the chain's sub-protocols pass" (blocksOr_ok,
                      ToldDesc/PlacesAtTable.lean).
  told_of_retype      hG from "the description's shared chain tells what chainOf, retyped, tells"
                      (oracles_retype, Johnson/Desc/Sound/SeamDesc.lean).
  chain_at_descPure   both premises at onlineDescription's F: ∃ Z N, each with the equation that fixes it.
HOW. chain_at_descPure is the first half of shared_fits_descPure's own proof
(ToldDesc/PlacesAtTable.lean), by the same calls: descPure_made, pureZ_make, shared_links,
blocksOk_retype; that theorem states the places alone, so its conclusion does not give these two.
What is not claimed. That a description passes planOk. Nothing on soundness.

-/
import Johnson.ToldDescR.PlacesAtTable
import Johnson.Desc.Sound.SeamDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open ProofFile ToldDesc
open VerifiableInference.Desc (Block Chain FileDescription blocksOk)
open Desc.K14 (blocks blocksOr P14 St p14Of beforePointOf chainOf)
open Desc.K14.Law.Fence (oracles_retype)

/-- **hp**: the kind's eight sub-protocols pass their tests on the plan. -/
theorem eight_ok (ch : OnBytes.Model.Verify.Chains) (Q : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (h : blocksOk (chainOf ch Q tests last).blocksInOrder = true) :
    ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], b.planOk = true := by
  intro b hb
  refine List.all_eq_true.1 (blocksOr_ok ch Q tests last h) b ?_
  unfold blocksOr
  rw [hbl]
  exact hb

/-- **hG**, where the shared chain tells what chainOf, retyped, tells. -/
theorem told_of_retype {Xi Cl' : Type} (G : FileDescription Xi) (ch : OnBytes.Model.Verify.Chains)
    (Q : P14) (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (h : VerifiableInference.Desc.oraclesOf G.shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf ((chainOf ch Q tests last).retype (Cl' := Cl')).blocksInOrder) :
    VerifiableInference.Desc.oraclesOf G.shared.blocksInOrder = VerifiableInference.Desc.oraclesOf (chainOf
               ch Q tests last).blocksInOrder :=
  h.trans (oracles_retype _ rfl)

/-- **At onlineDescription's F, under its tests on the plan.** -/
theorem chain_at_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : onlineDescription o pol lay KL = .ok F) (hp : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4), pureRoad.pub o pol lay KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧
      blocksOk (chainOf Z.p.chains (p14Of Z.p.chains (beforePointOf N))
        (VerifiableInference.Desc.K12.Seat.tests N)
        VerifiableInference.Desc.K12.Seat.last).blocksInOrder = true ∧
      VerifiableInference.Desc.oraclesOf F.shared.blocksInOrder = VerifiableInference.Desc.oraclesOf (chainOf
                 Z.p.chains (p14Of Z.p.chains (beforePointOf N))
                 (VerifiableInference.Desc.K12.Seat.tests N)
                 VerifiableInference.Desc.K12.Seat.last).blocksInOrder := by
  have hs := shared_ok_of_planOk F hp
  obtain ⟨Z, hZ, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, hA, -, rfl⟩ := pureZ_make h
  have hA' : laterShared Z = some A := hA
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    unfold laterShared Desc.K14.sharedSeatAt at hA'
    rw [hN] at hA'
    exact nomatch hA'
  | ok N =>
    have hs' : blocksOk A.chain.blocksInOrder = true :=
      (blocksOk_retype (Cl' := ProofFile.Cl) A.chain (shared_links hA')).symm.trans hs
    have ho : VerifiableInference.Desc.oraclesOf (A.chain.retype : Chain A.σ ProofFile.Cl).blocksInOrder =
      VerifiableInference.Desc.oraclesOf A.chain.blocksInOrder :=
      oracles_retype A.chain (shared_links hA')
    have hA'' := hA'
    unfold laterShared Desc.K14.sharedSeatAt at hA''
    rw [hN] at hA''
    have e := Option.some.inj hA''
    have hc : VerifiableInference.Desc.oraclesOf A.chain.blocksInOrder =
        VerifiableInference.Desc.oraclesOf (chainOf Z.p.chains
          (p14Of Z.p.chains (beforePointOf N)) (VerifiableInference.Desc.K12.Seat.tests N)
          VerifiableInference.Desc.K12.Seat.last).blocksInOrder := by
      rw [← e]
      rfl
    rw [← e] at hs'
    exact ⟨Z, N, hZ, hN, hs', ho.trans hc⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.eight_ok
#print axioms Desc.K14.Law.told_of_retype
#print axioms Desc.K14.Law.chain_at_descPure
