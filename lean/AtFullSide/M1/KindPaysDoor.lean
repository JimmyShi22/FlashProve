-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what the kind K1 pays with the book test paid.
/-
AtFullSide/M1/KindPaysDoor.lean: the public test on the book at a return of the maker with no further
premise (`book_at_return`, which is `door_closed`, AtFullSide/M1/LotsThinClosed.lean), and
`K1PaysAtFiles` with its hypothesis `book` paid. Left inside: `hG`, `hk`, `rows`. That test is a test on
the book's entries: it says nothing of what a run shows. No property of the protocol is claimed here.
-/
import AtFullSide.M1.KindPaysNamed
import AtFullSide.M1.LotsThinClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput tableCoins onlineMaker OnlineReturn termRows)
open Johnson.M1 (k1Lot wLot)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes (TableKey)
open P2Law.ProofPlan (WP)
open VerifiableInference.Desc.K1 (qFull firstPar parW)
open VerifiableInference.Desc.K13.Law (gpFull wMsgFull)
open OnBytes.SendSim.At OnBytes.SendSim.Seat

/-- **The public test on the book at a return of the maker, at any filling.** -/
theorem book_at_return {W₀ Rc Tr X₀ X' : Type} {P : VerifierAndGoals.PublicFiles} {Fl : OnlineProverParts W₀ Rc Tr X₀ X'}
    {R : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R) :
    ∀ e ∈ R.B.ahead, e.once = true → lotsMine R.Z R.G e.owner = true →
      lotsOkB R.Z R.G R.B (orderOf R.F) e.owner = true :=
  door_closed hS hL h

/-- **What the kind K1 pays at three public files, the book paid.** Left: `hG`, `hk`, `rows`. -/
def K1PaysBookPaid (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (returned : OnlineReturn files),
    onlineMaker files = .ok returned ∧ returned.Z = Zp ∧ H2U.placesOfMade returned.Z.made = .ok Np ∧
    ∀ (G : Sides returned.F returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Cells Unit Unit)
      (T₁ : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells → Thread returned.B returned.F.S₁ returned.F.Cl
        (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit
        ProofFile.Inst)
      (S₁ : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells → Nat → Coins returned.B →
        Mid (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit → Prop)
      (r₁ : List (Unlettered (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells)
        (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit ProofFile.Inst)),
      (G.first = r₁.map fun r => r.lay T₁ S₁ returned.F.first.blocksInOrder) →
      (∀ r ∈ r₁, r.place.kind = KindName.K1 →
        r ∈ (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id
            (tableCoins files)).rows returned.Z returned.G ∨
          r ∈ (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id
            (tableCoins files)).rows returned.Z returned.G) →
      (∀ L ∈ G.shared, L.place.kind = KindName.K1 → ∃ r ∈ termRows files Zp Np,
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) →
      VerifiableInference.Compilation.KindPays G KindName.K1

/-- **Where the gate accepts.** -/
theorem kindPays_K1_bookMet (files : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (hS : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) : K1PaysBookPaid files := by
  obtain ⟨Zp, Np, returned, hA, eZ, eP, H⟩ := kindPays_K1_live files hS read hL
  exact ⟨Zp, Np, returned, hA, eZ, eP, fun G T₁ S₁ r₁ hG hk rows =>
    H G T₁ S₁ r₁ hG hk (book_at_return hS hL hA) rows⟩

/-- **At the named files.** -/
theorem kindPays_K1_bookMet_named (Z : VerifierAndGoals.PublicFiles) (hN : VerifierAndGoals.NamedFiles Z) : K1PaysBookPaid Z := by
  rcases hN with rfl | rfl
  · obtain ⟨sc, ⟨pp, hr⟩, hl⟩ := AtFullSide.Tie.premises_zFull
    exact kindPays_K1_bookMet _ sc hr hl
  · obtain ⟨sc, ⟨pp, hr⟩, hl⟩ := AtFullSide.Tie.premises_zGap
    exact kindPays_K1_bookMet _ sc hr hl

end AtFullSide.M1

#print axioms AtFullSide.M1.book_at_return
#print axioms AtFullSide.M1.kindPays_K1_bookMet
#print axioms AtFullSide.M1.kindPays_K1_bookMet_named
