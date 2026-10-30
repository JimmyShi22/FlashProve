-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstFar.lean: THE FOLD FACTS AT A PROOF FILE's SEAT. At the seat's one
numbering over all three chains (Sh.openAt₀, Johnson/Desc/K14/Law/SharedConstOpenAt.lean) the fourth
fold fact of Johnson/Desc/K14/Law/SharedConstFold.lean, FarFrom, comes down to five closed tests on
the verifier's public value and ONE fact on the first chain's state that another file's list of
fold facts bears already: the book's places are the first of the written list's (atFirstSeats).

  Sh.testsFar Z N … L  the five closed tests, each with its name: the shared chain's three tenants
                       are found among the later chains' seats · every place of the written list L
                       is found among the first chain's · the first chain sends at most 1000 times
  Sh.farFrom_of_carried    at one state: the five tests and atFirstSeats L s give FarFrom
  Sh.foldFacts_at      **FoldFacts at the seat** from four facts on a reached last state of the
                       first chain at a typed instance (the constant's own R, both halves):
                           BookInOrder · EveryPlaced · CodesAre · atFirstSeats L
HOW. One call of P5T.far_of_found and mem_places_of_carried
(Johnson/Desc/Sound/FarOfFound.lean).
WHAT IS NOT HERE. No law. The four facts: each an induction along the first chain. That the five
tests accept.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstOpenAt
import Johnson.Desc.K14.Law.SharedConstFold
import Johnson.Desc.Sound.FarOfFound

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open Johnson.Desc.First.Walk.Tied (EndAt₁)
open VerifiableInference.Desc.K12.Door (atFirstSeats)
open P5T (foundFirstB foundLaterB)

namespace Sh

variable {Cells Tok : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
  (B' : ProofFile.SecondSeat) (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
  (c₀ : Cells) (matC : Cells → Nat → Nat → GE)
  (held : ((ixOf2 (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold 0 2852142980
    (rankLib (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold)).Row ×
    Fin (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold.index.code.ell → GE) → Option Cells)
  (O₁ : Open₁ Cells Tok (planAt Z N (seatF o Z N B' cF)).Q)
  (L : VerifiableInference.Desc.K12.Door.Laid)

/-- **The five closed tests.** -/
def testsFar : List (String × Bool) :=
  [("hten.oU: o_u's tenant is found among the later chains' seats",
      foundLaterB Z Z.D (tenantSh (t₁ (planAt Z N (seatF o Z N B' cF)))
        (layU (planAt Z N (seatF o Z N B' cF))) (layO (planAt Z N (seatF o Z N B' cF))) .oU)),
   ("hten.oOmega: o_omega's tenant is found among the later chains' seats",
      foundLaterB Z Z.D (tenantSh (t₁ (planAt Z N (seatF o Z N B' cF)))
        (layU (planAt Z N (seatF o Z N B' cF))) (layO (planAt Z N (seatF o Z N B' cF))) .oOmega)),
   ("hten.oSp: o_sp's tenant is found among the later chains' seats",
      foundLaterB Z Z.D (tenantSh (t₁ (planAt Z N (seatF o Z N B' cF)))
        (layU (planAt Z N (seatF o Z N B' cF))) (layO (planAt Z N (seatF o Z N B' cF))) .oSp)),
   ("hpl: every place of the written list is found among the first chain's seats",
      L.places.all (foundFirstB Z Z.D)),
   ("hlen: the first chain sends at most 1000 times",
      decide (Z.made.proof.1.sends.length ≤ 1000))]

/-- All of them accept. -/
def TestsFar : Prop := (testsFar o Z N B' cF L).all (·.2) = true

theorem testsFar_length : (testsFar o Z N B' cF L).length = 5 := rfl

/-- **At one state.** -/
theorem farFrom_of_carried (h : TestsFar o Z N B' cF L) (s : First.S)
    (hc : atFirstSeats L s = true) :
    FarFrom (openAt₀ o Z N B' cF c₀ matC held O₁).arr
      (nums (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)) s := by
  simp only [TestsFar, testsFar, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, hpl, hlen⟩ := h
  intro n j t hp m
  refine P5T.far_of_found Z Z.D
    (nums (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)).tenant
    (fun m' => ?_) L.places hpl hlen j t (mem_places_of_carried L _ hc n j t hp) m
  cases m'
  · exact h1
  · exact h2
  · exact h3

/-- **FoldFacts at the seat.** -/
theorem foldFacts_at (h : TestsFar o Z N B' cF L)
    (hb2 : ∀ p : ProofFile.InstPub × First.S, EndAt₁ (seatF o Z N B' cF) p →
      (∃ z : LPFD.Full.XF × RecFull, p.1 = (LPFD.Full.instanceAsPlainRecord z).pub) → p.2.failed = none →
          BookInOrder p.2)
    (hb3 : ∀ p : ProofFile.InstPub × First.S, EndAt₁ (seatF o Z N B' cF) p →
      (∃ z : LPFD.Full.XF × RecFull, p.1 = (LPFD.Full.instanceAsPlainRecord z).pub) → p.2.failed = none →
          EveryPlaced p.2)
    (hcod : ∀ p : ProofFile.InstPub × First.S, EndAt₁ (seatF o Z N B' cF) p →
      (∃ z : LPFD.Full.XF × RecFull, p.1 = (LPFD.Full.instanceAsPlainRecord z).pub) → p.2.failed = none →
      CodesAre (planAt Z N (seatF o Z N B' cF)).Q.codes p.2)
    (hcar : ∀ p : ProofFile.InstPub × First.S, EndAt₁ (seatF o Z N B' cF) p →
      (∃ z : LPFD.Full.XF × RecFull, p.1 = (LPFD.Full.instanceAsPlainRecord z).pub) → p.2.failed = none →
      atFirstSeats L p.2 = true) :
    FoldFacts (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁) :=
  ⟨fun p hr hm => hb2 p hr.1 hr.2 hm, fun p hr hm => hb3 p hr.1 hr.2 hm,
    fun p hr hm => hcod p hr.1 hr.2 hm, fun p hr hm =>
    farFrom_of_carried o Z N B' cF c₀ matC held O₁ L h p.2 (hcar p hr.1 hr.2 hm)⟩

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.farFrom_of_carried
#print axioms Desc.K14.Law.Sh.foldFacts_at
