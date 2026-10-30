-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/OpeningRowsAtTheBook.lean: the kind "the code switch" (K2): AT EACH OF THE PLAN's 25
SWITCHES, AT THE BOOK THAT `bookWhole` RETURNS: the rows that the switch lays anew of the first
segment's first sending, the fold's fresh mask among them, are the opening's sender's own rows. A
JOIN OF TWO HOUSES' LAWS: `copyShared_first_by_test`, `copyShared_mask_by_test`
(Johnson/Desc/ProofFile/Honest/K2/Law/CopySharedByTest.lean) with their premise ht, one public test
on the book's entry, PAID by `carried_opening_at_zero` (AtFullSide/K2/CarriedAtTheBook.lean, of
another author). One statement with its proof: four calls; no definition.

  `opening_rows_at_25`  the count, that the places differ, the first sending's size, and the law
                        at each place: ONE CONJUNCTION

TWO RANGES ARE PINNED IN THE SAME STATEMENT: the list of places has 25 members, at different places
(`carried_at_25`, AtFullSide/K2/CarriedCounted.lean) · the first sending has four messages
(`first_size_at_head`, AtFullSide/K2/FirstSizeAtHead.lean, of a third author): three in front of the
mask, and the mask. SO NEITHER "at each place" NOR "at each message" RUNS OVER NOTHING. WHAT THESE
TWO DO NOT GUARD: the clause for a place begins with three arrows: the hand, the rows laid anew, the
sender's cut (below): at coins where any of the three is lacking, that clause is empty. NOR THIS: Sg
comes in through hS, a premise: the theorem does not itself say that `segmentsOf` has an entry
number 0 (`segments_at_head`, Johnson/Desc/ProofFile/Honest/K2/Law/PlacesWritten.lean, with the
second half of `openingCarriedW`, CarriedAtTheBook.lean, would give one: not called for that). The
letters laid in: the book Bk := B · the first entry's number b₀ := 0 · the sender's address o :=
`openingAddr` · the sender's plan and ride: those of the two laws' hP and hρ, by rfl.

Limits. UNDER THE LIBRARY's HYPOTHESIS ON THE PUBLIC FILES (h), THE OPENING (O), AND hB: that
`bookWhole` returns B: not that B is the frame's own book. WHAT STAYS A PREMISE AT EACH PLACE: that
the switch is handed its stretches · that the first segment's rows are laid anew AT BASE 0: where
they are not laid nothing is said; that the lot's closing lays them at base 0 is not said here · the
opening's sender's own cut of the run's coins at its address · what the sender's filling holds at
the message: one equation each. NO COINS ARE EXHIBITED AT WHICH ALL THREE HOLD. THE FIRST SENDING's
MESSAGES ALONE: not the later sendings of the first segment, nor any other segment
(`copyShared_later_by_test` is not served). The limits of the files called stand:
CarriedAtTheBook.lean names six closed facts by evaluation in Lean's kernel, five of them controls,
with two options raised; and says of the merges, `mergesByName`'s, that the frame's own text calls
them a guess. OURS, NOT THEIRS: we know of no replay of these facts by an independent checker. ROWS
AGAINST ROWS: WHICH ROWS ARE LAID ANEW: no sentence on what a coin is for. NO LOT IS LAID. Nothing
on any property.
-/
import AtFullSide.K2.CarriedCounted
import AtFullSide.K2.FirstSizeAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.CopySharedByTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left zeroG)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- **AT EACH OF THE 25 SWITCHES, AT THE BOOK THAT `bookWhole` RETURNS.** Sg: the first segment. R:
the rows that the switch lays anew of it, at base 0. cs: the opening's sender's own cut of the run's
coins. The first clause: a message in front of the fold's mask. The second: the fresh mask. -/
theorem opening_rows_at_25 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) :
    (switchPlaces Zp Bs.G₀).length = 25 ∧ ((switchPlaces Zp Bs.G₀).map (·.place)).Nodup ∧
      (Sg.sent.headD #[]).size = 4 ∧
      ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ (ch : Nat) (k : Coins B)
        (c : SwitchCoins p.sizes p.others p.foldVars p.carries), handed ch p k = some c →
        ∀ (prev : Option Left) (prevKept : List OnBytes.OracleShape)
          (own : Nat → Nat → Nat → Cb.Gl.E) (R : GroupRows),
          segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) 0 true =
            .ok R →
          ∀ cs : Cs (K1.dueR (firstPar Bs.G₀.first (gpOf Zp))
              (K1.rideOf (K1.firstFold Bs.G₀.first))),
            K1.lentCut k ch AtFullSide.K2.openingAddr
              (K1.dueR (firstPar Bs.G₀.first (gpOf Zp))
                (K1.rideOf (K1.firstFold Bs.G₀.first))) = some cs →
            ∀ dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E),
              (∀ n, n < (Sg.sent.headD #[]).size - 1 →
                dataK n = asShared (shapeAt (firstPar Bs.G₀.first (gpOf Zp)) n)
                  (dataAtOf Sg prev own n) →
                R.rows[n]? = some (K1.rowsR (firstPar Bs.G₀.first (gpOf Zp))
                  (K1.rideOf (K1.firstFold Bs.G₀.first)) dataK cs n)) ∧
              (dataK ((Sg.sent.headD #[]).size - 1) =
                  asShared (shapeAt (firstPar Bs.G₀.first (gpOf Zp))
                    ((Sg.sent.headD #[]).size - 1)) (fun _ _ => zeroG) →
                R.fresh = some (K1.rowsR (firstPar Bs.G₀.first (gpOf Zp))
                  (K1.rideOf (K1.firstFold Bs.G₀.first)) dataK cs
                  ((Sg.sent.headD #[]).size - 1))) := by
  obtain ⟨h25, hnd⟩ := AtFullSide.K2.carried_at_25 h O
  have h4 : (Sg.sent.headD #[]).size = 4 := first_size_at_head h O hS
  refine ⟨h25, hnd, h4, fun p hp ch k c hc prev prevKept own R hR cs ho dataK =>
    ⟨fun n hn hdat => ?_, fun hdat => ?_⟩⟩
  · exact copyShared_first_by_test h O ch p k c hc hS hR hn rfl rfl AtFullSide.K2.openingAddr ho
      (AtFullSide.K2.carried_opening_at_zero h O hB hS hp (by omega)) dataK hdat
  · exact copyShared_mask_by_test h O ch p k c hc hS hR rfl rfl AtFullSide.K2.openingAddr ho
      (AtFullSide.K2.carried_opening_at_zero h O hB hS hp (by omega)) dataK hdat

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.opening_rows_at_25
