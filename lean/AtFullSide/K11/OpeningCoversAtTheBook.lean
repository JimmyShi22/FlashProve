-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K11/OpeningCoversAtTheBook.lean: AT WHATEVER BOOK bookWhole RETURNS AT F0T, UNDER THE
LIBRARY's HEAD AND THE OPENING, ON CHAIN 0: THE ROW AT THE OPENING's SENDER's ADDRESS HAS JUST WHAT
ITS SENDING TAKES: SO THE PUBLIC TEST `K1.bookCovers` SAYS YES THERE, AND THE SENDER's CUT OF A
RUN's COINS (`K1.lentCut`, Honest/K1/ScriptAt.lean, another group of authors') RETURNS AT EVERY
RUN's COINS. No definition. Lemmas; none of the library's goals. A LIGHT FILE: it stands over
written rows and two laws on the head alone, so that whoever needs the cut need not build what lies
beneath the kind K11's lots. It lies in the side library because it imports files of it.

  `openingCoversW`, `openingDueW`, `openingCoversW_can_fail`, `openingCoversW_can_fail_f`
      BY LEAN's KERNEL, at the written book's first chain's rows (`rawRowsFirstW`,
      AtFullSide/K14/RawBookRowsWritten.lean) and the written opening: the row covers the due ·
      both are ⟨25848, 8958⟩ · two controls: one coin more, of either field, is not covered
  `first_at_book`
      what bookWhole returns at F0T has the written rows on its first chain
  `opening_covers_at_book`
      `K1.bookCovers` B 0 at the opening's own letters
  `opening_place_at_head`
      the opening's sender's place, at the plan's own letters, is ⟨1, some 0, 1, K1⟩
  `opening_cut_at_book`
      SO THE CUT RETURNS: at every k there is a cs with `K1.lentCut k 0` ⟨⟨1, some 0, 1, K1⟩, 0⟩
      (the due) = some cs: by `K1.lentCut_isSome`
  `opening_cut_at_job`
      the same at a job J whose numbers and rides are the opening's: at ⟨J.P.place, 0⟩ and J's
      own due

WHAT IT IS NOT. COVERS, NOT LENDS: whether the frame lends the sender's part is another question.
WHETHER, NOT WHAT: nothing on the coins that are cut. That a thread's book is what bookWhole returns
at F0T is not said. Chain 0 alone.

Limits. FOUR CLOSED FACTS BY EVALUATION IN LEAN's KERNEL, two of them controls. The full size; the
format's second hash function. All limits of RawBookRowsWritten.lean stand. Nothing on any property.
-/
import AtFullSide.K14.RawAtTheBookAtHead
import AtFullSide.K14.RawBookRowsWritten
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexKeyWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF qFull firstPar gpOf)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open AtFullSide.K14 (rawRowsFirstW rawBookRows_written rawBook_same bookWhole_returns_raw
  bookRaw_returns_written)

set_option maxRecDepth 1000000 in
/-- **At the written rows and the written opening: the sender's row covers what its sending
takes.** -/
theorem openingCoversW :
    decide ((K1.dueR parGF (K1.rideOf (K1.firstFold qFull))).f ≤
        (dueAt rawRowsFirstW ⟨parGF.place, 0⟩).f ∧
      (K1.dueR parGF (K1.rideOf (K1.firstFold qFull))).e ≤
        (dueAt rawRowsFirstW ⟨parGF.place, 0⟩).e) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The numbers**: the sending takes, and the row has, 25848 coins of the base field and 8958 of
the extension field: so a row does stand at the address, and neither count is 0. -/
theorem openingDueW :
    K1.dueR parGF (K1.rideOf (K1.firstFold qFull)) = ⟨25848, 8958⟩ ∧
      dueAt rawRowsFirstW ⟨parGF.place, 0⟩ = ⟨25848, 8958⟩ := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: one coin of the extension field more is not covered. -/
theorem openingCoversW_can_fail :
    decide ((K1.dueR parGF (K1.rideOf (K1.firstFold qFull))).f ≤
        (dueAt rawRowsFirstW ⟨parGF.place, 0⟩).f ∧
      (K1.dueR parGF (K1.rideOf (K1.firstFold qFull))).e + 1 ≤
        (dueAt rawRowsFirstW ⟨parGF.place, 0⟩).e) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: one coin of the base field more is not covered. -/
theorem openingCoversW_can_fail_f :
    decide ((K1.dueR parGF (K1.rideOf (K1.firstFold qFull))).f + 1 ≤
        (dueAt rawRowsFirstW ⟨parGF.place, 0⟩).f ∧
      (K1.dueR parGF (K1.rideOf (K1.firstFold qFull))).e ≤
        (dueAt rawRowsFirstW ⟨parGF.place, 0⟩).e) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- **What bookWhole returns at F0T has the written rows on its first chain.** -/
theorem first_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    B.first = rawRowsFirstW := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  rw [rawBook_same h.scope h.laid (bookWhole_returns_raw W hW) hB]
  exact (rawBookRows_written _ W hW).1

/-- **At that book the opening's sender's row covers what its sending takes.** -/
theorem opening_covers_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    K1.bookCovers B 0 ⟨(firstPar Bs.G₀.first (gpOf Zp)).place, 0⟩
      (K1.dueR (firstPar Bs.G₀.first (gpOf Zp)) (K1.rideOf (K1.firstFold Bs.G₀.first))) =
        true := by
  rw [ProofFile.Honest.K11.par_at_head h O, ProofFile.Honest.K11.fold_at_head h O]
  have er : B.rowsOf 0 = rawRowsFirstW := first_at_book h hB
  unfold K1.bookCovers
  rw [er]
  exact openingCoversW

/-- **Under the head and the opening the opening's sender stands at the written place.** -/
theorem opening_place_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (firstPar Bs.G₀.first (gpOf Zp)).place = ⟨1, some 0, 1, .K1⟩ := by
  rw [ProofFile.Honest.K11.par_at_head h O]
  rfl

/-- THE HEAD, THE OPENING AND THE BOOK ARE PREMISES. **AT THAT BOOK THE OPENING's SENDER's CUT
RETURNS, AT EVERY RUN's COINS.** -/
theorem opening_cut_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (k : Coins B) :
    ∃ cs, K1.lentCut k 0 ⟨⟨1, some 0, 1, .K1⟩, 0⟩
      (K1.dueR (firstPar Bs.G₀.first (gpOf Zp)) (K1.rideOf (K1.firstFold Bs.G₀.first))) =
        some cs := by
  have hc := opening_covers_at_book h O hB
  rw [opening_place_at_head h O] at hc
  apply Option.isSome_iff_exists.1
  rw [K1.lentCut_isSome k 0 (by omega)]
  exact hc

/-- **The same at a job with the opening's numbers and rides**: at the job's own place and due. -/
theorem opening_cut_at_job {W Y : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (J : K1.SendJob W Y) (hJP : firstPar Bs.G₀.first (gpOf Zp) = J.P)
    (hJr : K1.rideOf (K1.firstFold Bs.G₀.first) = J.ride) (k : Coins B) :
    ∃ cs, K1.lentCut k 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some cs := by
  apply Option.isSome_iff_exists.1
  rw [K1.lentCut_isSome k 0 (by omega), ← hJP, ← hJr]
  exact opening_covers_at_book h O hB

end AtFullSide.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K11.openingCoversW
#print axioms AtFullSide.K11.openingDueW
#print axioms AtFullSide.K11.openingCoversW_can_fail
#print axioms AtFullSide.K11.openingCoversW_can_fail_f
#print axioms AtFullSide.K11.first_at_book
#print axioms AtFullSide.K11.opening_covers_at_book
#print axioms AtFullSide.K11.opening_place_at_head
#print axioms AtFullSide.K11.opening_cut_at_book
#print axioms AtFullSide.K11.opening_cut_at_job
