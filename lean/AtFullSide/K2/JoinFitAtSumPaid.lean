-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/JoinFitAtSumPaid.lean: `joinFit_at_sum` (AtFullSide/K2/JoinFitAtSum.lean) WITH THE
SHARED SENDING's TWO PREMISES PAID: UNDER THE LIBRARY's HEAD AND THE OPENING THE JOINED LIST IS FIT
(`JoinFit`, Johnson/Desc/ProofFile/Honest/Thread/JoinFit.lean, of other authors) AT THE SUM OF THE
CODE SWITCH's SHARE AND A RECORD K, UNDER PREMISES ON K ALONE. Two statements with their proofs:
calls alone; no definition.

  `joinFit_at_sum_ten`    hK1 is paid by `own_k1_head` (…/Honest/Thread/JoinOwnK1.lean, of other
                    authors). LEFT: the nine of K · hcoins
  `joinFit_at_sum_book`   AT THE BOOK THAT `onlineProverFromPublicFiles` RETURNS: hcoins too is paid, by `coins_at_head`
                    (…/Honest/Thread/JoinAtHead.lean, theirs). LEFT: THE NINE OF K: hn · hn' · hp ·
                    hp' · ht · hfarMK · hfarPK · m3 · p3

Limits. THE NINE ARE PREMISES: SHOWN HERE OF NO RECORD. That `onlineProverFromPublicFiles` returns is a premise of the
second. All limits of `joinFit_at_sum` stand: "fit" is a sentence on numbers, seats, places and
counts and on lots that agree: that a lot's text answers is not in it. The head and the opening are
premises. The full size; the format's second hash function. Nothing on any property.
-/
import AtFullSide.K2.JoinFitAtSum
import Johnson.Desc.ProofFile.Honest.Thread.JoinOwnK1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (momL)
open ProofFile.Honest.FirstThread (TreeLot Others JoinFit byNo k1Jobs own_k1_head coins_at_head)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {W₀ Rc Xi Tr Xj X : Type} {Bk : ProverCoinCounts}

/-- THE TEN ARE PREMISES. **THE SHARED SENDING's LIMB OF "owned" IS PAID.** -/
theorem joinFit_at_sum_ten (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj) (front : Nat)
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj) (own₀ : X)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) {K : Others Bk (Local W₀ Rc Xi Tr)}
    -- OF K: ITS PUBLIC FACE LIES IN THE PLAN's THIRD CLASS
    (hn : ∀ n ∈ ProofFile.Honest.FirstThread.nums K.ml, n ∈ lastNumsW)
    (hn' : (ProofFile.Honest.FirstThread.nums K.ml).Nodup)
    (hp : ∀ s ∈ ProofFile.Honest.FirstThread.seatsOf K.pl, s ∈ lastPadsW)
    (hp' : (ProofFile.Honest.FirstThread.seatsOf K.pl).Nodup) (ht : K.tn = [354])
    -- OF K: ITS LOTS STAND FAR FROM THE SHARED SENDING's
    (hfarMK : ∀ L' ∈ K.ml, ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    (hfarPK : ∀ L' ∈ K.pl, ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    -- OF K: ITS LIMBS OF "owned"
    (m3 : MsgsOwnedAt K.ml (P5J.At.arr Zp) lastSeatsW) (p3 : PadsOwnedAt K.pl lastSeatsW)
    -- THE BOOK's COUNTS
    (hcoins : ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀),
      dueAt (Bk.rowsOf 0) ⟨x.2.P.place, 0⟩ = K1.dueR x.2.P x.2.ride) :
    JoinFit cF.blocksInOrder front (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀))
      ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K) :=
  joinFit_at_sum h O no Dt Dd front wit own₀ D readers rest hn hn' hp hp' ht hfarMK hfarPK m3 p3
    (fun _ hq hs => own_k1_head h O no Dt Dd front wit own₀ _ hq hs) hcoins

/-- THE NINE ARE PREMISES, ALL ON K. **AT THE BOOK THAT `onlineProverFromPublicFiles` RETURNS.** -/
theorem joinFit_at_sum_book (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {X₀ Xa : Type} {P : OnlineProverParts W₀ Rc Tr X₀ Xa} {A : OnlineProverWithDescription W₀ Rc Tr X₀ Xa}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj) (front : Nat)
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj) (own₀ : X)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : Nat → TreeLot A.B (Local W₀ Rc Xi Tr)) {K : Others A.B (Local W₀ Rc Xi Tr)}
    -- OF K: ITS PUBLIC FACE LIES IN THE PLAN's THIRD CLASS
    (hn : ∀ n ∈ ProofFile.Honest.FirstThread.nums K.ml, n ∈ lastNumsW)
    (hn' : (ProofFile.Honest.FirstThread.nums K.ml).Nodup)
    (hp : ∀ s ∈ ProofFile.Honest.FirstThread.seatsOf K.pl, s ∈ lastPadsW)
    (hp' : (ProofFile.Honest.FirstThread.seatsOf K.pl).Nodup) (ht : K.tn = [354])
    -- OF K: ITS LOTS STAND FAR FROM THE SHARED SENDING's
    (hfarMK : ∀ L' ∈ K.ml, ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    (hfarPK : ∀ L' ∈ K.pl, ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81)
    -- OF K: ITS LIMBS OF "owned"
    (m3 : MsgsOwnedAt K.ml (P5J.At.arr Zp) lastSeatsW) (p3 : PadsOwnedAt K.pl lastSeatsW) :
    JoinFit cF.blocksInOrder front (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀))
      ((switchShareAt A.B cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K) :=
  joinFit_at_sum_ten h O no Dt Dd front wit own₀ D readers rest hn hn' hp hp' ht hfarMK hfarPK m3
    p3 (coins_at_head h O no Dt Dd hA)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.joinFit_at_sum_ten
#print axioms ProofFile.Honest.K2.Law.joinFit_at_sum_book
