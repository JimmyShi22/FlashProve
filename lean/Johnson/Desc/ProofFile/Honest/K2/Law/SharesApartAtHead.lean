-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SharesApartAtHead.lean: NUMBERS OF A PUBLIC PLAN: UNDER THE
LIBRARY's HEAD AND THE OPENING THE KIND's SHARE OF THE JOINED LIST (`switchShareAt`,
Honest/K2/JoinShare.lean) STANDS APART FROM EVERY RECORD WHOSE PUBLIC FACE LIES IN THE PLAN's THIRD
CLASS (the seats of the sendings 76 to 80; the member number 354): SO AT THE SUM OF THE TWO
(`Others.add`, Honest/Thread/JoinFit.lean, of other authors) THE LOTS AGREE AND NO MEMBER's NUMBER
STANDS TWICE. Definitions with code; closed facts by Lean's kernel, three of them controls;
statements with their proofs.

  `lastNumsW`, `lastPadsW`   the numbers and the seats of the written seats of the third class
  `widerSeatsW`     for the controls: the written seats of the sendings 75 to 80
  `sharesApartW`    BY LEAN's KERNEL: the switches' 96 numbers and these ten are all apart · the
                    switches' 132 seats and these ten · the switches' 25 members' numbers and 354.
                    CONTROLS, WHICH HANG ON THE WRITTEN DATA: with the third class made wider by the
                    sending in front of it (75; `widerSeatsW`) the first two tests say no; with 353
                    in 354's stead the third does
  `share_nums_face`, `share_pads_face`, `share_tn_face`   the share's public face under the head:
                    the written lists
  `sum_of_shares`   K a record with (i) each number of its lots of messages in `lastNumsW`, no two
                    one · (ii) each seat of its lots of pads in `lastPadsW`, no two one · (iii) tn =
                    [354] ⊢ at the sum: `MsgsAgree` · `PadsAgree` · no number twice in tn · both
                    shares stand in it (`ShareIn`) · 354 stands in its tn

WHO IS TO CALL IT. Its first three ends are the premises hml, hpl and htn of `joinFit_head`
(Honest/Thread/JoinAtHead.lean, of other authors; not imported) at the one record for all senders
but the shared sending. No file calls it yet.

Limits. NUMBERS AND SEATS ALONE: no text of a lot is applied. (i), (ii), (iii) ARE PREMISES: SHOWN
HERE OF NO RECORD. "Agree" is had the strong way: no number and no seat has two lots. The head and
the opening are premises. The full size; the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnedSplitAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.TreesSplitAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.FirstThread (TreeLot Others MsgsAgree PadsAgree msgsAgree_of_nodup
  padsAgree_of_nodup)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- The numbers of the written seats of the sendings 76 to 80. -/
def lastNumsW : List Nat := lastSeatsW.map fun q => arrW q.j q.t

/-- These seats. -/
def lastPadsW : List (Nat × Nat) := lastSeatsW.map fun q => (q.j, q.t)

/-- For the controls: the third class made wider by one sending, the one in front of it. -/
def widerSeatsW : List P5T.PSeat :=
  P5T.psFull.filter fun q => decide (75 ≤ q.send) && decide (q.send ≤ 80)

set_option maxRecDepth 1000000 in
/-- **At the written lists: all apart**; three controls that say no. -/
theorem sharesApartW :
    (k2NumsW ++ lastNumsW).Nodup ∧ (k2PadsW ++ lastPadsW).Nodup ∧
      (switchBorders placesW ++ [354]).Nodup ∧
      ¬ (k2NumsW ++ widerSeatsW.map fun q => arrW q.j q.t).Nodup ∧
      ¬ (k2PadsW ++ widerSeatsW.map fun q => (q.j, q.t)).Nodup ∧
      ¬ (switchBorders placesW ++ [353]).Nodup ∧ k2NumsW.length = 96 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

section
variable (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (seatZ Zp Np) (secondAt Zp Np))
  (front : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
  (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr))
include h O

/-- The numbers of the share's lots of messages are the written ones. -/
theorem share_nums_face (bs : List (Block S ProofFile.Cl)) :
    ProofFile.Honest.FirstThread.nums (switchShareAt Bk bs front Zp Bs.G₀ D readers rest).ml =
      k2NumsW := by
  unfold switchShareAt k2NumsW
  rw [nums_share, places_at_head h.toAtMg O, switchNum_at_head h.toAtMg]

/-- The seats of the share's lots of pads are the written ones. -/
theorem share_pads_face (bs : List (Block S ProofFile.Cl)) :
    ProofFile.Honest.FirstThread.seatsOf (switchShareAt Bk bs front Zp Bs.G₀ D readers rest).pl =
      k2PadsW := by
  unfold switchShareAt k2PadsW
  rw [seats_share, places_at_head h.toAtMg O, pseatsAll_at_head h.toAtMg]
  rfl

/-- The share's members' numbers are the written ones. -/
theorem share_tn_face :
    (switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).tn = switchBorders placesW :=
  borders_at_head h O

/-- (i), (ii), (iii) ARE PREMISES. **AT THE SUM OF THE KIND's SHARE AND A RECORD OF THE THIRD CLASS:
THE LOTS AGREE, NO MEMBER's NUMBER STANDS TWICE, BOTH SHARES STAND IN IT.** -/
theorem sum_of_shares {K : Others Bk (Local W₀ Rc Xi Tr)}
    (hn : ∀ n ∈ ProofFile.Honest.FirstThread.nums K.ml, n ∈ lastNumsW)
    (hn' : (ProofFile.Honest.FirstThread.nums K.ml).Nodup)
    (hp : ∀ s ∈ ProofFile.Honest.FirstThread.seatsOf K.pl, s ∈ lastPadsW)
    (hp' : (ProofFile.Honest.FirstThread.seatsOf K.pl).Nodup) (ht : K.tn = [354]) :
    MsgsAgree ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K).ml ∧
      PadsAgree ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K).pl ∧
      ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K).tn.Nodup ∧
      ShareIn (switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest)
        ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K) ∧
      ShareIn K ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K) ∧
      354 ∈ ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K).tn := by
  have et := share_tn_face h O front D readers rest (Bk := Bk)
  have dt : ∀ b ∈ K.tn, b ∉ (switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).tn := by
    intro b hb hb'
    rw [ht] at hb
    rw [et] at hb'
    exact List.disjoint_of_nodup_append sharesApartW.2.2.1 hb' hb
  refine ⟨msgsAgree_of_nodup ?_, padsAgree_of_nodup ?_, ?_, shareIn_add_left _ _,
    shareIn_add_right _ _ dt, ?_⟩
  · show (ProofFile.Honest.FirstThread.nums
      ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).ml ++ K.ml)).Nodup
    unfold ProofFile.Honest.FirstThread.nums
    rw [List.map_append]
    refine List.Nodup.append ?_ hn' fun a ha hb => ?_
    · have e := share_nums_face h O front D readers rest cF.blocksInOrder (Bk := Bk)
      unfold ProofFile.Honest.FirstThread.nums at e
      rw [e]
      exact sharesApartW.1.of_append_left
    · have e := share_nums_face h O front D readers rest cF.blocksInOrder (Bk := Bk)
      unfold ProofFile.Honest.FirstThread.nums at e
      rw [e] at ha
      exact List.disjoint_of_nodup_append sharesApartW.1 ha (hn a hb)
  · show (ProofFile.Honest.FirstThread.seatsOf
      ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).pl ++ K.pl)).Nodup
    unfold ProofFile.Honest.FirstThread.seatsOf
    rw [List.map_append]
    refine List.Nodup.append ?_ hp' fun a ha hb => ?_
    · have e := share_pads_face h O front D readers rest cF.blocksInOrder (Bk := Bk)
      unfold ProofFile.Honest.FirstThread.seatsOf at e
      rw [e]
      exact sharesApartW.2.1.of_append_left
    · have e := share_pads_face h O front D readers rest cF.blocksInOrder (Bk := Bk)
      unfold ProofFile.Honest.FirstThread.seatsOf at e
      rw [e] at ha
      exact List.disjoint_of_nodup_append sharesApartW.2.1 ha (hp a hb)
  · show ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).tn ++ K.tn).Nodup
    rw [et, ht]
    exact sharesApartW.2.2.1
  · show 354 ∈ (switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).tn ++ K.tn
    rw [ht]
    exact List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))

end

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lastNumsW
#print axioms ProofFile.Honest.K2.Law.lastPadsW
#print axioms ProofFile.Honest.K2.Law.widerSeatsW
#print axioms ProofFile.Honest.K2.Law.sharesApartW
#print axioms ProofFile.Honest.K2.Law.share_nums_face
#print axioms ProofFile.Honest.K2.Law.share_pads_face
#print axioms ProofFile.Honest.K2.Law.share_tn_face
#print axioms ProofFile.Honest.K2.Law.sum_of_shares
