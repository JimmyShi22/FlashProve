-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/KeyOwnersLayInOrder.lean: AT THE KEY FILE's BOOK, THE TWO OWNERS' SENDERS LAY THEIR COINS IN THE ORDER OF TAKING.
The two owners of the key file's lookups' mask entries are message 0 of the sending of the multiplicities
(AtPublicFiles.Key.msgJob, at ⟨msgPlace, 0⟩) and the index-mask message (AtPublicFiles.Key.idxJob, at ⟨idxPlace, 0⟩).

  1  ownersW   closed facts at the written sizes, by evaluation in Lean's kernel: each sending has a message 0; it has
     mask rows; how many entries its mask rows have
  2  job_lays_in_order   general in the job, at the key's book: from "the book's sending is made of the job's codes
     and notices" and "the book's count at the address is that sending's"
  3  msgOwner_lays_in_order, idxOwner_lays_in_order   THE TWO ENDS

THE FORM. Each end is SenderLays (keyBook K) 0 owner (tableAt ‹the book's sending› 0)
(fun k w h n => entry k w h (takenNo maskRows n)) (· < takes): the body, to the letter, of the lookups' proposition
SenderLaysItsCoinsInTheOrderOfTaking K owner maskRows (tableAt … 0) takes entry (E2E/Lookup/Key/LedgerIsTheKeyBook.lean),
which this file does not import. entry := the mask table's word, at a number of the table, of the rows that the
job's part lays of its own coins (maskWordE, AtFullSide/K1/MaskInOrderOfTaking.lean); own: the part's own coins, of
a run's: the book's cut at the owner's address.

Limits. hK and OneFull one are hypotheses, as in E2E/KeyBookHeldK1Jobs.lean. At the multiplicities' sending the ride is a
letter that passes the book's test and is none at message 0: rideMsg is such a one. It speaks of the rows that the
SENDER lays: that the entry which a spender reads is that entry is a further tie. That the job's own place is the
address's place is not said (N is free). This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.MaskInOrderOfTaking
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import E2E.KeyBookHeldK1Jobs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open VerifiableInference.Desc.Key (Pieces)
open Johnson.Prover.Send (shapeAt)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull of_atFull tableAt sendingOf ridesOf ridesOk rides_of_ok
  takes_held full_k1 kRanges idxPlace msgPlace OneFull rideMsg rides_full sendingPar_sent)
open AtPublicFiles.Key (idxJob msgJob)
open Lk6.AtPlan (keyFull)

/-! ## 1 General in the job -/

/-- **AT A BOOK THAT HAS THE JOB's SENDING AT THE ADDRESS: THE JOB's PART LAYS THE MASK COINS OF MESSAGE j IN THE ORDER OF
TAKING, FROM THE BOOK's OWN START OF THAT MESSAGE's MASK TABLE.** -/
theorem job_lays_in_order {Bk : ProverCoinCounts} {W X : Type} (o : Addr) (J : SendJob W X) (own₀ : X) (kf : Nat)
    (l : AtPublicFiles.KeyBook.Sending) (hl : sendingOf J.P.codes kf J.P.sent.toList = some l)
    (hr : ∀ i, i < J.P.sent.size → (J.ride i).map (·.count) = (ridesOf J.P kf i).map (·.count))
    (hrow : dueAt (Bk.rowsOf 0) o = l.due) (j : Nat) (hj : j < J.P.sent.size)
    (hn : J.ride j = none) (takes : Nat)
    (ht : takes ≤ (shapeAt J.P j).maskRows *
      (J.P.codes.mask.getD (shapeAt J.P j).maskCode default).ell) :
    ∃ own : Coins Bk → Cs (dueR J.P J.ride), OwnIs Bk 0 o (dueR J.P J.ride) own ∧
      SenderLays (W := W) Bk 0 o (tableAt l j)
        (fun c w h n => maskWordE J.P J.ride
          (J.data w { heard := h, own := own₀, seen := .bare [] }) j (own c)
          (takenNo (shapeAt J.P j).maskRows n)) (· < takes) := by
  have hd : l.due = dueR J.P J.ride := (takes_held (V := Unit) J kf l hl hr).symm
  obtain ⟨own, ho⟩ := ownIs_of_due (Bk := Bk) (ch := 0) (o := o) (d := dueR J.P J.ride)
    fun k => by rw [look_due k 0 (Nat.zero_le 1) o, hrow, hd]
  refine ⟨own, ho, ?_⟩
  rw [table_held J.P J.ride kf l hl j hj fun i hi => hr i (Nat.lt_trans hi hj)]
  exact senderLays_taken 0 o J.P J.ride
    (fun w h => J.data w { heard := h, own := own₀, seen := .bare [] }) j hj hn own ho takes ht

/-! ## 2 Closed facts -/

/-- The entries of the mask rows of notice number 0 of a list of notices, at the written codes. -/
def maskEntriesW (ns : Array OracleNotice) : Nat :=
  (ns.getD 0 default).shape.maskRows *
    (keyFull.codes.mask.getD (ns.getD 0 default).shape.maskCode default).ell

/-- **At the written sizes each of the two sendings has a message 0 with mask rows.** -/
theorem ownersW :
    0 < (Wf.messageOf keyFull.ranges.x).size ∧ 0 < maskEntriesW (Wf.messageOf keyFull.ranges.x) ∧
      0 < maskEntriesW #[keyFull.once.input] := by
  decide +kernel

/-! ## 3 The two ends -/

section
variable {W X : Type} (K : KeyPub) (hK : fullPub = some K) (one : OneTime) (h : OneFull one)
  (N : Pieces) (groups : List (List Nat)) (first : Nat) (own₀ : X)
include hK h

/-- **THE SENDER OF THE MULTIPLICITIES LAYS THE MASK COINS OF ITS MESSAGE 0 IN THE ORDER OF TAKING.** -/
theorem msgOwner_lays_in_order (entry : W → Nat → Nat → GF) (ride : Nat → Option Ride)
    (hr : ridesOk ride (Wf.messageOf keyFull.ranges.x) kRanges = true) (h0 : ride 0 = none)
    (takes : Nat) (ht : takes ≤ maskEntriesW (Wf.messageOf keyFull.ranges.x)) :
    ∃ own, OwnIs (keyBook K) 0 ⟨msgPlace, 0⟩
        (dueR (msgJob (X := X) entry one N groups first ride).P ride) own ∧
      SenderLays (W := W) (keyBook K) 0 ⟨msgPlace, 0⟩ (tableAt K.sMsg 0)
        (fun c w hd n => maskWordE (msgJob (X := X) entry one N groups first ride).P ride
          ((msgJob (X := X) entry one N groups first ride).data w
            { heard := hd, own := own₀, seen := .bare [] }) 0 (own c)
          (takenNo ((Wf.messageOf keyFull.ranges.x).getD 0 default).shape.maskRows n))
        (· < takes) := by
  have hs : (msgJob (X := X) entry one N groups first ride).P.sent =
      Wf.messageOf keyFull.ranges.x := by
    rw [← h.ranges]; exact sendingPar_sent _ _ _ _ _
  have hc : (msgJob (X := X) entry one N groups first ride).P.codes = keyFull.codes := h.codes
  have hf := of_atFull full_k1 hK
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  have hsh : shapeAt (msgJob (X := X) entry one N groups first ride).P 0 =
      ((Wf.messageOf keyFull.ranges.x).getD 0 default).shape := by
    unfold shapeAt
    rw [hs]
  have e := job_lays_in_order (Bk := keyBook K) ⟨msgPlace, 0⟩
    (msgJob (X := X) entry one N groups first ride) own₀ kRanges K.sMsg
    (by rw [hc, hs]; exact hf.1.2) (rides_of_ok hs hr) rfl 0 (by rw [hs]; exact ownersW.1) h0 takes
    (by rw [hsh, hc]; exact ht)
  rw [hsh] at e
  exact e

/-- **THE SENDER OF THE INDEX MASKS LAYS THE MASK COINS OF ITS MESSAGE IN THE ORDER OF TAKING.** -/
theorem idxOwner_lays_in_order (takes : Nat) (ht : takes ≤ maskEntriesW #[keyFull.once.input]) :
    ∃ own, OwnIs (keyBook K) 0 ⟨idxPlace, 0⟩
        (dueR (idxJob (W := W) (X := X) one N groups first).P fun _ => none) own ∧
      SenderLays (W := W) (keyBook K) 0 ⟨idxPlace, 0⟩ (tableAt K.sIdx 0)
        (fun c w hd n => maskWordE (idxJob (W := W) (X := X) one N groups first).P (fun _ => none)
          ((idxJob (W := W) (X := X) one N groups first).data w
            { heard := hd, own := own₀, seen := .bare [] }) 0 (own c)
          (takenNo keyFull.once.input.shape.maskRows n))
        (· < takes) := by
  have hs : (idxJob (W := W) (X := X) one N groups first).P.sent = #[keyFull.once.input] := by
    rw [← h.idx]; exact sendingPar_sent _ _ _ _ _
  have hc : (idxJob (W := W) (X := X) one N groups first).P.codes = keyFull.codes := h.codes
  have hf := of_atFull full_k1 hK
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  have hsh : shapeAt (idxJob (W := W) (X := X) one N groups first).P 0 =
      keyFull.once.input.shape := by
    unfold shapeAt
    rw [hs]
    rfl
  have e := job_lays_in_order (Bk := keyBook K) ⟨idxPlace, 0⟩
    (idxJob (W := W) (X := X) one N groups first) own₀ 0 K.sIdx
    (by rw [hc, hs]; exact hf.1.1) (rides_of_ok hs rides_full.1) rfl 0
    (by rw [hs]; exact Nat.zero_lt_one) rfl takes (by rw [hsh, hc]; exact ht)
  rw [hsh] at e
  exact e

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.job_lays_in_order
#print axioms ProofFile.Honest.K1.ownersW
#print axioms ProofFile.Honest.K1.msgOwner_lays_in_order
#print axioms ProofFile.Honest.K1.idxOwner_lays_in_order
