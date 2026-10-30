-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/JoinFitFull.lean: UNDER THE LIBRARY's HEAD AND THE OPENING THE JOINED LIST OF ALL
THREE SENDERS OF THE FIRST CHAIN IS FIT (`JoinFit`,
Johnson/Desc/ProofFile/Honest/Thread/JoinFit.lean, of other authors): THE SHARED SENDING's 52 JOBS
AND, FOR THE OTHERS' RECORD, THE SUM OF THE CODE SWITCH's SHARE (`switchShareAt`,
…/Honest/K2/JoinShare.lean) AND THE PROXIMITY TEST's (`K12.k12Share`, …/Honest/K12/JoinShare.lean,
of other authors), AT THE PLAN's LIST OF THE FIRST CHAIN's SEATS. AN ASSEMBLY: the nine premises on
the record K of `joinFit_at_sum_ten` and `joinFit_at_sum_book` (AtFullSide/K2/JoinFitAtSumPaid.lean)
ARE PAID AT THAT SHARE, each by a law of its authors. Small lemmas; two statements with their
proofs; no definition.

  `lastSend_iff`    the test `lastSend` as a sentence: 76 ≤ s and s ≤ 80
  `k12_face`        seven of the nine, at `K12.k12Share` at the tree 77, the member 354 and the
                    plan's numbering, under the head and hJ (the job's parameters have six stages)
  `joinFit_full_ten`   the list is fit; LEFT: the head · the opening · hJ · hcoins
  `joinFit_full`    AT THE BOOK THAT `onlineProverFromPublicFiles` RETURNS; LEFT: the head · the opening · hA (it
                    returns) · hJ

By, of the proximity test's authors (…/Honest/K12/OwnedAtHead.lean, ShareAtHead.lean):
`faceMsgs_k12` · `faceMsgs_nodup_k12` · `facePads_k12` · `testPl_seats_nodup` · `hfarM_k12` ·
`hfarP_k12` · `msgsOwned_k12` · `padsOwned_k12`.

Limits. "FIT" IS A SENTENCE ON NUMBERS, SEATS, PLACES AND COUNTS AND ON LOTS THAT AGREE: A LOT WHOSE
TEXT RETURNS NOTHING COUNTS LIKE ANY OTHER: that a text answers is not in it. OF THE BOOK "FIT" ASKS
THE SHARED SENDING's COUNTS ALONE (the field coins): the book's counts at the code switch's and the
proximity test's addresses are not asked about. THE TREE 77, THE MEMBER 354 AND hJ ARE FIXED BY HAND
OR ASSUMED: no law here ties them to a job that a thread lays (their authors say so of their own
files). The job J, its letters and both records' rest are free. The head and the opening are
premises; that they can be met together with hA is not said. The first chain alone. The full size;
the format's second hash function. Nothing on any property.
-/
import AtFullSide.K2.JoinFitAtSumPaid
import Johnson.Desc.ProofFile.Honest.K12.JoinShare
import Johnson.Desc.ProofFile.Honest.K12.OwnedAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (momL)
open ProofFile.Honest.FirstThread (TreeLot Others JoinFit byNo k1Jobs)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- The test `lastSend` as a sentence. -/
theorem lastSend_iff {s : Nat} : lastSend s = true ↔ 76 ≤ s ∧ s ≤ 80 := by
  unfold lastSend
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {W₀ Rc Xi Tr Xj X X₂ : Type} {Bk : ProverCoinCounts}

/-- hJ IS A PREMISE. **SEVEN OF THE NINE PREMISES ON THE RECORD, AT THE PROXIMITY TEST's SHARE.**
The two others are its authors' own `hfarM_k12` and `hfarP_k12`, as they stand. -/
theorem k12_face (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (ch : Nat)
    (J : K12.TestJob (Local W₀ Rc Xi Tr) X₂) (hJ : J.p.nums.stages.length = 6) (own₂ : X₂)
    (n₀ : Nat) (ok : Local W₀ Rc Xi Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) {K : Others Bk (Local W₀ Rc Xi Tr)}
    (hK : K = K12.k12Share ch J own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂) :
    (∀ n ∈ ProofFile.Honest.FirstThread.nums K.ml, n ∈ lastNumsW) ∧
      (ProofFile.Honest.FirstThread.nums K.ml).Nodup ∧
      (∀ s ∈ ProofFile.Honest.FirstThread.seatsOf K.pl, s ∈ lastPadsW) ∧
      (ProofFile.Honest.FirstThread.seatsOf K.pl).Nodup ∧ K.tn = [354] ∧
      MsgsOwnedAt K.ml (P5J.At.arr Zp) lastSeatsW ∧ PadsOwnedAt K.pl lastSeatsW := by
  subst hK
  have eA := arrW_at_head h.toAtMg
  refine ⟨?_, ?_, ?_, K12.testPl_seats_nodup ch J codes sh sh₁ 77, rfl, ?_, ?_⟩
  · intro n hn
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hn
    obtain ⟨q, hq, b1, b2, e⟩ := K12.faceMsgs_k12 ch J hJ own₂ n₀ (P5J.At.arr Zp) ok L hL
    refine List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, lastSend_iff.2 ⟨b1, b2⟩⟩, ?_⟩
    rw [e, eA]
  · show ((K12.testMsgLots (Bk := Bk) ch J own₂ n₀ 77 (P5J.At.arr Zp) ok).map (·.n)).Nodup
    rw [eA]
    exact K12.faceMsgs_nodup_k12 ch J hJ own₂ n₀ ok
  · intro s hs
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hs
    obtain ⟨q, hq, b1, b2, e1, e2⟩ := K12.facePads_k12 ch J hJ codes sh sh₁ L hL
    refine List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, lastSend_iff.2 ⟨b1, b2⟩⟩, ?_⟩
    rw [e1, e2]
  · intro q hq
    obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
    exact K12.msgsOwned_k12 ch J hJ own₂ n₀ (P5J.At.arr Zp) ok q hq1 (lastSend_iff.1 hq2).1
      (lastSend_iff.1 hq2).2
  · intro q hq
    obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
    exact K12.padsOwned_k12 ch J hJ codes sh sh₁ q hq1 (lastSend_iff.1 hq2).1
      (lastSend_iff.1 hq2).2

/-- hJ AND hcoins ARE PREMISES. **UNDER THE HEAD AND THE OPENING THE JOINED LIST OF ALL THREE
SENDERS IS FIT.** -/
theorem joinFit_full_ten (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj) (front : Nat)
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj) (own₀ : X)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr))
    -- THE PROXIMITY TEST's SHARE: ITS JOB AND LETTERS
    (ch : Nat) (J : K12.TestJob (Local W₀ Rc Xi Tr) X₂) (hJ : J.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc Xi Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot Bk (Local W₀ Rc Xi Tr))
    -- THE BOOK's COUNTS
    (hcoins : ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀),
      dueAt (Bk.rowsOf 0) ⟨x.2.P.place, 0⟩ = K1.dueR x.2.P x.2.ride) :
    JoinFit cF.blocksInOrder front (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀))
      ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add
        (K12.k12Share ch J own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := k12_face h ch J hJ own₂ n₀ ok codes sh sh₁ rest₂ rfl
  exact joinFit_at_sum_ten h O no Dt Dd front wit own₀ D readers rest f1 f2 f3 f4 f5
    (K12.hfarM_k12 h ch J hJ own₂ n₀ ok) (K12.hfarP_k12 h ch J hJ codes sh sh₁) f6 f7 hcoins

/-- hJ AND hA ARE PREMISES. **THE SAME AT THE BOOK THAT `onlineProverFromPublicFiles` RETURNS.** -/
theorem joinFit_full (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {X₀ Xa : Type} {P : OnlineProverParts W₀ Rc Tr X₀ Xa} {A : OnlineProverWithDescription W₀ Rc Tr X₀ Xa}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj) (front : Nat)
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj) (own₀ : X)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : Nat → TreeLot A.B (Local W₀ Rc Xi Tr))
    -- THE PROXIMITY TEST's SHARE: ITS JOB AND LETTERS
    (ch : Nat) (J : K12.TestJob (Local W₀ Rc Xi Tr) X₂) (hJ : J.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc Xi Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc Xi Tr)) :
    JoinFit cF.blocksInOrder front (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀))
      ((switchShareAt A.B cF.blocksInOrder front Zp Bs.G₀ D readers rest).add
        (K12.k12Share ch J own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂)) :=
  joinFit_full_ten h O no Dt Dd front wit own₀ D readers rest ch J hJ own₂ n₀ ok codes sh sh₁ rest₂
    (ProofFile.Honest.FirstThread.coins_at_head h O no Dt Dd hA)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lastSend_iff
#print axioms ProofFile.Honest.K2.Law.k12_face
#print axioms ProofFile.Honest.K2.Law.joinFit_full_ten
#print axioms ProofFile.Honest.K2.Law.joinFit_full
