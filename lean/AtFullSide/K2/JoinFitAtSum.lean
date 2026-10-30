-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/JoinFitAtSum.lean: UNDER THE LIBRARY's HEAD AND THE OPENING: THE JOINED LIST OF THE
SHARED SENDING's 52 JOBS AND, FOR THE OTHERS' RECORD, THE SUM OF THE CODE SWITCH's SHARE AND A
RECORD K IS FIT (`JoinFit`, Johnson/Desc/ProofFile/Honest/Thread/JoinFit.lean, of other authors), AT
THE PLAN's LIST OF THE FIRST CHAIN's SEATS: AN ASSEMBLY: `joinFit_head`
(…/Honest/Thread/JoinAtHead.lean, theirs) IS CALLED, AND EACH OF ITS TEN PREMISES IS PAID OR HANDED
ON BY NAME. Three small lemmas and a closed fact by Lean's kernel; one statement with its proof:
calls alone. It lies in the side library because it imports a file of it.

  `shared_nos`      the numbers of the shared sending's list by written numbers are `sharedNos`
  `sharedSend_gives`, `shared_in_all`   the test `sharedSend` as a sentence · under the head a
                    written seat of the shared sending's stands in the plan's list of all seats
  `not354`          BY LEAN's KERNEL: 354 is none of them; a control: 356 is
  `joinFit_at_sum`  THE ASSEMBLY.
      PAID INSIDE: hml · hpl · htn (`sum_of_shares`) · the share's halves of hfarM · hfarP
      (`share_far_msgs_at_head`, `share_far_pads_at_head`) · hdis (`share_meets_dis`; `not354`) ·
      htrees (`trees_of_three`, `share_trees_limb`, `shared_nos`) · the share's limbs of hown
      (`owned_at_join`) · hwhole (`declared_head`, AtFullSide/K1/DeclaredSeatsAtHead.lean, of other
      authors).
      LEFT, BY NAME: OF K: hn · hn' · hp · hp' · ht (its public face lies in the plan's third class)
      · hfarMK · hfarPK (its halves of hfarM · hfarP) · m3 · p3 (its limbs of hown) · OF THE SHARED
      SENDING: hK1 (its limb of hown, in its authors' own form) · hcoins

Limits. THE ELEVEN ARE PREMISES: SHOWN HERE OF NO RECORD AND NO BOOK. "Fit" is a sentence on
numbers, seats, places and counts and on lots that agree: that a lot's text answers is not in it.
The head and the opening are premises. The full size; the format's second hash function. Nothing on any
property.
-/
import AtFullSide.K1.DeclaredSeatsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.SharesApartAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.JoinShareMeets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (momL)
open ProofFile.Honest.FirstThread (TreeLot Others JoinFit joinMl joinPl byNo k1Jobs byNo_at_head
  joinFit_head)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- The numbers of the shared sending's list by written numbers. -/
theorem shared_nos {Xj X : Type} (J₂ : K1.SendJob (K1.PlaceIn Xj) X)
    (Jl : Nat → Bool → K1.SendJob (K1.PlaceIn Xj) X) (Jw : K1.SendJob (K1.PlaceIn Xj) X) :
    (K1.k1MembersW J₂ Jl Jw).map (·.1) = sharedNos := by
  unfold K1.k1MembersW K1.k1Members sharedNos
  rw [List.map_append, List.map_cons, List.map_flatMap]
  rfl

/-- What the test `sharedSend` says, as a sentence. -/
theorem sharedSend_gives {s : Nat} (hs : sharedSend s = true) :
    s = 0 ∨ (∃ l, l < 25 ∧ ∃ d, s = 3 * l + momL d) ∨ s = 81 := by
  unfold sharedSend at hs
  rw [Bool.or_eq_true, Bool.or_eq_true] at hs
  rcases hs with (c | c) | c
  · exact Or.inl (beq_iff_eq.1 c)
  · exact Or.inr (Or.inr (beq_iff_eq.1 c))
  · obtain ⟨l, hl, c'⟩ := List.any_eq_true.1 c
    obtain ⟨d, -, e⟩ := List.any_eq_true.1 c'
    exact Or.inr (Or.inl ⟨l, List.mem_range.1 hl, d, beq_iff_eq.1 e⟩)

/-- 354 is none of the shared sending's numbers; a control: 356 is one. -/
theorem not354 : 354 ∉ sharedNos ∧ 356 ∈ sharedNos := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {W₀ Rc Xi Tr Xj X : Type} {Bk : ProverCoinCounts}

/-- Under the head a written seat of the shared sending's stands in the plan's list of all seats. -/
theorem shared_in_all (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (q : P5T.PSeat)
    (hq : q ∈ sharedSeatsW) : q ∈ P5J.At.pseatsAll Zp := by
  refine AtFullSide.K1.first_in_all Zp q ?_
  show q ∈ P5T.planSeats Zp Zp.D.1
  rw [h.toAtMg.seats]
  exact (List.mem_filter.1 hq).1

/-- THE ELEVEN ARE PREMISES. **UNDER THE HEAD AND THE OPENING THE JOINED LIST IS FIT, AT THE SUM OF
THE KIND's SHARE AND A RECORD OF THE PLAN's THIRD CLASS.** -/
theorem joinFit_at_sum (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
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
    -- OF THE SHARED SENDING: ITS LIMB OF "owned", IN ITS AUTHORS' FORM; THE BOOK's COUNTS
    (hK1 : ∀ q ∈ P5J.At.pseatsAll Zp,
      (q.send = 0 ∨ (∃ l, l < 25 ∧ ∃ d, q.send = 3 * l + momL d) ∨ q.send = 81) →
      (∃ L ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀
          (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀))
          ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K),
        L.n = P5J.At.arr Zp q.j q.t) ∧
      ∃ L ∈ joinPl cF.blocksInOrder (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀))
          ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K),
        L.j = q.j ∧ L.t = q.t)
    (hcoins : ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀),
      dueAt (Bk.rowsOf 0) ⟨x.2.P.place, 0⟩ = K1.dueR x.2.P x.2.ride) :
    JoinFit cF.blocksInOrder front (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀))
      ((switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ D readers rest).add K) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := sum_of_shares h O front D readers rest hn hn' hp hp' ht
  have eN : (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)).map (·.1) = sharedNos := by
    rw [byNo_at_head h O no Dt Dd]
    exact shared_nos _ _ _
  refine joinFit_head h O no Dt Dd front (P5J.At.seats Zp) wit own₀ a1 a2 ?_ ?_ ?_ a3 ?_ ?_ hcoins
    (AtFullSide.K1.declared_head h)
  · intro L' hL'
    rcases List.mem_append.1 hL' with c | c
    · exact share_far_msgs_at_head h.toAtMg O cF.blocksInOrder front D readers rest L' c
    · exact hfarMK L' c
  · intro L' hL'
    rcases List.mem_append.1 hL' with c | c
    · exact share_far_pads_at_head h.toAtMg O cF.blocksInOrder front D readers rest L' c
    · exact hfarPK L' c
  · refine owned_at_join h.toAtMg O a4 ?_ ?_ ?_ ?_
    · intro q hq
      exact (hK1 q (shared_in_all h q hq) (sharedSend_gives (List.mem_filter.1 hq).2)).1
    · intro q hq
      exact (hK1 q (shared_in_all h q hq) (sharedSend_gives (List.mem_filter.1 hq).2)).2
    · intro q hq
      obtain ⟨L, hL, e⟩ := m3 q hq
      exact ⟨L, List.mem_append.2 (Or.inr (a5.ml L hL)), e⟩
    · intro q hq
      obtain ⟨L, hL, e⟩ := p3 q hq
      exact ⟨L, List.mem_append.2 (Or.inr (a5.pl L hL)), e⟩
  · intro b hb
    rcases List.mem_append.1 hb with c | c
    · exact share_meets_dis h O no Dt Dd front D readers rest b c
    · rw [ht] at c
      rw [List.mem_singleton.1 c, eN]
      exact not354.1
  · refine trees_of_three h O ?_ (share_trees_limb a4) a6
    intro b hb
    rw [eN]
    exact hb

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.shared_nos
#print axioms ProofFile.Honest.K2.Law.sharedSend_gives
#print axioms ProofFile.Honest.K2.Law.not354
#print axioms ProofFile.Honest.K2.Law.shared_in_all
#print axioms ProofFile.Honest.K2.Law.joinFit_at_sum
