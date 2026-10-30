-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/JoinOwnK1.lean: K1's share of "owned" (the field owned of
`JoinFit`, Honest/Thread/JoinFit.lean; the premise hown of `joinFit_head`,
Honest/Thread/JoinAtHead.lean). The seats at which K1's own lots sit have their two lots, whatever
the other senders lay. No definition.

  1  `k1_owns`, `own_of_seat` at every list: the seat of a job's message has K1's own two lots in
     the joined lists
  2  `own_k1_head` under the head: each seat of the plan's list whose sending is one of K1's is such
     a seat: by lemmas of K1's authors (Honest/K1/Law/SendsAreOurs.lean)

Limits.
  * "Owned" asks that a lot bears the number or the seat, not that its text answers
    (Honest/Thread/Join.lean, Limits).
  * Under the head h and the opening O: two hypotheses. The full size and the format's second hash function
    alone.
  * Of the seats in the other senders' sendings nothing is said: hown is not paid here. Of "each
    member that declares a tree has a number" (htrees) K1's share is that its 52 numbers stand in
    the list, which needs no lemma.
  * `own_k1_head` takes a seat q of the list of all three chains' seats; its pair (q.j, q.t) is then
    a seat of K1's lots at the first chain's flat list. That q stands in the first chain's own list
    (`P5J.At.pseats Zp`) is neither asked nor said here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.JoinAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.SendsAreOurs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (momL)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K1

variable {Bk : ProverCoinCounts} {Cl Wl Xi X : Type}

/-! ## 1 At every list -/

section
variable {bs : List (Block S Cl)} {front : Nat} {arr : ℕ → ℕ → ℕ} {wit : Wl → PlaceIn Xi} {own₀ : X}
  {jobs : List (Nat × SendJob (PlaceIn Xi) X)} {O : Others Bk Wl}

/-- **The seat of a job's message has K1's own two lots in the joined lists.** -/
theorem k1_owns {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) {n : Nat}
    (hn : n < x.2.P.sent.size) :
    (∃ L ∈ joinMl bs front arr wit own₀ jobs O,
        L.n = arr (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2) ∧
      ∃ L ∈ joinPl bs jobs O,
        L.j = (seatAtMember bs x.1 x.2.P n).1 ∧ L.t = (seatAtMember bs x.1 x.2.P n).2 := by
  constructor
  · refine ⟨⟨arr (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2,
      front + roundsTo bs x.1, msgTxt 0 wit x.2 own₀ n⟩, ?_, rfl⟩
    unfold joinMl
    exact List.mem_append_left _
      (mem_k1MsgLots hx (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩))
  · refine ⟨⟨(seatAtMember bs x.1 x.2.P n).1, (seatAtMember bs x.1 x.2.P n).2,
      fun k _ => padTxt 0 x.2 n k⟩, ?_, rfl, rfl⟩
    unfold joinPl
    exact List.mem_append_left _
      (mem_k1PadLots hx (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩))

/-- The same at a seat that is given as a pair. -/
theorem own_of_seat {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) {n : Nat}
    (hn : n < x.2.P.sent.size) {j t : Nat} (e : (j, t) = seatAtMember bs x.1 x.2.P n) :
    (∃ L ∈ joinMl bs front arr wit own₀ jobs O, L.n = arr j t) ∧
      ∃ L ∈ joinPl bs jobs O, L.j = j ∧ L.t = t := by
  have k := k1_owns (bs := bs) (front := front) (arr := arr) (wit := wit) (own₀ := own₀) (O := O)
    hx hn
  rw [← e] at k
  exact k

end

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

section
variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi)
include h O

/-- **K1's share of "owned" under the head**: a seat of the plan's list whose sending is one of K1's
(number 0; 3 l + momL d at l below 25; 81) has K1's own two lots in the joined lists, whatever the
other senders' record is. By K1's authors' `sendIsOurs_two`, `sendIsOurs_fifty`, `sendIsOurs_w`. -/
theorem own_k1_head (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X) (Oth : Others Bk Wl)
    {q : P5T.PSeat} (hq : q ∈ P5J.At.pseatsAll Zp)
    (hs : q.send = 0 ∨ (∃ l, l < 25 ∧ ∃ d, q.send = 3 * l + momL d) ∨ q.send = 81) :
    (∃ L ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth, L.n = P5J.At.arr Zp q.j q.t) ∧
      ∃ L ∈ joinPl cF.blocksInOrder (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)) Oth,
        L.j = q.j ∧ L.t = q.t := by
  have eJ := byNo_at_head (X := X) h O no Dt Dd
  rcases hs with hs | ⟨l, hl, d, hs⟩ | hs
  · obtain ⟨hn, e⟩ := sendIsOurs_two h O hq hs
    have p : (headJ₂ (X := X) Zp Bs.G₀ no Dt).P = K1.firstPar Bs.G₀.first (K1.gpOf Zp) :=
      two_plan_head Zp Bs.G₀ _ _
    refine own_of_seat (x := (2, headJ₂ (X := X) Zp Bs.G₀ no Dt)) ?_ (n := q.idx) ?_ ?_
    · rw [eJ]
      exact mem_k1MembersW.2 (Or.inl (mem_k1Members.2 (Or.inl rfl)))
    · show q.idx < (headJ₂ (X := X) Zp Bs.G₀ no Dt).P.sent.size
      rw [p]
      exact hn
    · show (q.j, q.t) = seatAtMember cF.blocksInOrder 2 (headJ₂ (X := X) Zp Bs.G₀ no Dt).P q.idx
      rw [p]
      exact e
  · obtain ⟨hn, e⟩ := sendIsOurs_fifty h O hl d hq hs
    have p : (headJl (X := X) Zp Bs.G₀ no Dt l d).P = K1.parL Zp Bs.G₀ l d :=
      later_plan_head Zp Bs.G₀ l d _ _
    refine own_of_seat (x := (K1.noL l d, headJl (X := X) Zp Bs.G₀ no Dt l d)) ?_ (n := q.idx)
      ?_ ?_
    · rw [eJ]
      exact mem_k1MembersW.2 (Or.inl (mem_k1Members.2 (Or.inr ⟨l, hl, d, rfl⟩)))
    · show q.idx < (headJl (X := X) Zp Bs.G₀ no Dt l d).P.sent.size
      rw [p]
      exact hn
    · show (q.j, q.t) =
        seatAtMember cF.blocksInOrder (K1.noL l d) (headJl (X := X) Zp Bs.G₀ no Dt l d).P q.idx
      rw [p]
      exact e
  · obtain ⟨hn, e⟩ := sendIsOurs_w h O hq hs
    have p : (headJw (X := X) Zp Bs.G₀ no Dd).P =
        K1.parW Zp.first (wGp Zp) 4 VerifiableInference.Desc.K13.Law.wMsgFull :=
      w_plan_head Zp _ _
    refine own_of_seat (x := (356, headJw (X := X) Zp Bs.G₀ no Dd)) ?_ (n := q.idx) ?_ ?_
    · rw [eJ]
      exact mem_k1MembersW.2 (Or.inr rfl)
    · show q.idx < (headJw (X := X) Zp Bs.G₀ no Dd).P.sent.size
      rw [p]
      exact hn
    · show (q.j, q.t) = seatAtMember cF.blocksInOrder 356 (headJw (X := X) Zp Bs.G₀ no Dd).P q.idx
      rw [p]
      exact e

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k1_owns
#print axioms ProofFile.Honest.FirstThread.own_of_seat
#print axioms ProofFile.Honest.FirstThread.own_k1_head
