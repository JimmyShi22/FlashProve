-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/OwnMsgsIndex.lean: THE SHARED "SENDING" (the kind K1): UNDER
THE RECORD OF PREMISES K1Seated (Honest/K1/Seated.lean) AT THE OPENING: THE RECORD's OWN FIELD msgs,
AT THE MESSAGE WHOSE SEAT IS THE TABLE's N.index: WITH WHICH NUMBER OF THE WITNESS's MESSAGES, AND
AT WHICH n. Three theorems; no definition.

  - ownMsgs_index: the pen of the threads' statement, to the letter: general in all letters; no
    head; no closed fact: UNDER K : K1Seated L b blk wit J own₀ .opening …: THERE IS an n below the
    job's number of messages, sampled, whose seat is L.N.index, and OwnMsgs stands at arr
    L.N.index.1 L.N.index.2 at msgTxt 0 wit J own₀ n. Fields spent: seats, msgs.
  - index_alone: UNDER h (the library's head: A HYPOTHESIS), O: of the opening's plan's messages
    NUMBER 4 ALONE sits at the table's N.index (indexW, index_two, K1NumAtHead.lean).
  - ownMsgs_index_four: n IS NAMED: UNDER h, O, K at b = 2 and arr := P5J.At.arr Zp, and three
    equations on the letters (hbs : L.bs = cF.blocksInOrder · hN : L.N = P5J.At.N Zp cF · hP : the job's plan
    is the opening's at the description's own ground), which hold at ProofFile's lettersHead by unfolding
    and at the prover that a filling makes by RecordAtWider.lean: OwnMsgs stands at P5J.At.arr Zp
    N.index.1 N.index.2 at msgTxt 0 wit J own₀ 4.

What they are. Each end is the record's own field msgs at one n, its number rewritten by an equation
of seats: no new sentence on the Script or on coins. K1Seated AT REAL LETTERS IS A PREMISE: msgs is
paid once a Script is laid with our lot at that number: no Script is laid.

Limits. Nothing on what an entry of that message holds. The full size alone (the last two). Nothing
on soundness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (MsgT Mem)
open VerifiableInference.Desc.K1 (parGF seatOfMsg)
open ProofFile.Honest.FirstThread (Letters OwnMsgs OwnPads)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}

/-- **THE RECORD's msgs AT THE MESSAGE WHOSE SEAT IS N.index.** n stands under "there is". -/
theorem ownMsgs_index {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat}
    {blk : Block S Cl} {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X}
    {own₀ : X} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}
    (K : K1Seated L b blk wit J own₀ .opening arr seats₀ ms rad) :
    ∃ n, n < J.P.sent.size ∧ (shapeAt J.P n).answers ≠ 0 ∧
      seatAtMember L.bs b J.P n = L.N.index ∧
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs b) (arr L.N.index.1 L.N.index.2)
        (L.thread.front + roundsTo L.bs b) (msgTxt 0 wit J own₀ n) := by
  obtain ⟨n, hn, ha, e⟩ := (K.seats L.N.index).1
    (show L.N.index ∈ L.N.sent 0 0 ++ [L.N.index] from
      List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
  refine ⟨n, hn, ha, e.symm, ?_⟩
  have t := K.msgs n hn
  rw [← e] at t
  exact t

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **NUMBER 4 ALONE.** -/
theorem index_alone (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size)
    (e : seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n = (P5J.At.N Zp cF).index) :
    n = 4 := by
  rw [seat_two_written h O n,
    show (P5J.At.N Zp cF).index = (1, 0) from K1.index_atAll h O (K1.pin1_atAll h)] at e
  rw [K1.eG_atAll h O (K1.pin1_atAll h)] at hn
  have hm : n ∈ (List.range parGF.sent.size).filter
      (fun n => decide (seatOfMsg parGF 0 n = (1, 0))) :=
    List.mem_filter.2 ⟨List.mem_range.2 hn, decide_eq_true e⟩
  rw [indexW] at hm
  exact List.mem_singleton.1 hm

/-- **n IS NAMED: AT MESSAGE NUMBER 4.** -/
theorem ownMsgs_index_four (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {blk : Block S ProofFile.Cl}
    {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X} {own₀ : X}
    {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}
    (K : K1Seated L 2 blk wit J own₀ .opening (P5J.At.arr Zp) seats₀ ms rad)
    (hbs : L.bs = cF.blocksInOrder) (hN : L.N = P5J.At.N Zp cF)
    (hP : J.P = (K1.firstPar Bs.G₀.first (K1.gpOf Zp))) :
    OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs 2)
      (P5J.At.arr Zp (P5J.At.N Zp cF).index.1 (P5J.At.N Zp cF).index.2)
      (L.thread.front + roundsTo L.bs 2) (msgTxt 0 wit J own₀ 4) := by
  obtain ⟨n, hn, -, e, t⟩ := ownMsgs_index K
  rw [hbs, hN, hP] at e
  rw [hP] at hn
  obtain rfl := index_alone h O hn e
  rw [hN] at t
  exact t

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.ownMsgs_index
#print axioms ProofFile.Honest.K1.index_alone
#print axioms ProofFile.Honest.K1.ownMsgs_index_four
