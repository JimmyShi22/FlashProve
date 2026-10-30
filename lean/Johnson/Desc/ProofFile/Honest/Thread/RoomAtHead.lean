-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/RoomAtHead.lean: THE COUNTING RIDER's SENTENCE IS A FACT AT
REACHED STATES. `riderRoom` (Honest/Thread/RidersStay.lean) was laid as a clause of the first
chain's letter `rides`: the index masks' ledger is open and has room for all that is still to be
taken, and that message is a member of no group. Our researcher's find: the library has both AS
LAWS AT WHAT IS REACHED BY THE MEMBERS' OWN STEPS, from border 3 to border 355, and has paid their
one structure of premises: `P1L20.room_at_reach`, `room_out_of_groups`
(Johnson/P1L20R/RoomFold.lean) under `RoomOwes`, and `roomOwes_paid` (RoomKeepAll.lean), under what
the library's head holds. The thread gives that reach (`thr_reach`, Honest/Thread/ReachFacts.lean).
So at `lettersHead` the ledger has JUST the fresh count less the entries taken in front of the
border; with the pile's length (the rider `riderPile` at the library's own count `P1L20.takenAt`)
and one public inequality, `RoomLeft` follows. So that clause need not ride: no member's clause of
`keeps` need say how it leaves the ledger. Calls of sealed lemmas, and arithmetic.

  `head_room`       at the thread: the ledger's exact count, and "a member of no group"
  `roomLeft_of`     `RoomLeft` from that count, the pile's length and the inequality
  `head_roomLeft`   both together: the rider's own sentence

Limits. The full size and the format's second hash function alone. The library's head has a member at the
name under four premises on the public files (the seal's `head_exists_at_name`); none of our files
calls it; no member of the head together with the thread's sentence is shown. The pile's length
stays a premise (PileAtHead.lean's `head_roomLeft_thr` proves it from the sealed
`pile_length_reach`). The inequality (the plan's room is at most the fresh ledger's free count) is a
premise on public data: the author knows of no lemma that proves it. None is one of the library's
goals. This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.RidersStay
import Johnson.P1L20R.RoomKeepAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- `RoomLeft` from the ledger's exact count, the pile's length and one inequality. -/
theorem roomLeft_of {room free0 t : Nat} {s : VerifiableInference.Desc.First.S}
    (hl : Johnson.Desc.First.Walk.Tied.leftIsB (free0 - t) s = true)
    (hp : s.out.pending.length = t) (hle : room ≤ free0) : RoomLeft room s := by
  unfold Johnson.Desc.First.Walk.Tied.leftIsB at hl
  cases hL : Johnson.Desc.First.Walk.Law.ledgerAt s with
  | none =>
    rw [hL] at hl
    cases hl
  | some l =>
    rw [hL] at hl
    simp at hl
    obtain ⟨hc, hn⟩ := hl
    refine ⟨l, hL, hc, ?_⟩
    rw [hn, hp]
    omega

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT THE THREAD, FROM BORDER 3 TO BORDER 355: THE INDEX MASKS' LEDGER IS THERE, IS NOT CLOSED
AND HAS JUST THE FRESH COUNT LESS WHAT IS TAKEN IN FRONT; AND THAT MESSAGE IS A MEMBER OF NO
GROUP.** At whatever opening of the maker the head holds. -/
theorem head_room (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {Bs base}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length) (h3 : 3 ≤ b) (h355 : b ≤ 355)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    Johnson.Desc.First.Walk.Tied.leftIsB
        (VerifiableInference.Desc.K1.free0Of Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) -
          P1L20.takenAt b) s = true ∧
      P1L20.outOfGroupsB s = true := by
  have hp := P5J.flat_ok h.toAtMg
  have HO := P1L20.roomOwes_paid h.scope h.reads O
  have hR := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  exact ⟨P1L20.room_at_reach h.scope h.reads O hp HO hR h3 h355,
    P1L20.room_out_of_groups h.scope h.reads O hp HO hR h3 h355⟩

/-- **THE COUNTING RIDER's OWN SENTENCE, AT THE THREAD**: from the pile's length and one inequality
on public data, asked at whatever opening the head holds. -/
theorem head_roomLeft (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {room : Nat}
    (hle : ∀ Bs base, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs
      base cF (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
      room ≤ VerifiableInference.Desc.K1.free0Of Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp))
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length) (h3 : 3 ≤ b) (h355 : b ≤ 355)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    (hpile : s.out.pending.length = P1L20.takenAt b) :
    RoomLeft room s ∧ P1L20.outOfGroupsB s = true := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  obtain ⟨h1, h2⟩ := head_room h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hb h3 h355 hT
  exact ⟨roomLeft_of h1 hpile (hle Bs base O), h2⟩

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.roomLeft_of
#print axioms ProofFile.Honest.FirstThread.head_room
#print axioms ProofFile.Honest.FirstThread.head_roomLeft
