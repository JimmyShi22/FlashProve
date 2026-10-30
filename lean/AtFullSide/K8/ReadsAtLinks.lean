-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/ReadsAtLinks.lean: the honest side of the smallness test (K8): WHAT SEGMENT l READS
OFF THE THREAD's OWN WITNESS AT THE SEATS OF ITS MATRICES IS THE PACKING OF THE READER's CELLS, at
the segments 1 to 24, at the joined `Script`, at the book and the prover that `onlineProverFromPublicFiles` returns, at
the inputs `ReadyInput`, under the library's head: the hypothesis hrd of `hst_of_reads`
(Johnson/Desc/ProofFile/Honest/K8/ShowsAtStand.lean, not imported), in its own form. EXCHANGED, NOT
PAID: two hypotheses of other kinds are taken. One definition, a public test. Lemmas; none of the
library's goals. It lies in the side library because it imports files of it.

  `ownersOk`         A PUBLIC TEST on the written labels (`K8Q35.labW`, `nmW`,
                     Johnson/K8Q35R/MatsAtHead.lean), with three bounds
  `ownersW`          BY LEAN's KERNEL: each matrix's owner's link is below 25 and its number there
                     below 26; below 9 where the owner's link is 0
  `ownersW_can_fail`   THREE CONTROLS THAT SAY NO: 24 for the link; 8 for the number; 7 for the
                     number at link 0. The bound 26 is not sharp: it is the one that
                     `labelNo_arrayLabel` (Honest/K5/Law/PackedVals.lean) takes
  `ownersW_borrow`   there are 24 matrices whose owner is another segment, or another number: so
                     hBor below is not idle
  `reads_at_links`   THE END

How. `reads_of_owners_at_head` (Honest/K8/ReadsOfOwnersAtHead.lean): what the segment reads is the
witness's message of the OWNER's number. Where the owner's link is from 1 to 24 that message is one
of a code switch's own: `msg_owner_at_head` (AtFullSide/K2/OwnMsgIsPackedAtHead.lean). Where it is 0
the message is the opening's: hK1. That the head's labels and count are the written ones:
`lab_at_head`, `nm_at_head` (Honest/K8/PlanAtHead.lean). That the book which `onlineProverFromPublicFiles` returns is the
maker's: `makers_book_one` (AtFullSide/K14/MakersBookOne.lean).

What stays a hypothesis.
  * h: the library's head. hA: `onlineProverFromPublicFiles` returns. hb: Bs is what the maker's base returns.
  * F, hin: the joined list is fit, and holds the switches' share at the plan's own letters, with
    the readers that the opening's jobs read (`(wit v).R`).
  * hD: the light test at the reads' filling says yes at each instance that passes `okStart`.
    Proved by nobody.
  * hK1, ON THE SCRIPT AND THE HIDDEN INPUT: at the thread's stand in front of the draw, the
    witness's message of the plan's number of (link 0, an array's message) holds the packing of the
    reader's cells of (0, mu), at mu below 9. Another kind's limb: not shown here.
  * hBor, ON THE HIDDEN INPUT: at a valid input the packing of the reader's cells at a matrix's
    owner is the packing at the segment's own number. At a matrix that the segment owns it says
    nothing. Shown at no input. `bor_of_trace` (Honest/K8/BorrowedAtTrace.lean, not imported) has
    its equation at the reader of cells that a trace gives, under a condition on the public data and
    one on the trace; that `(wit v).R` is such a reader is shown by nobody.

Limits. An implication from the thread's stand: where the thread stands at no state, or `ReadyInput`
holds of no input, it says nothing. hK1 and hBor speak of the hidden input: in front of a sentence
on hiding neither stands as a bare hypothesis. It speaks of the reader's cells: that these are any
trace's is not said. NOT IN FRONT OF A LAW OVER COINS. One choice of sizes
(`Sz.ref`). Chain 0 alone. The full size; the format's second hash function. Closed facts by Lean's kernel,
with an option raised. One instance is taken away, as in the files beneath (no default table of
scales). It takes files under Johnson/Goal/Meaning/ and Johnson/Road/K4/ through what it imports.
hK1 ranges over all nine arrays of link 0, though the proof calls it for a borrowed matrix alone.
That the joined Script is the honest prover's is not said here: it is laid from lots, and holds what
their texts say. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import AtFullSide.K14.MakersBookOne
import AtFullSide.K2.OwnMsgIsPackedAtHead
import Johnson.Desc.ProofFile.Honest.K8.ReadsOfOwnersAtHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.K8.PlanAtHead
import Johnson.K8Q35R.MatsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8
open OnBytes.HonestTrace (Sz packedCells)
open OnBytes.Maker (WholeD)
open OnBytes.Params (ReqArray)
open VerifiableInference.Desc (Chain Strs Place arrayOf laidAt)
open VerifiableInference.Desc.Sound (MsgT readAt)
open Meaning (labAt ownerK ownerA nameOf sizesOf)
open K8Q35 (labW nmW)
open P5J (AtMgA F0T CellsM TS)
open P1K8T (seatC)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (withSwitchData switchShareAt)
open ProofFile.Honest.K2.Law (ReadsLight ShareIn)
open ProofFile.Honest.K8 (reads_of_owners_at_head nm_at_head lab_at_head)
open AtFullSide.K2 (msg_owner_at_head)
open AtFullSide.K14 (makers_book_one)

/-! ## 1 The written labels -/

/-- **A PUBLIC TEST** on the written labels, with three bounds: each matrix's owner's link is below
a and its number there below b; below c where the owner's link is 0. -/
def ownersOk (a b c : ℕ) : Bool :=
  (List.range 25).all fun l => (List.range (nmW l)).all fun μ =>
    decide (ownerK (labW l μ) < a) && decide (ownerA (labW l μ) < b) &&
      (ownerK (labW l μ) != 0 || decide (ownerA (labW l μ) < c))

set_option maxRecDepth 1000000 in
/-- **Each matrix's owner's link is below 25, and its number there below 26; below 9 where the
owner's link is 0.** -/
theorem ownersW : ownersOk 25 26 9 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Three controls: each bound can fail: at 24 for the link; at 8 for the number; at 7 for the
number at link 0. -/
theorem ownersW_can_fail :
    (ownersOk 24 26 9 || ownersOk 25 8 9 || ownersOk 25 26 7) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There are 24 matrices whose owner is not (the segment, the number). -/
theorem ownersW_borrow : ((List.range 25).map fun l => ((List.range (nmW l)).filter fun μ =>
    !(ownerK (labW l μ) == l && ownerA (labW l μ) == μ)).length).foldl (· + ·) 0 = 24 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-! ## 2 The end -/

/-- **What a segment from 1 to 24 reads off the thread's witness at its matrices' seats is the
packing of the reader's cells**: exchanged, not paid: for hK1 (the opening's limb) and hBor (the
reader's cells at a borrowed matrix), each shown nowhere here. Q is the joined `Script`, by hQ;
Vd is `ReadyInput`, by hV. NOT IN FRONT OF A LAW OVER COINS. -/
theorem reads_at_links {W₀ Rc Tr X₀ X Y : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (front : Nat) (seats : List (Nat × Nat))
    (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (jobs : List (Nat × K1.SendJob (K1.PlaceIn ProofFile.Inst) Y))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt A.B cF.blocksInOrder front Zp Bs.G₀
      (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) (fun v => (wit v).R) rest) Oth)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hQ : Q = joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (hV : Vd = ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hD : ∀ ξ, (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true → ReadsLight Zp Bs.G₀ ξ)
    {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {l : ℕ} (h1 : 1 ≤ l)
    (hl : l < 25)
    (hK1 : ∀ k s m E e,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      ∀ (mu : ℕ) (B : ReqArray) (i c : ℕ) (rp : ℕ × ℕ), mu < 9 →
        arrayOf (P5J.At.layout Zp) 0 (nameOf mu) = some B → i < B.sizeI → c < B.sizeC →
        laidAt B i c = some rp →
        ((lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
            (m.st.heard ++ e)).msg (P5J.At.num Zp 0 B.message) false rp.1 rp.2 =
          algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (wit m.st.input).R.cells.cell 0 mu i c))
    (hBor : ∀ v, v = w ∧ Vd v → ∀ μ, μ < nmW l → ∀ r c,
      packedCells Sz.ref (wit v).R.cells.cell (ownerK (labW l μ)) (ownerA (labW l μ)) r c =
        packedCells Sz.ref (wit v).R.cells.cell l μ r c) :
    ∀ k s m E e,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      ∀ (μ : Fin (sizesOf (P5J.At.X Zp) l).NM) (r c : ℕ),
        r < Alg.symRows ((sizesOf (P5J.At.X Zp) l).m μ) →
        c < (sizesOf (P5J.At.X Zp) l).k μ →
        readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
            ((lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
              (m.st.heard ++ e))
            (seatC Zp l μ r c).1 false (seatC Zp l μ r c).2.1 (seatC Zp l μ r c).2.2 =
          algebraMap Cb.Gl.F Cb.Gl.E
            (packedCells Sz.ref (wit m.st.input).R.cells.cell l μ r c) := by
  intro k s m E e hT
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hb)
  have hv : m.st.input = w ∧ Vd m.st.input := hT.1.2.2.2.2.2.2
  have hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart m.st.input.x = true := by
    have q := hv.2
    rw [hV] at q
    exact q.1
  have eN : (sizesOf (P5J.At.X Zp) l).NM = nmW l := nm_at_head h (by omega)
  have eLab := fun μ => lab_at_head h (l := l) (by omega) μ
  refine reads_of_owners_at_head h hl _
    (fun μ r c => algebraMap Cb.Gl.F Cb.Gl.E
      (packedCells Sz.ref (wit m.st.input).R.cells.cell l μ r c)) ?_
  intro μ B x r c hB _ _ hr hc hxp
  have hμ : μ.val < nmW l := eN ▸ μ.isLt
  have t0 := ownersW
  unfold ownersOk at t0
  have t := List.all_eq_true.1 (List.all_eq_true.1 t0 l (List.mem_range.2 hl)) μ.val
    (List.mem_range.2 hμ)
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at t
  rw [eLab μ.val] at hB ⊢
  show _ = algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (wit m.st.input).R.cells.cell l μ.val r c)
  rw [← hBor m.st.input hv μ.val hμ r c]
  rcases Nat.eq_zero_or_pos (ownerK (labW l μ.val)) with e0 | hpos
  · have t9 : ownerA (labW l μ.val) < 9 := by
      have q := t.2
      rw [e0] at q
      simpa using q
    rw [e0] at hB ⊢
    exact hK1 k s m E e hT _ B r c x t9 hB hr hc hxp
  · subst hQ
    have hBk : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) Johnson.G.proofSendsFull.1
        Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
        (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B := by
      obtain ⟨B', -, hB', -, -, hall⟩ := makers_book_one h
      rw [(hall _ _ _ _ _ P A hA).1]
      exact hB'
    exact msg_owner_at_head h O hBk front seats wit own₀ jobs Oth
      (fun v => (wit v).R) rest F hin cells tok hD hpos t.1.1 t.1.2 hB k m.st.input hx
      (m.st.heard ++ e) hr hc hxp

end AtFullSide.K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K8.ownersOk
#print axioms AtFullSide.K8.ownersW
#print axioms AtFullSide.K8.ownersW_can_fail
#print axioms AtFullSide.K8.ownersW_borrow
#print axioms AtFullSide.K8.reads_at_links
