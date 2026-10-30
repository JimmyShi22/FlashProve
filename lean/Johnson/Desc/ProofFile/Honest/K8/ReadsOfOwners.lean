-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ReadsOfOwners.lean: the honest side of the smallness test (K8):
WHAT SEGMENT l READS OFF A WITNESS AT THE SEATS OF ITS MATRICES (`readAt`,
Johnson/Desc/Sound/ReadAt.lean, at `P1K8T.seatC`, Johnson/P1K8R/SmallJoin.lean) IS THE WITNESS's OWN
MESSAGE OF THE OWNER's NUMBER, AT THE LAYOUT's ROW AND PLACE. Under the library's head, for each of
the 25 segments, at every witness. Of no kind of sender: no Script, no coins, no state of the
verifier. No definition. Two lemmas: joins of the library's own; none of the library's goals.

  `read_is_msg`       the reading at the seat of (μ, r, c) is w.msg n false x.1 x.2, where n is the
                      plan's number of the message in which the array lies that the matrix's label
                      names, at the OWNER's link, and x is the layout's place of (r, c) in that
                      array
  `reads_of_owners`   so an equation on these entries of the witness's messages, at every matrix of
                      the segment, gives the same equation on what the segment reads

By. `Meaning.seat_of_laidThere` (Johnson/Goal/Meaning/HidSeatsOf.lean): the seat is that number, row
and place · `readAt_msg` (Johnson/Desc/Kinds/Law/WitRead.lean): off the pads a segment reads the
witness's own message · `Meaning.seat_inside_members` (Johnson/Goal/Meaning/LaidInsideSeats.lean):
the seats lie off the pads of every member with that number · of the head: the plan's tests laid and
named, and that each tenant of a group is a member's seat (`P5J.At.PlanOk`,
Johnson/P5J/PlanOk.lean).

What stays a hypothesis, all on public data. h: the library's head. hl: l is below 25. hC, hS, hL:
the programs' three tests on the codes, the request's shape and the layout. tie:
`Meaning.ShapesTied`: a member that sits in a segment's group under the number of a message in which
an array lies has that message's key of shape. None of the four is shown here.

Limits. An equation between two readings of one witness. It says nothing on what the witness holds.
A matrix that a segment borrows is read at its owner's message: the second lemma's hypothesis speaks
of that message. Nothing at a pad's place or at a mask row. The full size alone. It imports files
under Johnson/Goal/Meaning/ straight, and takes what lies beneath them. One instance is taken away,
as in the files beneath (no default table of scales). This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.P1K8R.SmallJoin
import Johnson.Goal.Meaning.LaidInsideSeats
import Johnson.Desc.Kinds.Law.WitRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes.Maker (WholeD)
open OnBytes.Params (ReqArray)
open VerifiableInference.Desc (Chain Wit arrayOf laidAt)
open VerifiableInference.Desc.Sound (MsgT readAt readAt_of_named)
open VerifiableInference.Desc.Kinds.Head.Law.Sym (readAt_msg)
open Meaning (labAt ownerK ownerA nameOf sizesOf ShapesTied seat_of_laidThere seat_inside_members)
open P5J (AtMgA CellsM TS)
open P1K8T (seatC)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **What a segment reads at a matrix's seat is the witness's message of the owner's number.** -/
theorem read_is_msg (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    (hC : (P5J.At.cs Zp).lengthsOk = true) (hS : OnBytes.reqShapeOk (P5J.At.shape Zp) = true)
    (hL : OnBytes.reqLayoutOk (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) = true)
    (tie : ShapesTied (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
      (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) fun k => (P5J.At.N Zp cF).group k)
    (w : Wit (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (μ : Fin (sizesOf (P5J.At.X Zp) l).NM) {r c : ℕ}
    (hr : r < Alg.symRows ((sizesOf (P5J.At.X Zp) l).m μ))
    (hc : c < (sizesOf (P5J.At.X Zp) l).k μ) :
    ∃ A x, arrayOf (P5J.At.layout Zp) (ownerK (labAt (P5J.At.X Zp) l μ.val))
        (nameOf (ownerA (labAt (P5J.At.X Zp) l μ.val))) = some A ∧
      A.sizeI = Alg.symRows ((sizesOf (P5J.At.X Zp) l).m μ) ∧
      A.sizeC = (sizesOf (P5J.At.X Zp) l).k μ ∧ laidAt A r c = some x ∧
      readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l w
          (seatC Zp l μ r c).1 false (seatC Zp l μ r c).2.1 (seatC Zp l μ r c).2.2 =
        w.msg (P5J.At.num Zp (ownerK (labAt (P5J.At.X Zp) l μ.val)) A.message) false x.1 x.2 := by
  obtain ⟨A, x, hA, e1, e2, hx, e⟩ := seat_of_laidThere h.plan.laid (P5J.At.num Zp) hl μ hr hc
  refine ⟨A, x, hA, e1, e2, hx, ?_⟩
  obtain ⟨y, hy, -⟩ := readAt_of_named (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay)
    (P5J.At.N Zp cF) l (seatC Zp l μ r c).1 w (h.plan.hN l μ r c hr hc)
  have hm : y ∈ ((P5J.At.N Zp cF).group l).filter fun x =>
      P5J.At.arr Zp x.1 x.2 == (seatC Zp l μ r c).1 := by
    rw [hy]
    exact List.mem_singleton.2 rfl
  obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hm
  rw [readAt_msg (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l w
    (seatC Zp l μ r c).1 false (seatC Zp l μ r c).2.1 (seatC Zp l μ r c).2.2
    ⟨y, hy1, eq_of_beq hy2⟩ (h.plan.hG l)
    fun z hz hg hn => (seat_inside_members hC hS hL h.plan.laid tie hl μ hr hc hl z hz hg hn).2]
  show w.msg (seatC Zp l μ r c).1 false (seatC Zp l μ r c).2.1 (seatC Zp l μ r c).2.2 = _
  rw [show seatC Zp l μ r c = _ from e]

/-- **An equation on the owners' messages gives the same equation on what the segment reads.** V:
the value that is claimed at (μ, r, c). -/
theorem reads_of_owners (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    (hC : (P5J.At.cs Zp).lengthsOk = true) (hS : OnBytes.reqShapeOk (P5J.At.shape Zp) = true)
    (hL : OnBytes.reqLayoutOk (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) = true)
    (tie : ShapesTied (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
      (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) fun k => (P5J.At.N Zp cF).group k)
    (w : Wit (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) (V : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hown : ∀ (μ : Fin (sizesOf (P5J.At.X Zp) l).NM) (A : ReqArray) (x : ℕ × ℕ) (r c : ℕ),
      arrayOf (P5J.At.layout Zp) (ownerK (labAt (P5J.At.X Zp) l μ.val))
        (nameOf (ownerA (labAt (P5J.At.X Zp) l μ.val))) = some A →
      A.sizeI = Alg.symRows ((sizesOf (P5J.At.X Zp) l).m μ) →
      A.sizeC = (sizesOf (P5J.At.X Zp) l).k μ → r < A.sizeI → c < A.sizeC →
      laidAt A r c = some x →
      w.msg (P5J.At.num Zp (ownerK (labAt (P5J.At.X Zp) l μ.val)) A.message) false x.1 x.2 =
        V μ.val r c) :
    ∀ (μ : Fin (sizesOf (P5J.At.X Zp) l).NM) (r c : ℕ),
      r < Alg.symRows ((sizesOf (P5J.At.X Zp) l).m μ) → c < (sizesOf (P5J.At.X Zp) l).k μ →
      readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l w
          (seatC Zp l μ r c).1 false (seatC Zp l μ r c).2.1 (seatC Zp l μ r c).2.2 =
        V μ.val r c := by
  intro μ r c hr hc
  obtain ⟨A, x, hA, e1, e2, hx, e⟩ := read_is_msg h hl hC hS hL tie w μ hr hc
  exact e.trans (hown μ A x r c hA e1 e2 (e1 ▸ hr) (e2 ▸ hc) hx)

end ProofFile.Honest.K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K8.read_is_msg
#print axioms ProofFile.Honest.K8.reads_of_owners
