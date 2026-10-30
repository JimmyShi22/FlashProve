-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ReadsOfOwnersAtHead.lean: the honest side of the smallness test
(K8): THE FOUR PUBLIC HYPOTHESES OF ReadsOfOwners.lean OF THIS FOLDER, PAID UNDER THE LIBRARY's
HEAD: the programs' three tests on the codes, the request's shape and the layout, and the tie of the
members' shapes (`Meaning.ShapesTied`, Johnson/Goal/Meaning/LaidInsideSeats.lean) at the first
table's own members. So its two lemmas hold under the head alone. PUBLIC DATA ALONE. No definition.
Lemmas: joins of the library's own; none of the library's goals.

  `shapesTied_carry`        general: the tie reads of a member its shape and its seat: it passes
                            between two lists of members with one list of such pairs
  `shapesTied_at_head`      the tie, at the head's letters and the first table's own members
  `read_is_msg_at_head`, `reads_of_owners_at_head`   the two lemmas, under h and l < 25 alone

By, all of other authors, under Johnson/Road/K4/: `written_of_head` (K4HeadWritten.lean): under the
head five parts of the public parameters are the written values · `programs_at` (K4PlanTied.lean):
there the programs' three tests accept · `shapesTied_at` (K4PlanPaid.lean): there the test with code
for the tie accepts, at the members by the make at the radii 0; its closed fact is an evaluation in
Lean's kernel (`shapesTied_written`, K4PlanWrittenShapes.lean) · `shapesTied_of_table`
(K4PlanAt.lean): the test's yes gives the tie · `num_fast`, `arr_fast` (K4PlanFast.lean): the test's
two look-ups are the plan's numberings · `SamePairs`, `mem_pairs`, `samePairs_R` (K4PlanCarry.lean):
the members by the make have the same shapes and seats at every family of radii. That file carries
four other conditions between such lists; the tie is not among them.

Limits. Those of ReadsOfOwners.lean. It takes a cone of files under Johnson/Road/K4/ and
Johnson/Goal/Meaning/. One instance is taken away, as in the files beneath (no default table of
scales). The full size; the format's second hash function. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K8.ReadsOfOwners
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K4PlanPaid
import Johnson.Road.K4.K4PlanFast
import Johnson.Road.K4.K4PlanCarry

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes.Maker (WholeD)
open OnBytes.Params (ReqArray ReqLayout ReqShape)
open VerifiableInference.Desc (Chain Wit arrayOf laidAt)
open VerifiableInference.Desc.Sound (MsgT Mem readAt seatOf)
open OnBytes.Road.K4 (SamePairs mem_pairs samePairs_R shapesTied_of_table shapesTied_at
  written_of_head programs_at num_fast arr_fast numbersAt)
open Meaning (labAt ownerK ownerA nameOf sizesOf ShapesTied)
open P5J (AtMgA CellsM TS)
open P1K8T (seatC)

/-- **The tie passes between two lists of members with one list of pairs (shape, seat).** -/
theorem shapesTied_carry {codes : OnBytes.Codes} {shape : ReqShape} {layout : ReqLayout}
    {num arr : ℕ → ℕ → ℕ} {ms ms' : List Mem} {grp : ℕ → List (ℕ × ℕ)} (hp : SamePairs ms ms')
    (T : ShapesTied codes shape layout num arr ms grp) :
    ShapesTied codes shape layout num arr ms' grp := by
  intro l as A m hl hA hm k hk y hy hg hn
  obtain ⟨y', hy', e⟩ := mem_pairs hp hy
  have e' : ((y'.1.l.get y'.2).1, seatOf y') = ((y.1.l.get y.2).1, seatOf y) := e
  obtain ⟨e1, e2⟩ := Prod.mk.inj e'
  rw [← e1]
  refine T l as A m hl hA hm k hk y' hy' (e2 ▸ hg) ?_
  show arr (seatOf y').1 (seatOf y').2 = _
  rw [e2]
  exact hn

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The tie of the members' shapes, under the head.** -/
theorem shapesTied_at_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) :
    ShapesTied (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
      (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) fun k => (P5J.At.N Zp cF).group k := by
  have T0 := shapesTied_of_table (N := numbersAt Zp) _ rfl
    (shapesTied_at (written_of_head h.toAtMg))
  rw [num_fast, arr_fast] at T0
  exact shapesTied_carry (samePairs_R _ _ _ _) T0

/-- **What a segment reads at a matrix's seat is the witness's message of the owner's number**,
under the head alone. -/
theorem read_is_msg_at_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) {l : ℕ} (hl : l < 25)
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
        w.msg (P5J.At.num Zp (ownerK (labAt (P5J.At.X Zp) l μ.val)) A.message) false x.1 x.2 :=
  read_is_msg h hl (programs_at (written_of_head h.toAtMg)).1
    (programs_at (written_of_head h.toAtMg)).2.1 (programs_at (written_of_head h.toAtMg)).2.2
    (shapesTied_at_head h) w μ hr hc

/-- **An equation on the owners' messages gives the same equation on what the segment reads**, under
the head alone. V: the value that is claimed at (μ, r, c). -/
theorem reads_of_owners_at_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) {l : ℕ}
    (hl : l < 25) (w : Wit (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (V : ℕ → ℕ → ℕ → Cb.Gl.E)
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
        V μ.val r c :=
  reads_of_owners h hl (programs_at (written_of_head h.toAtMg)).1
    (programs_at (written_of_head h.toAtMg)).2.1 (programs_at (written_of_head h.toAtMg)).2.2
    (shapesTied_at_head h) w V hown

end ProofFile.Honest.K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K8.shapesTied_carry
#print axioms ProofFile.Honest.K8.shapesTied_at_head
#print axioms ProofFile.Honest.K8.read_is_msg_at_head
#print axioms ProofFile.Honest.K8.reads_of_owners_at_head
