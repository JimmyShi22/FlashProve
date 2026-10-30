-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/CellOkAtWrap.lean: THE SMALLNESS TEST: THE DICTIONARY ON THE DIGITS' CELLS
(`CellOkR`, Johnson/Top/H/Keep/DigitsCell.lean) AT EVERY STATE WITHOUT A MARK THAT THE FIRST CHAIN's
BLOCKS, EACH WITH THE TEST ON WORDS IN FRONT, REACH IN FRONT OF A SEGMENT's BATCHING: UNDER THE
LIBRARY's HEAD ALONE, AT ALL 25. The library has the sentence at the states of the verifier's side's
frame that are on the table and reached (`P5J.AtMgA.left_cells_at`,
Johnson/P5J/K09LeftCellsAll.lean). Here the table's promise is not asked. It stands over the library
alone. One theorem and one lemma; none of the library's goals.

  `book_at_wrap`   the book-keeping's test `bookAt` at the head's numbers, at every state that the
                   blocks' own steps reach: `IM.book_reached_planOk` (Johnson/IMR/BookPaidR.lean)
                   at the numbers in front of what is told, with `P5J.N₀_told` and `placesW_at`
                   (Johnson/P5J/FoldJ3.lean)
  **`cellOkR_at_wrap`**   the head · m < 25 · what `digAt` returns at m · a state reached so in
                   front of the batching, without a mark · its part pa ⊢ CellOkR at the data's list
                   of what is sent, radii and seats, at own := h.𝔇.N.group m
HOW. `AtMgA.left_cells`' own proof (Johnson/P5J/K09LeftCells.lean) draws four things out of "on the
table and reached": no mark: a premise here · the facts on reached states: `P5J.foldFacts_at_head'`
(Johnson/P5J/FoldJ3Whole.lean) at that reach, its three tests on public data by `laid_at_head`,
`startB_at_head`, `sendsB_of_madeRow` at `madeRow_at_head` · the reach by the blocks' own steps:
`reach_raw` · `bookAt`: the lemma above. The tests on public data by the names by which
`left_cells_at` calls them. Then `cellOkR_of_facts`.
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
TACTICS THAT SEARCH: none.
Limits. THE LIBRARY's HEAD IS A PREMISE. That any such state is reached is not said. The full size
and the format's second hash function alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.P5J.K09LeftCellsAll
import Johnson.P5J.FoldJ3Whole
import Johnson.P5J.ReadsTestsAtHead
import Johnson.P5J.StartAtHead
import Johnson.P5J.AtMgRAtHead
import Johnson.IMR.BookPaidR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Maker (WholeD)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (digList)
open VerifiableInference.Desc.LinkJoin (batchAt laidPub_of_B cellOkR_of_facts cell_front part_reads)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw RchAt)
open P5J (AtMgA TS F0T fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

/-- The book-keeping's test at the head's numbers, at every state that the blocks' own steps
reach. -/
theorem book_at_wrap (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {z : ProofFile.InstPub} {s : S} {k : ℕ}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (z, s)) :
    bookAt (P5J.At.N Zp cF) P5J.At.ps[k]? s = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := IM.book_reached_planOk h.scope h.reads O (P5J.At.N₀ Zp cF) h.laid.planOk z k s hr
  rw [P5J.N₀_told, P5J.placesW_at] at e
  exact e

/-- **THE DICTIONARY ON THE DIGITS' CELLS, WITHOUT THE TABLE's PROMISE.** -/
theorem cellOkR_at_wrap (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) m = some (xx, tlD)) {z : ProofFile.InstPub} {s : S}
    (hw : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m) (z, s))
    (hu : s.failed = none) {pa : K9.Part} (hpa : Desc.K9.atS.get? s = some pa) :
    CellOkR xx tlD h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xx.link true j.1)
      (h.𝔇.N.group m) pa := by
  obtain ⟨p, hp, hpl⟩ := P5J.batch_place hm
  have el : xx.link = m := IM.lookAt_link (P5J.look_of_dig hd)
  obtain ⟨hB, hZ⟩ := h.toAtMg.hBZ_cells hm hd el h.𝔇.l3.rad
  have hL0 := P5J.laid_at_head h.toAtMg
  have F := P5J.foldFacts_at_head' h.toAtMg
    (fun k (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) × Unit) =>
      RchAt (F0T OnBytes.secondHashFunction Zp Np cF) k a) (fun _ _ ha => ha) hL0
    (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  obtain ⟨set, pp, H⟩ := h.left_dig hm hd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, Xl, _, e3, _⟩ := TocK8.k08_scope h.scope h.reads O m hm
  have hrch : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) (batchAt fullLinks P5J.At.ps m) ((z, s), ()) := hw
  have hraw : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m) (z, s) := reach_raw hw
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * m + IM.nAt m + 2) (z, s) := by
    rw [← LPFK9.batch_nAt m hm]
    exact hraw
  obtain ⟨c1, c2, c3, -⟩ := cell_front h.scope h.reads O hm e3 (h.left_moments m) hr hpa
  have hL := (part_reads s pa hpa).1
  obtain ⟨-, hown, -, -⟩ := F.frameIs _ ((z, s), ()) p m pa.L hrch hu hp hpl hL
  have hbook := book_at_wrap h hraw
  rw [hp] at hbook
  refine cellOkR_of_facts xx tlD h.𝔇.sent h.𝔇.l3.rad _ _ hpa (by rw [el]; exact c1) c2
    (by rw [el]; exact c3) (F.codes _ _ hrch hu) hown hbook (F.seatsCarried _ _ hrch hu)
    (F.msgShapes _ _ hrch hu) (h.toAtMg.hT1_cells hL0 hm el hp h.𝔇.l3.rad)
    (h.toAtMg.hT2_cells _ hm el hp h.𝔇.l3.rad) (fun ad had => ?_) (fun ad s had hs => ?_)
    (laidPub_of_B _ _ _ _ hB hZ)
  · obtain ⟨s, hs, -⟩ := P5J.cells_have_seats H ad had
    rw [hs]
    rfl
  · obtain ⟨s', hs', hf⟩ := P5J.cells_have_seats H ad had
    obtain rfl : s' = s := Option.some.inj (hs'.symm.trans hs)
    exact hf

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.book_at_wrap
#print axioms VerifiableInference.Desc.First.K8.Honest.cellOkR_at_wrap
