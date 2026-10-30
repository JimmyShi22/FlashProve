-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/WAtHead.lean: the kind K1's sending of W (number 356 of the
first chain's flat list), under the library's head: if the table's six tests hold at the state in
front, they hold at border 357 behind an accepting step. The one further premise is: no mark at the
state in front. Beside the step no premise speaks of the state behind.

What this file proves. Let h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x (the library's head,
Johnson/P5J/MgAtAll.lean), blk whatever stands at number 356 in the first chain's flat list, and s,
s' the states in front of and behind an accepting step of blk (IM.Yes).
  - xk_W_head: the six tests IM.XK (Johnson/IMR/HandsDef.lean) at the numbers P5J.At.N Zp cF, the
    written lists IM.linksW and IM.placesW and the further test EW h.𝔇.pubD base z
    (Johnson/LPFK9R/SharesAtE.lean: every public item that is open or tied at the border passes
    pubAll) go from border 356 at s to border 357 at s'. Its premises: what stands at the number
    (hb), the step (hy), no mark at s (h0), the six in front (hx). base and z are free.
  - hands_W_head: all that a sub-protocol owes to the table (IM.Hands, all six fields, at every pair
    of states) for blk at number 356, at the head's numbers, the written list linksFull and that
    further test.
  - pub_W_head: the further test alone, behind a yes of the decision of the bare sub-protocol atM4
    (whereOf Zp) (sendAtS (parWZ Zp wMsgFull)), from the further test and the test on the book in
    front. hands_W_head ties that sub-protocol to blk.
  - rowM4_head: what is asked of the table at number 356 (RowM4,
    Johnson/Desc/K13/Law/AtTableW.lean) holds at the head's numbers, at moreAll and the written
    lists.
  - mark_W_head: there is no mark behind an accepting step of blk.
  - Three facts on the written lists, by evaluation in Lean's kernel, with no premise. rowM4_all:
    the test rowM4B says yes at number 356. rowM4_all_fails: it says no at number 355: so the test
    can fail. open_356: one public item is open at border 356: frontOk.
rowM4_head and pub_W_head take an opening O (IM.Open; the head gives one: LaidAt.opened) as a
premise. No thread, no prover and no proof file's bytes occur. No definition. Statements and proofs.

How it fits. Every public item that is open or tied at border 357 is one of five (the fields pubs
and tied of the table's row, with open_356). frontOk and evalLaid: the decision lays them, from
frontOk in front (atM4_laid). The item "K13.wSits": atM4_sits and atM4_seat, with the book's two
equations in front and the plan's two tests (W_sits_atAll). indexIs and indexThere: they stood in
front and stay (atM4_index). The row's field pubs has a fourth arm, whatever else was open in front:
by open_356 that is frontOk again, so pub_W_head rests on open_356, and nothing is owed for an item
that rides past the sub-protocol. pubAll answers each of the five by a test with code: by equations
that hold by unfolding (Johnson/Desc/First/PubAllAt.lean, Johnson/Desc/K13/Law/FillK13Laws.lean).

Another way, and why it is not taken: hands_M4_e (Johnson/Desc/AtSeats/HandsAtE.lean) at the
library's closed meaning, with its premise FillM4 from fillM4_paid6
(Johnson/Desc/K13/Law/FillM4Paid6.lean). That lemma asks that four named items are open in front;
by open_356 frontOk alone is open there, and it is none of the four. And that way would give the
statement at one base alone.

Proof that this file follows: the last field of hands_M4_e in pub_W_head, with FillM4's clauses
replaced by pubAll's equations. The frame and the string that atM4_laid and frontOkB_iff take are
idle there: the proof lays a frame without trees and strOf's string
(Johnson/Desc/K14/Law/Border0.lean).

Lemmas used beside these: rowM4_of_test (Johnson/Desc/K13/Law/AtTableW.lean); W_hNt_atAll,
W_hNm_atAll, W_hm_atAll, W_sits_atAll (Johnson/Desc/K1/Law/TiesAtAll.lean) at pin1_atAll,
pin2_atAll (Johnson/Desc/K1/Law/PinsAtHead.lean); frontOkB_iff, evalLaidB_iff
(Johnson/Desc/K13/Law/Bools.lean), atM4_laid, StepM4.decide (Johnson/Desc/K13/Law/AtRecord.lean),
atM4_sits, planSitsB_iff (Johnson/Desc/K13/Law/SitsMade.lean), atM4_seat, PlanSits.pos
(Johnson/Desc/K13/Law/SeatMade.lean), atM4_index (Johnson/Desc/K13/Law/IndexKept.lean), tied_of_pin
(Johnson/Desc/AtSeats/HandsMore.lean); at_356 (Johnson/IMR/LastFour.lean); k13_sits_flat
(Johnson/Desc/AtSeats/K13SitsJoin.lean), hands_M4 (Johnson/Desc/AtSeats/HandsAtThree.lean),
Hands.under, xk_parts (Johnson/IMR/HandsDef.lean), Hands.step (Johnson/IMR/HandsFold.lean);
linksW_full, placesW_full (Johnson/IMR/K8Owed.lean); head_N_is
(Johnson/Desc/ProofFile/Honest/K1/Law/FiftyAtHead.lean); the opening from the head (LaidAt.opened,
Johnson/P5J/LaidOpens.lean).

Limits, the weightiest first.
  1. This file shows no value of the head h, and no state at which the premises of xk_W_head hold.
    That blk accepts anywhere is not shown here.
  2. At the further test EW, which has no "in order". At P1K2.EQ (Johnson/P1K2R/TieTwo.lean) "in
    order" at the state behind is wanted beside it; this file does not prove that.
  3. The samples' test at border 357, and the meaning's field pubP at the public items that are open
    there, are not touched here.
  4. At the full size's written lists and under IM.Open at the earlier hash OnBytes.secondHashFunction alone.
  5. The three closed facts are evaluations in Lean's kernel (decide +kernel) over the written
    lists: a row more in the table reopens them; for them the recursion depth is raised in this file
    (maxRecDepth 1000000, as in Johnson/Desc/AtSeats/DoorAt9WG.lean).
  6. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FiftyAtHead
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K13.Law.AtTableW
import Johnson.Desc.K13.Law.FillK13Laws
import Johnson.Desc.K13.Law.IndexKept
import Johnson.Desc.K13.Law.SeatMade
import Johnson.Desc.K13.Law.SitsMade
import Johnson.Desc.K14.Law.Border0
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.EPubAt
import Johnson.Desc.AtSeats.HandsMore
import Johnson.Desc.AtSeats.K13SitsJoin
import Johnson.IMR.LastFour
import Johnson.IMR.HandsFold
import Johnson.LPFK9R.SharesAtE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf pubAll ePubAt)
open VerifiableInference.Desc.Sound (linksFull moreAll)
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.Desc.K13.Law (openAt rowM4B RowM4 rowM4_of_test wMsgFull wSitsItem StepM4)
open VerifiableInference.Desc.K1 (parWZ layOf sendAtS)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-! ## 1 Three facts on the written lists -/

/-- At number 356 the test says yes. -/
theorem rowM4_all : rowM4B moreAll linksFull (flatPlacesOf linksFull true) 356 = true := by
  decide +kernel

/-- **The test can fail**: at number 355. -/
theorem rowM4_all_fails : rowM4B moreAll linksFull (flatPlacesOf linksFull true) 355 = false := by
  decide +kernel

/-- **The one public item that is open at border 356.** -/
theorem open_356 : (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[356]?.getD [] =
    [.frontOk] := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-! ## 2 Under the head -/

/-- **What is asked of the table at number 356**, at the head's numbers, at moreAll and the written
lists. -/
theorem rowM4_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    RowM4 h.𝔇.N moreAll linksFull (flatPlacesOf linksFull true) 356
      (layOf (parWZ Zp wMsgFull)).shapes.size (parWZ Zp wMsgFull).sent.size :=
  rowM4_of_test moreAll linksFull (flatPlacesOf linksFull true) 356 _ _ rowM4_all h.𝔇.N
    (K1.W_hNt_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h))
    (K1.W_hNm_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h))

/-- **The further test behind a yes of the bare sub-protocol's decision**: from the further test and
the test on the book in front. -/
theorem pub_W_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (base : First.Pub → ProofFile.InstPub × S → Bool) (z : ProofFile.InstPub) {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (atM4 (Cl := ProofFile.Cl) (whereOf Zp) (sendAtS (parWZ Zp wMsgFull))).decide s [r₁, r₂] gs =
      .ok s')
    (hbk : First.bookAt h.𝔇.N (flatPlacesOf linksFull true)[356]? s = true)
    (hF : ePubAt (pubAll h.𝔇.pubD base) moreAll linksFull (flatPlacesOf linksFull true) 356
      (z, s) = true) :
    ePubAt (pubAll h.𝔇.pubD base) moreAll linksFull (flatPlacesOf linksFull true) (356 + 1)
      (z, s') = true := by
  have hT := rowM4_head h O
  have hA := List.all_eq_true.1 hF
  have y₀ : (⟨0, [], id, 0⟩ : Sound.Frame).E.Str :=
    _root_.Desc.K14.Law.strOf ⟨0, [], id, 0⟩ fun _ => []
  have f0 : K13.Law.frontOkB (whereOf Zp) s = true :=
    hA .frontOk (List.mem_append_left _ hT.frontIn)
  have hon := (K13.Law.frontOkB_iff (whereOf Zp) s y₀).1 f0
  obtain ⟨hE, hFr⟩ := K13.Law.atM4_laid hd y₀ y₀ hon
  have fOk : pubAll h.𝔇.pubD base .frontOk (z, s') = true :=
    (K13.Law.frontOkB_iff (whereOf Zp) s' y₀).2 hFr
  refine List.all_eq_true.2 fun q hq => ?_
  rcases List.mem_append.1 hq with hq | hq
  · rcases hT.pubs q hq with rfl | rfl | rfl | hq'
    · exact fOk
    · exact (K13.Law.evalLaidB_iff (whereOf Zp) s').2 hE
    · have hbk' := hbk
      unfold First.bookAt at hbk'
      simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
      obtain ⟨⟨b1, b2⟩, _⟩ := hbk'
      obtain ⟨p1, p2⟩ := K1.W_sits_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)
      have hp1 := (K13.Law.planSitsB_iff (whereOf Zp) (parWZ Zp wMsgFull)).1 p1
      have hp2 : h.𝔇.N.w = _ := eq_of_beq p2
      have hs := K13.Law.atM4_seat hd b2 hp1.pos
      rw [b1, ← hp2] at hs
      show pubAll h.𝔇.pubD base (.more none "K13.wSits") (z, s') = true
      rw [First.pubAll_more_wSits, K13.Law.wSitsC_eq, K13.Law.wSeatC_eq, Bool.and_eq_true]
      exact ⟨K13.Law.atM4_sits hd y₀ hon hp1, hs⟩
    · rw [open_356] at hq'
      obtain rfl : q = .frontOk := List.mem_singleton.1 hq'
      exact fOk
  · rcases hT.tied q hq with rfl | rfl
    · exact (K13.Law.atM4_index hd).1 _
        (hA .indexIs (List.mem_append_right _ (HashBuild.tied_of_pin hT.pinIn _ (Or.inl rfl))))
    · exact (K13.Law.atM4_index hd).2.1
        (hA .indexThere (List.mem_append_right _ (HashBuild.tied_of_pin hT.pinIn _ (Or.inr rfl))))

/-- No mark behind an accepting step of what stands at number 356. -/
theorem mark_W_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[356]? = some blk) (ft : ℕ) {s s' : S} (hy : IM.Yes ft blk s s') :
    s'.failed = none := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨rs, cols, n, e⟩ := hy
  obtain ⟨-, -, -, h1, -⟩ := IM.at_356 h.scope h.reads O hb e
  exact h1

/-- **All that what stands at number 356 owes to the table**, at the head's numbers, the written
lists and the further test on the public items. -/
theorem hands_W_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[356]? = some blk) (base : First.Pub → ProofFile.InstPub × S → Bool) (z : ProofFile.InstPub)
    (ft : ℕ) :
    IM.Hands h.𝔇.N linksFull (flatPlacesOf linksFull true)
      (fun k t => ePubAt (pubAll h.𝔇.pubD base) moreAll linksFull (flatPlacesOf linksFull true) k
        (z, t)) ft 356 blk := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, e, msg, he, -, hm, hu⟩ := K13.Law.k13_sits_flat h.scope h.reads O
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  obtain rfl : msg = wMsgFull := Option.some.inj
    (hm.symm.trans (K1.W_hm_atAll h O (K1.pin1_atAll h)))
  refine IM.Hands.under hu (HashBuild.hands_M4 h.𝔇.N moreAll linksFull
    (flatPlacesOf linksFull true) _ ft 356 (whereOf Zp) (parWZ Zp wMsgFull) (rowM4_head h O)
    fun s s' hy _ _ hx => ?_)
  obtain ⟨rs, cols, n, e'⟩ := hy
  obtain ⟨r₁, r₂, gs, hd⟩ := StepM4.decide (Pp := Unit) (x := ((), s)) (x' := ((), s'))
    ⟨rfl, ft, rs, cols, n, e'⟩
  exact pub_W_head h O base z hd (IM.xk_parts hx).2.2.2.1 (IM.xk_parts hx).2.2.2.2

/-- **The six tests at border 357, behind an accepting step of what stands at number 356**, under
the head: from the six in front and no mark there. Beside the step no premise speaks of the state
behind. -/
theorem xk_W_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[356]? = some blk) (base : First.Pub → ProofFile.InstPub × S → Bool) (z : ProofFile.InstPub)
    (ft : ℕ) {s s' : S} (hy : IM.Yes ft blk s s') (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (LPFK9.HandsAt.EW h.𝔇.pubD base z) 356 s =
      true) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (LPFK9.HandsAt.EW h.𝔇.pubD base z) (356 + 1) s' =
      true := by
  have eE : LPFK9.HandsAt.EW h.𝔇.pubD base z = fun k t =>
      ePubAt (pubAll h.𝔇.pubD base) moreAll linksFull (flatPlacesOf linksFull true) k (z, t) := by
    funext k t
    unfold LPFK9.HandsAt.EW
    rw [IM.placesW_full, IM.linksW_full]
  rw [IM.placesW_full, IM.linksW_full, ← head_N_is h, eE] at hx ⊢
  exact (hands_W_head h hb base z ft).step hy h0 (mark_W_head h hb ft hy) hx

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.rowM4_all
#print axioms ProofFile.Honest.K1.rowM4_all_fails
#print axioms ProofFile.Honest.K1.open_356
#print axioms ProofFile.Honest.K1.rowM4_head
#print axioms ProofFile.Honest.K1.pub_W_head
#print axioms ProofFile.Honest.K1.mark_W_head
#print axioms ProofFile.Honest.K1.hands_W_head
#print axioms ProofFile.Honest.K1.xk_W_head
