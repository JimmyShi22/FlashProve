-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/OpeningAtHead.lean: the kind K1's opening (number 2 of the
first chain's flat list), under the library's head: if the table's six tests hold at the state in
front, they hold at border 3 behind an accepting step, under further premises at the state in front
(no mark; that the state is reached), two equations on the meaning, and one premise at the state
behind: the further test there (h6). Beside the step and h6 no premise speaks of the state behind.

What this file proves. Let h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x (the library's head,
Johnson/P5J/MgAtAll.lean), blk whatever stands at number 2 in the first chain's flat list, and s, s'
the states in front of and behind an accepting step of blk (IM.Yes).
  - xk_opening_head: the six tests IM.XK (Johnson/IMR/HandsDef.lean) at the numbers P5J.At.N Zp cF,
    the written lists IM.linksW and IM.placesW and the further test P1K2.EQ Mg IM.linksW IM.placesW
    z (Johnson/P1K2R/TieTwo.lean) go from border 2 at s to border 3 at s'. Its premises beside the
    step and the six in front: no mark at s (h0); s is reached at number 2 of the flat list
    (hreach); the meaning's extra rows are moreAll (hm) and its public tests are pubAll h.𝔇.pubD
    base (hpub); the further test at border 3 at s' (h6).
  - rowG_head: what is asked of the table at number 2 (RowG, Johnson/Desc/K13/Law/AtTableFirst.lean)
    holds at the head's numbers, at moreAll and the written lists, with all seven public items that
    are open at border 3 (open_three, Johnson/Desc/ProofFile/Honest/K1/Law/FormBehindSix.lean) in
    the place of mk.
  - frame_two_head: at a state that is reached at number 2 the checked frame has the files' shape
    and stands at link 0.
  - own_two_head: at such a state the test on the first sending's own seats (ownSeatsB) holds, if
    the test on the book holds there.
  - mark_opening_head: there is no mark behind an accepting step of blk.
  - Three facts on the written lists, by evaluation in Lean's kernel, with no premise. rowG_all: the
    test rowGB says yes at number 2 with the seven. rowG_all_fails, rowG_all_lacks: it says no at
    number 3, and at number 2 with the empty list: so the test can fail, in its number and in its
    clause on mk.
rowG_head and own_two_head take an opening O (IM.Open; the head gives one: LaidAt.opened) as a
premise, and speak of the first sending's parameters at O's ground: firstPar Bs.G₀.first (gpOf Zp).
No thread, no prover and no proof file's bytes occur. No definition. Statements and proofs.

How it fits. xk_opening_six (Johnson/Desc/ProofFile/Honest/K1/Law/FormBehindSix.lean) has the same
end, from seven more premises: the table's row (hT), the groups' count (hgroups), the own seats'
test (hown), no mark behind (h1), and three on how the sub-protocol is built (hL, hp, hj). Here none
of the seven is asked. Four are proved: the row (with hm), the groups' count (with hpub), the own
seats' test (with hreach) and no mark behind. The three on how the sub-protocol is built are not
needed: first_under gives at once what joined_under gave from them. h6 stays: six_of_nine (the same
file) brings it down to "in order" and nine public tests at the state behind.

Proofs that this file follows: xk_opening_six in xk_opening_head, with first_under
(Johnson/IMR/FirstUnder.lean) in the place of joined_under; hown_plusG
(Johnson/Desc/AtSeats/MoreAtOpening.lean) in own_two_head, whose "in order" at another meaning gave
the frame's shape and link: here frame_two_head gives them.

Lemmas used beside these: rowG_of_test (Johnson/Desc/K13/Law/AtTableFirst.lean); G_hNt_atAll,
G_hNm_atAll, G_hownB_atAll (Johnson/Desc/K1/Law/TiesAtAll.lean) at pin1_atAll, pin2_atAll
(Johnson/Desc/K1/Law/PinsAtHead.lean); recAll_reached (Johnson/IMR/AtReach.lean), front_len
(Johnson/IMR/RootsWhole.lean), laid_at (Johnson/IMR/FrontPin.lean); atMoment_zero
(Johnson/Desc/AtSeats/FrontG.lean); flat_cases (Johnson/IMR/FlatCases.lean), case_noMark
(Johnson/IMR/MemberPath.lean); groups_of_sentence (Johnson/Desc/K13/Law/FillGFromSentences.lean),
pubAll_noneSent (Johnson/Desc/First/PubAllAt.lean); handsPt_G_four, xk_of_four
(Johnson/Desc/ProofFile/Honest/K1/Law/FormBehindSix.lean), epub_eq
(Johnson/Desc/ProofFile/Honest/K1/Law/FormBehind.lean); yes_decides
(Johnson/Desc/AtSeats/HandsAtThree.lean); linksW_full, placesW_full (Johnson/IMR/K8Owed.lean);
head_N_is (Johnson/Desc/ProofFile/Honest/K1/Law/FiftyAtHead.lean); the opening from the head
(LaidAt.opened, Johnson/P5J/LaidOpens.lean).

Limits, the weightiest first.
  1. This file shows no value of the head h, and no state at which the premises of xk_opening_head
    hold. That blk accepts anywhere is not shown here.
  2. h6 is a premise at the state behind the step. This file does not prove it.
  3. Under hreach s is the first state ProofFile.startS Zp z (reach_two, Johnson/P1L20R/RoomFold.lean): so
    xk_opening_head speaks of one state in front for each z.
  4. hm and hpub are premises on the meaning Mg. This file shows no meaning that meets them.
  5. At the further test P1K2.EQ, which holds "in order". The form at EW
    (Johnson/LPFK9R/SharesAtE.lean) is not stated here.
  6. The samples' test at border 3, and the meaning's field pubP at the public items that are open
    there, are not touched here. Nothing at number 356.
  7. The three closed facts are evaluations in Lean's kernel (decide +kernel) over the written
    lists: a row more in the table reopens them; for them the recursion depth is raised in this file
    (maxRecDepth 1000000, as in Johnson/Desc/AtSeats/DoorAt9WG.lean).
  8. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormBehindSix
import Johnson.Desc.ProofFile.Honest.K1.Law.FiftyAtHead
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K13.Law.AtTableFirst
import Johnson.Desc.K13.Law.FillGFromSentences
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.AtSeats.FrontG
import Johnson.IMR.FirstUnder
import Johnson.IMR.FlatCases
import Johnson.IMR.MemberPath
import Johnson.IMR.AtReach
import Johnson.IMR.FrontPin
import Johnson.IMR.RootsWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf pubAll)
open VerifiableInference.Desc.Sound (linksFull moreAll)
open VerifiableInference.Desc.K13.Law (openAt rowGB RowG rowG_of_test groups_of_sentence)
open VerifiableInference.Desc.K1
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Desc.K14.Law (seatZ secondAt)

/-! ## 1 Three facts on the written lists -/

/-- At number 2, with the seven public items that are open at border 3: the test says yes. -/
theorem rowG_all : rowGB moreAll linksFull (flatPlacesOf linksFull true) 2
    [.unheard, .ledger 0, .lookIn 0 2, .linkFresh 0, .freeAbove 0,
      .more (some 0) "frame.sentIs", .more (some 0) "ledger.treesAre"] = true := by
  decide +kernel

/-- **The test can fail**: at number 3, with the same seven. -/
theorem rowG_all_fails : rowGB moreAll linksFull (flatPlacesOf linksFull true) 3
    [.unheard, .ledger 0, .lookIn 0 2, .linkFresh 0, .freeAbove 0,
      .more (some 0) "frame.sentIs", .more (some 0) "ledger.treesAre"] = false := by
  decide +kernel

/-- **Its clause on mk can fail**: at number 2, with the empty list. -/
theorem rowG_all_lacks : rowGB moreAll linksFull (flatPlacesOf linksFull true) 2 [] = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-! ## 2 Under the head -/

/-- **What is asked of the table at number 2**, at the head's numbers, at moreAll and the written
lists, with the seven. -/
theorem rowG_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    RowG h.𝔇.N moreAll linksFull (flatPlacesOf linksFull true) 2
      (layOf (firstPar Bs.G₀.first (gpOf Zp))).shapes.size
      (firstPar Bs.G₀.first (gpOf Zp)).sent.size
      [.unheard, .ledger 0, .lookIn 0 2, .linkFresh 0, .freeAbove 0,
      .more (some 0) "frame.sentIs", .more (some 0) "ledger.treesAre"] :=
  rowG_of_test moreAll linksFull (flatPlacesOf linksFull true) 2 _ _ _ rowG_all h.𝔇.N
    (K1.G_hNt_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h))
    (K1.G_hNm_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h))

/-- At a state that is reached at number 2 the checked frame has the files' shape and stands at link
0. -/
theorem frame_two_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {z : ProofFile.InstPub} {s : S}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 2 (z, s)) :
    s.check.frame.shape = Zp.first.shape ∧ s.check.frame.link = 0 := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := hreach.fold
  exact ⟨(Meaning.K2.recAll_reached h.scope h.reads O hreach (le_refl 2)
      (by rw [Meaning.Carry.front_len h.scope h.reads O]; decide)).walk.shape,
    (Meaning.K2.laid_at h.scope h.reads O (l := 0) (by decide) f).2⟩

/-- **The test on the first sending's own seats** at a state that is reached at number 2, from the
test on the book there. -/
theorem own_two_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {z : ProofFile.InstPub} {s : S}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 2 (z, s))
    (hbk : First.bookAt h.𝔇.N (flatPlacesOf linksFull true)[2]? s = true) :
    ownSeatsB h.𝔇.N (openAt linksFull (flatPlacesOf linksFull true) (2 + 1))
      (firstPar Bs.G₀.first (gpOf Zp)) (s.check.frame.atMoment 0).length s.book.trees.size =
      true := by
  obtain ⟨hsh, hl⟩ := frame_two_head h hreach
  have ht : s.book.trees.size = h.𝔇.N.treesAt (flatPlacesOf linksFull true)[2]? := by
    unfold First.bookAt at hbk
    rw [Bool.and_eq_true, Bool.and_eq_true] at hbk
    exact eq_of_beq hbk.1.1
  rw [HashBuild.atMoment_zero _ h.𝔇.shape hsh hl, ht]
  exact K1.G_hownB_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)

/-- No mark behind an accepting step of what stands at number 2. -/
theorem mark_opening_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[2]? = some blk) (ft : ℕ) {s s' : S} (hy : IM.Yes ft blk s s') :
    s'.failed = none := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨rs, gs, hd⟩ := HashBuild.yes_decides hy
  rcases IM.case_noMark (IM.flat_cases h.scope h.reads O 2 blk hb) hd with h1 | ⟨h1, -⟩ |
    ⟨l, -, h1⟩
  · exact h1
  · cases h1
  · omega

/-- **The six tests at border 3, behind an accepting step of what stands at number 2**, under the
head: from the six in front, no mark there, that the state in front is reached, the two equations hm
and hpub on the meaning, and the further test at the state behind (h6). Beside the step and h6 no
premise speaks of the state behind. -/
theorem xk_opening_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[2]? = some blk) {W : Type} (Mg : Meaning ProofFile.InstPub W) (hm : Mg.more = moreAll)
    (base : First.Pub → ProofFile.InstPub × S → Bool) (hpub : Mg.pub = pubAll h.𝔇.pubD base)
    (z : ProofFile.InstPub) (ft : ℕ) {s s' : S}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 2 (z, s)) (hy : IM.Yes ft blk s s')
    (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (P1K2.EQ Mg IM.linksW IM.placesW z) 2 s =
      true)
    (h6 : P1K2.EQ Mg IM.linksW IM.placesW z (2 + 1) s' = true) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (P1K2.EQ Mg IM.linksW IM.placesW z) (2 + 1) s' =
      true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, nm, X, he, -, hu⟩ := IM.first_under h.scope h.reads O
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  rw [← epub_eq] at hx h6 ⊢
  rw [IM.placesW_full, IM.linksW_full] at hx h6 ⊢
  rw [← head_N_is h] at hx ⊢
  exact xk_of_four ((handsPt_G_four h.𝔇.N Mg linksFull (flatPlacesOf linksFull true) z ft 2
    Bs.G₀.first (K1.gpOf Zp) nm X (Johnson.Desc.First.Walk.Seat.fvsOf Zp.p.built.links)
    Zp.first.lin.kCol _ (hm ▸ rowG_head h O) s
    (fun hn => groups_of_sentence (N := h.𝔇.pubD.N) (Mg := Mg)
      (fun y => by rw [hpub, First.pubAll_noneSent]) (z, s) hn)
    fun _ hbk => own_two_head h O hreach hbk).under hu) hy h0 (mark_opening_head h hb ft hy) hx h6

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.rowG_all
#print axioms ProofFile.Honest.K1.rowG_all_fails
#print axioms ProofFile.Honest.K1.rowG_all_lacks
#print axioms ProofFile.Honest.K1.rowG_head
#print axioms ProofFile.Honest.K1.frame_two_head
#print axioms ProofFile.Honest.K1.own_two_head
#print axioms ProofFile.Honest.K1.mark_opening_head
#print axioms ProofFile.Honest.K1.xk_opening_head
