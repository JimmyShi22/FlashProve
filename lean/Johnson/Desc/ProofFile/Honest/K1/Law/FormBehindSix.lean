-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormBehindSix.lean: THE FIRST SEGMENT's OPENING (number 2 of
the first chain's flat list): WHICH PUBLIC ITEMS ARE OPEN OR TIED AT BORDER 3, AS TWO CLOSED LISTS;
and the six tests of the table's promise at border 3 behind an accepting step of the whole joined
member, WITH THE LAST OF THE SIX AT THE STATE BEHIND AS A PREMISE, in the place of the three
premises on the bare joined sub-protocol that xk_opening_at takes
(Johnson/Desc/ProofFile/Honest/K1/Law/FormBehindTwo.lean). No thread, no prover and no file's string
occurs. No definition. Statements and proofs.

  open_three, tied_three: at the closed list moreAll (Johnson/Desc/Sound/MoreAll.lean) and the
    written lists linksW and placesW (Johnson/IMR/WrittenList.lean): seven items are open at border
    3, and two are tied to what is open there: by evaluation in Lean's kernel. Kin in the library,
    at the borders 338 and 339: front338W, behind339W (Johnson/P4R/HandsE338.lean); each of these
    states the open and the tied items as one list.
  six_of_nine: so, at any meaning with these extra rows: "in order" and the public tests of these
    nine at a state give the further test P1K2.EQ (Johnson/P1K2R/TieTwo.lean) at border 3 at that
    state.
  xk_of_four: for any sub-protocol: what it owes at one state in front, at a further test that is
    true at the next border whatever the state, gives the four tests on the book-keeping behind; the
    further test behind is then a premise.
  handsPt_G_four: the opening's whole sub-protocol owes that much from the table's row, the groups'
    count and the own seats' test alone.
  xk_opening_six: THE STATEMENT: xk_opening_at's premises less its three on the bare sub-protocol,
    and h6: the further test at border 3 at the state behind.

Why. The six tests are four on the book-keeping, which do not read the further test (xk_swap,
Johnson/Desc/AtSeats/HandsBridge.lean), and the further test. The library's hands_G
(Johnson/Desc/AtSeats/HandsAtThree.lean) is general in the further test, and spends its premise on
it in its last field alone. xk_opening_at's three premises speak of every state behind a step of the
bare joined sub-protocol; a fact that is known only behind the chain's own member's accepting step
cannot be laid into them: the member stands under that sub-protocol, not the other way round.

Limits. xk_opening_six BY ITSELF IS LESS THAN "the six behind from the six in front": IT GIVES THE
FOUR; THE FURTHER TEST BEHIND IS A PREMISE ON THE STATE BEHIND THE STEP (h6). Nothing here pays it:
six_of_nine brings it down to "in order" and nine public tests behind, which are premises. The
table's row (hT), the groups' count (hgroups) and the own seats' test (hown) at the state in front
are premises: shown at no numbers or meaning. The letter mk stands in hT alone. That a meaning has
the extra rows moreAll (hm) is a premise. The two closed lists are evaluations in Lean's kernel
(decide +kernel) over the written lists: no compiled code; a row more in the table reopens them; for
them maxRecDepth is raised to 1000000 in this file. xk_opening_six stands in the goals' scope, at
files that are read, under IM.Open at the earlier hash OnBytes.secondHashFunction. That a member accepts
anywhere is not shown. Nothing on W's sending. Nothing on soundness, on completeness or on any other
property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormBehindTwo
import Johnson.Desc.AtSeats.HandsBridge
import Johnson.Desc.AtSeats.MoreAtOpening
import Johnson.Desc.Sound.MoreAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open IM (linksW placesW)
open ProofFile (Cl)
open HashBuild (EPub epub_of epub_parts handsPt_of_all hands_G joined_under xk_swap)

/-! ## 1 What is open, and what is tied, at border 3: by evaluation in Lean's kernel -/

/-- **The seven public items that are open at border 3.** -/
theorem open_three : (First.pubSets moreAll linksW placesW)[2 + 1]?.getD [] =
    [.unheard, .ledger 0, .lookIn 0 2, .linkFresh 0, .freeAbove 0, .more (some 0) "frame.sentIs",
      .more (some 0) "ledger.treesAre"] := by
  decide +kernel

/-- **The two public items that are tied to what is open at border 3.** -/
theorem tied_three : First.pubOfItems (openAt linksW placesW (2 + 1)) =
    [.indexIs, .indexThere] := by
  decide +kernel

variable {Pp W : Type}

/-- **"In order" and the nine public tests at a state give the further test at border 3 there.** -/
theorem six_of_nine (Mg : Meaning Pp W) (hm : Mg.more = moreAll) (z : Pp) (t : S)
    (hO : Mg.inOrder (z, t) = true) (h1 : Mg.pub .unheard (z, t) = true)
    (h2 : Mg.pub (.ledger 0) (z, t) = true) (h3 : Mg.pub (.lookIn 0 2) (z, t) = true)
    (h4 : Mg.pub (.linkFresh 0) (z, t) = true) (h5 : Mg.pub (.freeAbove 0) (z, t) = true)
    (h6 : Mg.pub HashBuild.sentItem0 (z, t) = true)
    (h7 : Mg.pub HashBuild.treesItem0 (z, t) = true) (h8 : Mg.pub .indexIs (z, t) = true)
    (h9 : Mg.pub .indexThere (z, t) = true) :
    P1K2.EQ Mg linksW placesW z (2 + 1) t = true := by
  rw [← epub_eq]
  refine epub_of hO (fun q hq => ?_) fun q hq => ?_
  · rw [hm, open_three] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
  · rw [tied_three] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact h8
    · exact h9

/-! ## 2 The four tests on the book-keeping, without a word on the further test behind -/

/-- **From what is owed at a further test that is true at the next border, and the further test
behind, to the six tests behind.** For any sub-protocol. -/
theorem xk_of_four {N : Numbers} {links : List ModelPart} {ps : List Place} {E : ℕ → S → Bool}
    {ft k : ℕ} {b : Block S Cl} {s s' : S}
    (H : IM.HandsPt N links ps (fun j t => decide (j = k + 1) || E j t) ft k b s)
    (hy : IM.Yes ft b s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : IM.XK N links ps E k s = true) (h6 : E (k + 1) s' = true) :
    IM.XK N links ps E (k + 1) s' = true :=
  xk_swap (xk_step_pt H hy h0 h1 (xk_swap hx (by
    show (decide (k = k + 1) || E k s) = true
    rw [(IM.xk_parts hx).2.2.2.2, Bool.or_true]))) h6

/-- **What the opening's whole sub-protocol owes at such a test, at one state in front**: from the
table's row, the groups' count and the own seats' test. -/
theorem handsPt_G_four (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (z : Pp) (ft k : ℕ) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : ℕ) (mk : List First.Pub)
    (hT : RowG N Mg.more links ps k (K1.layOf (K1.firstPar q gp)).shapes.size
      (K1.firstPar q gp).sent.size mk)
    (s₀ : S)
    (hgroups : Mg.pub .noneSent (z, s₀) = true → N.groupAt 0 = s₀.st.groups.size)
    (hown : Mg.inOrder (z, s₀) = true → First.bookAt N ps[k]? s₀ = true →
      K1.ownSeatsB N (openAt links ps (k + 1)) (K1.firstPar q gp)
        (s₀.check.frame.atMoment 0).length s₀.book.trees.size = true) :
    IM.HandsPt N links ps (fun j t => decide (j = k + 1) || EPub z Mg links ps j t) ft k
      (K1.openingZero q gp nm X fvs kCol : Block S Cl) s₀ :=
  have low : ∀ t, (decide (k = k + 1) || EPub z Mg links ps k t) = true →
      EPub z Mg links ps k t = true := fun t h => by
    rw [decide_eq_false (by omega), Bool.false_or] at h
    exact h
  handsPt_of_all s₀ fun E₀ h1 h2 =>
    hands_G N Mg.more links ps E₀ ft k q gp nm X fvs kCol mk hT
      (fun s hx => by
        obtain ⟨rfl, he⟩ := h1 s (IM.xk_parts hx).2.2.2.2
        exact hgroups ((epub_parts (low _ he)).2.1 _ hT.noneSent))
      (fun s hx => by
        obtain ⟨rfl, he⟩ := h1 s (IM.xk_parts hx).2.2.2.2
        exact hown (epub_parts (low _ he)).1 (IM.xk_parts hx).2.2.2.1)
      fun s s' _ _ _ _ => by
        rw [h2]
        show (decide (k + 1 = k + 1) || EPub z Mg links ps (k + 1) s') = true
        rw [decide_eq_true rfl, Bool.true_or]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Fd : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE SIX TESTS AT BORDER 3, BEHIND AN ACCEPTING STEP OF THE WHOLE JOINED MEMBER AT NUMBER 2**,
in the goals' scope: from the six at border 2, facts at that one state, AND THE FURTHER TEST AT THE
STATE BEHIND (h6). -/
theorem xk_opening_six (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL Fd Z Bs base c A B) (N : Numbers)
    (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (G₀ : ProofFile.Ground) (mk : List First.Pub)
    (hT : RowG N Mg.more linksW placesW 2
      (K1.layOf (K1.firstPar G₀.first (K1.gpOf Z))).shapes.size
      (K1.firstPar G₀.first (K1.gpOf Z)).sent.size mk)
    {b b' : Block S Cl} (hL : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hp : b'.place = { chain := 1, link := some 0, piece := 1, kind := .K1 })
    (hj : IM.Joined Z 0 b b' { chain := 1, link := some 0, piece := 1, kind := .K1 })
    (s s' : S)
    (hgroups : Mg.pub .noneSent (z, s) = true → N.groupAt 0 = s.st.groups.size)
    (hown : Mg.inOrder (z, s) = true → First.bookAt N placesW[2]? s = true →
      K1.ownSeatsB N (openAt linksW placesW (2 + 1)) (K1.firstPar G₀.first (K1.gpOf Z))
        (s.check.frame.atMoment 0).length s.book.trees.size = true)
    (hy : IM.Yes ft b s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : IM.XK N linksW placesW (P1K2.EQ Mg linksW placesW z) 2 s = true)
    (h6 : P1K2.EQ Mg linksW placesW z (2 + 1) s' = true) :
    IM.XK N linksW placesW (P1K2.EQ Mg linksW placesW z) (2 + 1) s' = true := by
  rw [← epub_eq] at hx h6 ⊢
  obtain ⟨X, -, hu⟩ := joined_under hS hR O hL hp hj
  exact xk_of_four ((handsPt_G_four N Mg linksW placesW z ft 2 G₀.first (K1.gpOf Z) b.name X
    (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol mk hT s hgroups
    hown).under hu) hy h0 h1 hx h6

end

end ProofFile.Honest.K1
