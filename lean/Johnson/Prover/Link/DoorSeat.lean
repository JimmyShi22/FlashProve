-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorSeat.lean: THE FORM's HALF AT THE LINK: IN FRONT OF THE PROXIMITY TEST THE
GROUP's TWO MEMBERS AND THE ONE MESSAGE's THIRD ORACLE MESSAGE ARE, IN THIS ORDER, ALL THE PARTS OF
ONE TREE, OPENED AT NO LIST: ReadSeat (Johnson/Prover/Link/ReadSeat.lean) behind the link's steps.
Off the library's record of facts (LinkRanR) and the plan's share (DoorPlan), as
Johnson/Prover/Link/DoorPay.lean looks them up. General in the context in front of the steps.

Main names (namespace Johnson.Prover.Link).
  msg_size, ran_tau, ran_part   three oracle messages; each in tree 0; the j-th is part j.
  ran_theTree   THE ONE TREE: its shape and number; opened at no list; its three parts; the mark.
  readSeat_of_ran   THE STATEMENT, with the tree's shape, number and mark.

By calls: layTrees_fits (Johnson/Desc/Book/BookFits.lean); treesSent_at, partsLaid_one, cnt_all
(Johnson/Prover/Link/BookLaid.lean); ran_place, ran_size, ran_oracle0, ran_oracle1, ran_oracle2
(DoorPay.lean).

Limits. The record stands IN FRONT OF THE BATCHING: that ReadSeat goes over the test's beginning is
not shown here. "One tree" is DoorPlan's clause "one". Nothing on values. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorPay
import Johnson.Prover.Link.ReadSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Book (cnt layTrees_fits)

/-! ## The one tree behind the link's steps -/

section Ran
variable {S : LinkShape} {first further : TableKey} {c c1 : Ctx} {x : LinkRun} {D : LinkDataR}
  (hR : LinkRanR S first further c c1 x D) {p : P12} {cur nxt : Fmt.M1.Stage} {i n : Nat × Nat}
  (Pl : DoorPlan S c.st.codes p cur nxt i n)

include hR Pl

theorem msg_size : (linkMessage S 1).size = 3 := by simp [linkMessage, Pl.ahead]

theorem ran_tau (j : Nat) (hj : j < 3) : D.lay.tree.getD j 0 = 0 := by
  have h := (layTrees_fits hR.laid j (by rw [msg_size hR Pl]; exact hj)).1
  rw [Pl.one D.lay hR.laid] at h
  omega

theorem ran_part (j : Nat) (hj : j < 3) : D.lay.part.getD j 0 = j := by
  have h := (layTrees_fits hR.laid j (by rw [msg_size hR Pl]; exact hj)).2
  rw [ran_tau hR Pl j hj] at h
  rw [h]
  exact cnt_all _ j fun k hk => ran_tau hR Pl k (Nat.lt_trans hk hj)

/-- **The one tree**: its shape, its number; opened at no list; its three parts; it holds a message
without a sample. -/
theorem ran_theTree :
    ∃ (T : Tree) (sh : TreeShape), c1.book.trees[c.book.trees.size]? = some T ∧
      D.lay.shapes[0]? = some sh ∧ T.shape = sh ∧ T.number = c.ch.firstTree + c.ch.roots ∧
      T.lists = 0 ∧
      T.parts = #[c.st.oracles.size, c.st.oracles.size + 1, c.st.oracles.size + 2] ∧
      T.oneList = true := by
  have hs : 0 < D.lay.shapes.size := by rw [Pl.one D.lay hR.laid]; exact Nat.one_pos
  have hnew := treesSent_at c.ch.firstTree D.lay.shapes.toList c.ch.roots c.book.trees 0
  rw [Nat.add_zero, Nat.add_zero, Array.getElem?_toList, Array.getElem?_eq_getElem hs] at hnew
  have h := partsLaid_one (linkMessage S 1) D.lay c.st.oracles.size c.book.trees.size _ _
    (fun j hj => ran_tau hR Pl j (by rw [msg_size hR Pl] at hj; exact hj)) hnew
  refine ⟨_, D.lay.shapes[0], by rw [hR.book]; exact h, Array.getElem?_eq_getElem hs, rfl, rfl,
    rfl, ?_, ?_⟩
  · simp [msg_size hR Pl, List.range_succ]
  · simp [msg_size hR Pl, List.range_succ, linkMessage, Pl.ahead]
    exact .inr (.inr rfl)

/-- **ReadSeat IN FRONT OF THE PROXIMITY TEST**: the two members and the third message are the
parts of the one tree. -/
theorem readSeat_of_ran {t : T12} (hst : t.st = c1.st) (hb : t.book = c1.book) :
    ∃ (T : Tree) (sh : TreeShape),
      ReadSeat t.st t.book [c.st.oracles.size, c.st.oracles.size + 1] (c.st.oracles.size + 2)
        c.book.trees.size T ∧
      D.lay.shapes[0]? = some sh ∧ T.shape = sh ∧ T.number = c.ch.firstTree + c.ch.roots ∧
      T.oneList = true := by
  obtain ⟨T, sh, a1, a2, a3, a4, a5, a6, a7⟩ := ran_theTree hR Pl
  have hpl : ∀ j, j < 3 → t.book.place[c.st.oracles.size + j]? = some (c.book.trees.size, j) := by
    intro j hj
    rw [hb, ran_place hR j (by rw [msg_size hR Pl]; exact hj), ran_tau hR Pl j hj,
      ran_part hR Pl j hj, Nat.add_zero]
  refine ⟨T, sh, ⟨by rw [hb]; exact a1, ?_, a6, a5, ?_, ?_⟩, a2, a3, a4, a7⟩
  · intro q hq
    have hq' : q < 3 := hq
    match q, hq' with
    | 0, _ => exact hpl 0 (by decide)
    | 1, _ => exact hpl 1 (by decide)
    | 2, _ => exact hpl 2 (by decide)
  · have h0 := ran_oracle0 hR
    have h1 := ran_oracle1 hR
    have h2 := ran_oracle2 hR Pl.ahead
    rw [← hst] at h0 h1 h2
    have hans : (rowShape S).answers = 1 := rfl
    have hfa : (foldMaskNotice (linkFoldShape S)).shape.answers = 0 := rfl
    unfold sharesOk
    rw [a6]
    simp [h0, h1, h2, linkOracle, hans, hfa]
  · intro o ho
    have ho' : o = c.st.oracles.size ∨ o = c.st.oracles.size + 1 ∨ o = c.st.oracles.size + 2 := by
      simpa using ho
    rw [hst, ran_size hR, msg_size hR Pl]
    omega

end Ran

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.msg_size
#print axioms Johnson.Prover.Link.ran_tau
#print axioms Johnson.Prover.Link.ran_part
#print axioms Johnson.Prover.Link.ran_theTree
#print axioms Johnson.Prover.Link.readSeat_of_ran
