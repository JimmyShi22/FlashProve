-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Unopened.lean: THE TREES THAT A SEGMENT LAYS HAVE BEEN OPENED AT NO
LIST AS LONG AS NO FURTHER MESSAGE IS SENT BEHIND THE SEGMENT's THREE SENDINGS. Segments 1 to 23. In
the goals' scope, from the returns of one fold. THAT NO FURTHER MESSAGE IS SENT IS A PREMISE HERE,
AS AN EQUATION OF COUNTS. A tool for `AllOpen`'s clause "a tree of one list has not been opened"
(Returns/ReadOpen.lean). A definition; statements with their proofs: calls and sums.

  `newZero T B` every tree of the book B at a number from T on has `lists` = 0
  `newZero_stays` it goes along `treesStay` (Returns/TreesStay.lean)
  `switch_step_zero` AT THE SEAT, over the switch into group l + 1 (the cuts 14 (l + 1) + 2 and +
                    3): what it lays itself
  `commit_step_stays` AT THE SEAT, over hearing sub-protocol number 3 or 5 of a segment: `treesStay`
  `unopened_seg` THE TOP: l + 1 < 24 · the fold's return at a cut kE from 14 (l + 1) + 8 up to the
                    front's length · the count of oracle messages there is the count at 14 (l + 1) +
                    2 and what the segment's three sendings add ⊢ `newZero` at the number of trees
                    at 14 (l + 1) + 2, of the book at kE

THE ROAD. The switch's own yes leaves what it lays unopened (`yes_fresh`, Returns/SwitchFresh.lean).
The counts at the seven cuts only rise, and by the premise they rise by no more than the three
sendings add (`counts_link`, Returns/SendCounts.lean): so over each of the three stretches between
and behind the sendings the count stands, and the book with it (`book_same_between`,
Returns/BookSame.lean). Each later sending leaves the elder trees and lays unopened ones
(`commit_stays`, Returns/TreesStay.lean).

By, beside these, this folder's: `closed_behind_laid` (Returns/ClosedReached.lean),
`stated_of_close` (Returns/MembersReached.lean): the opened messages are stated · `counts_rise`
(Returns/BookSame.lean) · `treesStay_same`, `treesStay_trans` (Returns/TreesStay.lean). The
library's: `k2_link_sits`, `Joined.yes` (Johnson/IMR/FirstSeats.lean), `hear_at_flat`
(Johnson/IMR/FlatIx.lean), `flatIx_scope` (Johnson/IMR/FlatScope.lean), `laid_at`
(Johnson/IMR/FrontPin.lean), `andThen_yes`, `fold_next` (Johnson/IMR/FoldTools.lean), `head_inv`,
`firstFront_rows` (Johnson/Top/H0/Tw/K2C/Closed.lean) · `framesOf_core`
(Johnson/Goal/Meaning/CoreSeated.lean) · `hear_flat`, `hear_commitQ` (Johnson/IMR/FrameAt.lean) ·
`open_fits`, `open_has` (Johnson/IMR/WalkGivesAt.lean) · `fold_cut` (Johnson/IMR/GroupRest.lean),
`front_len` (Johnson/IMR/FinPin.lean). `switch_step_zero`'s descent to the text's yes is
`entry_count`'s (Returns/SendCounts.lean), which is the library's `entry_mask`'s: typed a third
time.

Limits. THE EQUATION OF COUNTS IS PAID BY NOBODY HERE. Segments 0 and 24: nothing. That a fold
returns is shown of no proof here. This file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.BookSame
import Johnson.Desc.K2.Honest.Returns.SwitchFresh
import Johnson.Desc.K2.Honest.Returns.TreesStay
import Johnson.Desc.K2.Honest.Returns.SendCounts
import Johnson.Desc.K2.Honest.Returns.MembersReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1.RelCore (coreS)
open Meaning.K2 (hear_flat hear_commitQ laid_at andThen_yes fold_next fold_cut front_len frontOf
  open_fits open_has framesOf_core msgsAt)
open ProofFile (Cl)

/-- **Every tree at a number from T on has been opened at no list.** -/
def newZero (T : Nat) (B : TreeBook) : Prop :=
  ∀ j t, T ≤ j → B.trees[j]? = some t → t.lists = 0

theorem newZero_stays {T : Nat} {a b : VerifiableInference.Desc.Ground.Core}
    (h : newZero T a.book) (k : treesStay a b) :
    newZero T b.book := by
  intro j t hj ht
  rcases Nat.lt_or_ge j a.book.trees.size with lt | ge
  · rw [k.2.1 j lt] at ht
    exact h j t hj ht
  · exact k.2.2 j t ge ht

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the seat: the switch leaves what it lays itself opened at no list.** -/
theorem switch_step_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat}
    (h24 : l + 1 < 24) {p : ProofFile.InstPub} {R R₀ R₁ : List Fmt.RoundView}
    {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    newZero t₀.book.trees.size t₁.book := by
  have hlen : 14 * (l + 1) + 2 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  obtain ⟨hB, -⟩ := laid_at hS hR O (by omega : l + 1 < 25) f₀
  obtain ⟨Lk, b, x0, eLk, e0, -, J, hx⟩ := IM.k2_link_sits hS hR O (l + 1) (by omega) h24
  have i0 : c.blocksInOrder[14 * (l + 1) + 2]? = some b := by
    have k := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : l + 1 ≤ 24) 0).trans
      (by omega : 14 * (l + 1) + 0 + 2 = 14 * (l + 1) + 2)] at k
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  revert y1
  generalize rs.take _ = rs'
  generalize gs.take _ = gs'
  intro y1
  have y1' : x0.decide t₀ rs' gs' = .ok m := y1
  have km : treesStay (coreS m) (coreS t₁) :=
    (framesOf_core treesStay_same hfs fr (List.mem_of_getElem? hf)).2.1 m t₁ y3
  refine newZero_stays (a := coreS m) (b := coreS t₁) ?_ km
  rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, -, h3⟩
  · obtain ⟨er, he⟩ := hm t₀ rs' gs'
    rw [he] at y1'
    cases y1'
  · rcases h3 with ⟨hn, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
    · cases hn
    · rw [ex] at y1'
      obtain ⟨w, a1, -⟩ := andThen_yes (n := x0.name) y1'
      obtain ⟨r₁, r₂, a, G', w', roots, -, H⟩ :=
        First.K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
      unfold S.atBetween at hB
      rw [H.hHere] at hB
      cases hB
    · rw [ex] at y1'
      have h' : First.K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some (l + 1), piece := 1, kind := .K2 } x0.name .link n)
          t₀ rs' gs' = .ok m := y1'
      obtain ⟨owed, f, S₀, es, rc, xc, hxc, hfc, hgc⟩ :=
        closed_behind_laid hS hR O (by omega : l < 24) f₀
      have H := stated_of_close hxc hgc
      rw [← hfc] at H
      intro j t hj ht
      refine yes_fresh h' (open_fits O hlen f₀) (fun x hF o ho => ?_) hj ht
      rcases hF with ⟨-, a⟩ | ⟨a, -⟩ | ⟨a, -⟩
      · rw [First.K2.firstFront_rows a] at ho
        rw [open_has O hlen f₀]
        exact H o ho
      · cases a
      · cases a

/-- **At the seat: a later sending leaves the elder trees and lays unopened ones.** -/
theorem commit_step_stays (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat}
    (h24 : l < 24) {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn}
    {j : Nat} (hj : j = 3 ∨ j = 5) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j + 1)) (ProofFile.startS Z p) R C =
      .ok (s', r', q')) :
    treesStay (coreS s) (coreS s') := by
  obtain ⟨Lk, eL, hA⟩ := hear_flat hS hR O h24
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  obtain ⟨Q, lk, mo, ar, v, rs2, gs2, cm, qv⟩ := hear_commitQ hS hR O h24 hj eL e d'
  exact treesStay_trans (commit_stays Q lk mo ar cm)
    (treesStay_same (coreS v) (coreS s') qv.1.2.2.1 qv.1.2.2.2)

/-- **A segment's trees have been opened at no list, as long as nothing more is sent.** -/
theorem unopened_seg (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat}
    (h24 : l + 1 < 24) {p : ProofFile.InstPub} {R R₀ RE : List Fmt.RoundView}
    {C C₀ CE : List VerifiableInference.Desc.OpenedColumn} {t₀ s : S} {d : Nat}
    (hk : 14 * (l + 1) + 8 + d ≤ (frontOf c).length)
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 8 + d)) (ProofFile.startS Z p) R C = .ok (s, RE, CE))
    (hc : s.st.oracles.size = t₀.st.oracles.size +
      (1 + (First.K2.targetAt Z.first.shape (l + 1)).kept.size +
        (msgsAt Z.first.shape (l + 1) 0 + 1)) +
      msgsAt Z.first.shape (l + 1) 1 + msgsAt Z.first.shape (l + 1) 2) :
    newZero t₀.book.trees.size s.book := by
  obtain ⟨t6, R6, C6, g6⟩ := fold_cut (k := 14 * (l + 1) + 8) d f
  obtain ⟨t₅, R₅, C₅, g₅⟩ := fold_cut (k := 14 * (l + 1) + 7) 1 g6
  obtain ⟨t₄, R₄, C₄, g₄⟩ := fold_cut (k := 14 * (l + 1) + 6) 1 g₅
  obtain ⟨t₃, R₃, C₃, g₃⟩ := fold_cut (k := 14 * (l + 1) + 5) 1 g₄
  obtain ⟨t₁, R₁, C₁, g₁⟩ := fold_cut (k := 14 * (l + 1) + 3) 2 g₃
  obtain ⟨c1, c4, c6⟩ := counts_link hS hR O (by omega : 1 ≤ l + 1) h24 f₀ g₁ g₃ g₄ g₅ g6
  -- the counts only rise
  have u13 := counts_rise O (by omega : 14 * (l + 1) + 3 ≤ 14 * (l + 1) + 5) (by omega) g₁ g₃
  have u45 := counts_rise O (by omega : 14 * (l + 1) + 6 ≤ 14 * (l + 1) + 7) (by omega) g₄ g₅
  have u6s := counts_rise O (by omega : 14 * (l + 1) + 8 ≤ 14 * (l + 1) + 8 + d) hk g6 f
  -- so over the three stretches the book stands
  have e13 : t₃.book = t₁.book := book_same_between O (by omega) (by omega) g₁ g₃ (by omega)
  have e45 : t₅.book = t₄.book := book_same_between O (by omega) (by omega) g₄ g₅ (by omega)
  have e6s : s.book = t6.book := book_same_between O (by omega) hk g6 f (by omega)
  -- the walk
  have z1 := switch_step_zero hS hR O h24 f₀ g₁
  have z3 : newZero t₀.book.trees.size t₃.book := by rw [e13]; exact z1
  have z4 : newZero t₀.book.trees.size t₄.book :=
    newZero_stays (a := coreS t₃) (b := coreS t₄) z3
      (commit_step_stays hS hR O h24 (j := 3) (Or.inl rfl) g₃ g₄)
  have z5 : newZero t₀.book.trees.size t₅.book := by rw [e45]; exact z4
  have z6 : newZero t₀.book.trees.size t6.book :=
    newZero_stays (a := coreS t₅) (b := coreS t6) z5
      (commit_step_stays hS hR O h24 (j := 5) (Or.inr rfl) g₅ g6)
  rw [e6s]
  exact z6

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.newZero_stays
#print axioms VerifiableInference.Desc.K2.Honest.Returns.switch_step_zero
#print axioms VerifiableInference.Desc.K2.Honest.Returns.commit_step_stays
#print axioms VerifiableInference.Desc.K2.Honest.Returns.unopened_seg
