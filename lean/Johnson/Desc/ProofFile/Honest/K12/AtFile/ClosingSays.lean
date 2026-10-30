-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingSays.lean: the clause on values of `DataFront`
(K12/ShapeAll.lean) in front of the first chain's closing proximity test, from the items that the
test closes: `row n carried`, `row n position`, `row n (sample 0)` (`backRow`,
Johnson/Desc/First/Borders.lean). The thread carries these items at the verifier's own state, with
its true targets. General in the thread's letters.

  `rows_of_thr`       an open item "row" says, at a stand of the thread, that every row of the class
                      says its claim of the witness's words
  `open_of_classes`   every open row of the group lies in one of two classes, so it says its claim
  `samples_of_class`  each member's sample rows lie in the class of the moment's samples
  `allSay_at_items`   the rows that the test takes in say their claims of the words that the plain
                      rows make, where these are the witness's words on the members' tables

By what. `rows_of_thr`: the clause (I) of `Thr`, `Item.holds`, `rowSays`
(Johnson/Desc/First/Close/Law/FillRow.lean): the adapted meaning keeps the letter `row`.
`allSay_at_items`: `runRows_iff_items` (Johnson/Desc/Means/ItemsAt.lean), `allSay_begun`
(ItemsBegun.lean), `says_members` (Johnson/RunOne/Law/GrowsOfAllSay.lean), as in `allSay_of_met`
(K12/SaysOfMet.lean).

Hypotheses. hMg: the letter's meaning of `row` is `rowSays` at a reader of words. hopen: the item is
open at the border. h0, h1, h2: the classes lie one behind the other and cover the group's rows:
`rowsAtFit` and `rowsHeld` (Borders.lean) are tests that say so. hm: each member's seat is among those
that the segment sends at moment 0. hK, hI: no open row is a sample row; the statement is in order.
hw: the witness's words are the plain rows' on the members' tables.

Limits.
- hw is the tie of the thread's witness to the job's rows: it is asked, not shown. It is the whole
  content of "the prover's rows are the witness's messages" at this test.
- The words are those of the thread's witness at the challenges heard.
- A stand of `Thr` is a hypothesis.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `rows_of_thr` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread from `Thr` as a premise.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingThr
import Johnson.Desc.ProofFile.Honest.K12.SaysOfMet
import Johnson.Desc.First.Close.Law.FillRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc.First (S Item RowClass Numbers classRows rowSays)
open VerifiableInference.Desc (Strs Wit)
open ProofFile.Honest.K12.Light (WordsTied)
open Johnson.RunOne.Law.GrowsOfAllSay (says_members)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **An open item "row" at a stand of the thread.** -/
theorem rows_of_thr (L : ProofFile.Honest.FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)
    (words : P × S → Strs → Wit Cells Tok M → Words GE)
    (hMg : ∀ w, (L.Mg w).row = rowSays L.N words) {b n : ℕ} {c : RowClass}
    (hopen : Item.row n c ∈ L.thread.opened b) {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (h : Thr L.thread b k s m E) :
    AllSay rdE s.st (classRows L.N n c s)
      (words (L.thread.seat k m s) (L.thread.strs E)
        (L.thread.wit k m.st.input (m.st.heard ++ []))) := by
  have h' := h
  unfold Thr at h'
  obtain ⟨-, -, -, hI, -, -, -⟩ := h'
  have e := hI [] (Item.row n c) hopen
  have e' : (L.Mg m.st.input).row n c (L.thread.seat k m s) (L.thread.strs E)
      (L.thread.wit k m.st.input (m.st.heard ++ [])) := e
  rw [hMg] at e'
  exact e'

/-- **Every open row of the group lies in one of two classes.** -/
theorem open_of_classes {N : Numbers} {n : ℕ} {s : S} {G : Group} {m : Words GE}
    (hg : s.st.groups[N.groupAt n]? = some G)
    (hc : AllSay rdE s.st (classRows N n .carried s) m)
    (hp : AllSay rdE s.st (classRows N n .position s) m)
    (h0 : (N.rowsAt n .carried).1 = 0)
    (h1 : (N.rowsAt n .position).1 = (N.rowsAt n .carried).2)
    (h2 : G.rows.size ≤ (N.rowsAt n .carried).2 + (N.rowsAt n .position).2) (i : ℕ) :
    OpenSays rdE s.st (N.groupAt n) i m := by
  intro r hr
  obtain ⟨G', hG', hi⟩ := rowAt_iff.1 hr
  rw [hg] at hG'
  obtain rfl := Option.some.inj hG'
  have hl : i < G.rows.size := (Array.getElem?_eq_some_iff.1 hi).1
  by_cases hlt : i < (N.rowsAt n .carried).2
  · refine hc r ?_
    simp only [classRows, hg]
    refine List.mem_filterMap.2 ⟨i, List.mem_range.2 hlt, ?_⟩
    rw [h0, Nat.zero_add]
    exact hi
  · refine hp r ?_
    simp only [classRows, hg]
    refine List.mem_filterMap.2 ⟨i - (N.rowsAt n .carried).2, List.mem_range.2 (by omega), ?_⟩
    rw [h1, Nat.add_sub_cancel' (Nat.le_of_not_lt hlt)]
    exact hi

/-- **Each member's sample rows lie in the class of the moment's samples.** -/
theorem samples_of_class {N : Numbers} {n t : ℕ} {s : S} {m : Words GE} {os : List ℕ}
    (hq : AllSay rdE s.st (classRows N n (.sample t) s) m)
    (hm : ∀ o ∈ os, (s.book.place[o]?).any (fun x => (N.sent n t).contains x) = true) :
    sampleItem rdE s.st os m := by
  intro o ho x hx r hr
  refine hq r ?_
  simp only [classRows]
  refine List.mem_flatMap.2 ⟨o, List.mem_range.2 (Array.getElem?_eq_some_iff.1 hx).1, ?_⟩
  rw [if_pos (hm o ho), hx]
  exact hr

/-- **The rows taken in say their claims of the words that the plain rows make.** -/
theorem allSay_at_items (St : Statement) (g : ℕ) (G : Group) (hG : St.groups[g]? = some G)
    (hI : InOrder St) (hK : OpenKinds St) (m : Words GE) (hO : ∀ i, OpenSays rdE St g i m)
    (hS : sampleItem rdE St G.members.toList m) (Ly : GroupLayout) (R : PlainRows)
    (hw : WordsTied St g G m Ly R) :
    AllSay rdE (begun St g G) (runRows St G).toList (wordsAt (begun St g G) Ly R) :=
  (allSay_begun rdE hI g hG _).2 fun r hr =>
    (says_members (hI.runRows g G hG r hr) _ _ hw).1
      ((runRows_iff_items rdE hK g hG _).2 ⟨hO, hS⟩ r hr)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.rows_of_thr
#print axioms ProofFile.Honest.K12.open_of_classes
#print axioms ProofFile.Honest.K12.samples_of_class
#print axioms ProofFile.Honest.K12.allSay_at_items
