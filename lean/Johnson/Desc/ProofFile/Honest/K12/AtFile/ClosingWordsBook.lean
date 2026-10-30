-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingWordsBook.lean: one public test on the book that ties
the switch's part to the closing test's second part, and the job's rows from it.

  wordsBookB          the test: the first n carried entries of the two parts agree in owner, start
                      and count, and the next of the second is the first part's own, from 0
  wordsBook_parts     what it says
  carryRows_of_book   the job's rows at the second part's coins are message 0 of the switch's lot

By what. carryRows_at_lent (ClosingWordsJob.lean); lend_stretch (K12/AgreeBook.lean) for the count.

Limits. At which book the test says yes: under the head, where the maker returns a book, at that
book, at the finish at the blank ground: wordsBookB_at_makers_book (LotLBookLine.lean). Nothing on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingWordsJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K2.Law (SwitchCoins)
open ProofFile.Honest (carryE)

variable {W₀ Rc Xi Tr X V' : Type} {Bk : ProverCoinCounts}

/-- **The test on the book.** a₁: the switch's part. a₂: the later part. n: how many stretches the
switch carries. -/
def wordsBookB (Bk : ProverCoinCounts) (a₁ a₂ : Addr) (n : ℕ) : Bool :=
  decide (n ≤ (carryE Bk a₁).length) &&
    decide (((carryE Bk a₁).take n).map (fun e => (e.owner, e.start, e.count)) =
      ((carryE Bk a₂).take n).map fun e => (e.owner, e.start, e.count)) &&
    decide (((carryE Bk a₂)[n]?).map (fun e => (e.owner, e.start)) = some (a₁, ⟨0, 0⟩))

/-- What the test says. -/
theorem wordsBook_parts {a₁ a₂ : Addr} {n : ℕ} (h : wordsBookB Bk a₁ a₂ n = true) :
    n ≤ (carryE Bk a₁).length ∧
      (∀ t a, t < n → (carryE Bk a₁)[t]? = some a → ∃ a', (carryE Bk a₂)[t]? = some a' ∧
        a'.owner = a.owner ∧ a'.start = a.start ∧ a'.count = a.count) ∧
      ∃ a', (carryE Bk a₂)[n]? = some a' ∧ a'.owner = a₁ ∧ a'.start = ⟨0, 0⟩ := by
  unfold wordsBookB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun t a ht ha => ?_, ?_⟩
  · have e := congrArg (·[t]?) h2
    simp only [List.getElem?_map, List.getElem?_take, if_pos ht] at e
    rw [ha, Option.map_some] at e
    obtain ⟨a', ha', k⟩ := Option.map_eq_some_iff.1 e.symm
    exact ⟨a', ha', (congrArg (·.1) k), (congrArg (·.2.1) k), (congrArg (·.2.2) k)⟩
  · obtain ⟨a', ha', k⟩ := Option.map_eq_some_iff.1 h3
    exact ⟨a', ha', congrArg (·.1) k, congrArg (·.2) k⟩

/-- **The job's rows at the later part's coins are message 0 of the switch's lot.** -/
theorem carryRows_of_book {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
    {closing : K2.Closing} {p : K2.SwitchPlace} {ch : ℕ} {k : Coins Bk} {w : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    {V : ℕ → Johnson.Prover.Send.Rows}
    (hH : K2.handed ch p k = some c)
    (hV : K2.switchRowsLaid D readers closing p c w hd = .ok V)
    (h1 : 1 < (K2.switchSent p.sizes p.others).size)
    {a₂ : Addr} {q : Part V' (Local W₀ Rc Xi Tr) X} {cT : q.Coins}
    (hT : lendPart Bk (Bk.rowsOf ch) (k.look ch) a₂ q = .ok cT)
    (hb : wordsBookB Bk ⟨p.place, 0⟩ a₂ p.front.length = true)
    (hq : (q.carries[p.front.length]?).map (·.2) =
      some (K2.messageDue p.sizes.codes (shapeL p) none)) :
    carryRows D readers closing p w hd (stretches q.carries cT.2.2) = .ok (V 0) := by
  obtain ⟨hlen, hsame, a', ha, ho, hs⟩ := wordsBook_parts hb
  have l₂ := lend_of_lendPart_words hT
  obtain ⟨hd', -⟩ := ProofFile.Honest.K12.lend_stretch _ _ _ _ l₂ _ a' ha
  have hc : a'.count = K2.messageDue p.sizes.codes (shapeL p) none := by
    rw [hq] at hd'
    exact (Option.some.inj hd').symm
  exact carryRows_at_lent hH hV h1 hT hlen hsame ha ho hs hc

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.wordsBook_parts
#print axioms ProofFile.Honest.K12.AtProof.carryRows_of_book
