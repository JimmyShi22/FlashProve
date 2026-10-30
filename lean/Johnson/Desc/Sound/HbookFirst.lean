-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/HbookFirst.lean: THE PREMISE hbook OF THE LAW AT "LIN point", IN ITS FENCED FORM (Johnson/Desc/Sound/PointFenced.lean), PAID AT THE RULED READER (wordsFirst: wordsOn at the table tabAt st.codes arr (seatBy noFirst book) st w: Johnson/Desc/Sound/TabAt.lean | WordsAt.lean). Two theorems.
  tabFirst_at_book: AT ONE RECORD: where the tree at the place z of the book bears the number z (h₂), and every message of the statement has a place in the book at a tree that is there (h₃): where the book lays n at (j, t) and the statement has the shape sh there: the ruled reader's table at n is the witness's accessor at THE RECORD's codes, sh and (j, t). One call of tabFirst_at_plan (Johnson/Desc/Sound/WordsAtPlan.lean), at M := the statement's own list of shapes.
  hbook_first: SO THE FENCED hbook, TO THE LETTER, at tabP₁ a w := tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w: from h₂ | h₃ ASKED INSIDE THE PROMISE, AT A RECORD WITHOUT A MARK.
WHO PAYS h₂ | h₃ THERE (by report, none called here): h₂: the public item "K12.bookInOrder" at ft := 0, with its plain sentence numbers_of_book0 (Johnson/Desc/K12/Door/DoorGives.lean); open at every border and in the last promise, by report; or a theorem on the seated description · h₃: the book-keeping on the book's sizes with "K12.seatsCarried".

Limits. Rules under letters. NO MEMBER IS SHOWN.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.WordsAtPlan
import Johnson.Desc.Sound.TieEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Means
open VerifiableInference.Desc.First (Meaning Numbers ModelPart)

variable {Cells Tok : Type}

/-- **At one record: the ruled reader's table, by the book's own place.** -/
theorem tabFirst_at_book (arr : ℕ → ℕ → ℕ) (st : Statement) (B : TreeBook)
    (h₂ : ∀ (z : ℕ) (T : Tree), B.trees[z]? = some T → T.number = z)
    (h₃ : ∀ o, o < st.oracles.size → ∃ q : ℕ × ℕ, B.place[o]? = some q ∧ q.1 < B.trees.size)
    (w : Wit Cells Tok MsgT) (n j t : ℕ) (sh : OracleShape) (hp : B.place[n]? = some (j, t))
    (hs : (st.oracles[n]?).map (·.shape) = some sh) :
    tabAt st.codes arr (seatBy noFirst B) st w n = w.tab st.codes sh (arr j t) j t := by
  have hn : n < st.oracles.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hs
    cases hs
  obtain ⟨sh', q, e1, e2, e3⟩ := tabFirst_at_plan arr (st.oracles.toList.map (·.shape)) st B
    (fun o _ => by rw [List.getElem?_map, Array.getElem?_toList]) h₂ h₃ w n hn
  rw [List.getElem?_map, Array.getElem?_toList, hs] at e1
  rw [hp] at e2
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  exact e3

/-- **The fenced hbook at the ruled reader.** -/
theorem hbook_first {P₁ P₀ : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (get : P₁ → P₀ × First.S)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (h₂ : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → (get p).2.failed = none →
      ∀ (z : ℕ) (T : Tree), (get p).2.book.trees[z]? = some T → T.number = z)
    (h₃ : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → (get p).2.failed = none →
      ∀ o, o < (get p).2.st.oracles.size →
        ∃ q : ℕ × ℕ, (get p).2.book.place[o]? = some q ∧ q.1 < (get p).2.book.trees.size) :
    ∀ p y, ocEnd get N₁ Mg₁ links ps p y → (get p).2.failed = none → (get p).2.st.codes = cs →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh →
      tabAt (get p).2.st.codes arr (seatBy noFirst (get p).2.book) (get p).2.st w n =
        w.tab cs sh (arr j t) j t := by
  intro p y hO hm hc w n j t sh hp hs
  rw [tabFirst_at_book arr _ _ (h₂ p y hO hm) (h₃ p y hO hm) w n j t sh hp hs, hc]

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tabFirst_at_book
#print axioms VerifiableInference.Desc.Sound.hbook_first
