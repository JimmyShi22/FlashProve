-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/LettersFirst.lean: TWO LETTERS OF THE LAW AT "LIN point" THAT READ THE FIRST CHAIN's LAST STATE (stOf₁ · tabP₁), AS CLOSED TERMS, WITH THE PREMISES THAT THE LAW ASKS OF THEM. Definitions and theorems.
WORDS. "The verifier's state": the value of type First.S that the verifier carries between two blocks.
  stFirst a := a.2.st · hst_first: the law's hst: rfl.
  tabFirst arr a w := tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w: the table that the reader of words (wordsFirst, Johnson/Desc/Sound/WordsAt.lean) reads · words_tabFirst: wordsOn (stFirst a) (tabFirst arr a w) IS wordsFirst arr a.2.st a.2.book w: by wordsFirst_is (Johnson/Desc/Sound/WordsAtPlan.lean).
  htab_first: the law's htab: the table reads a witness's messages and pads alone.
  hbook at tabFirst: Johnson/Desc/Sound/HbookFirst.lean's hbook_first, in the fenced form (Johnson/Desc/Sound/PointFenced.lean): restated here at the name tabFirst: hbook_tabFirst.
  (gOf lies already: gLaid Pw get, with gLaid_is, which pays the law's hg and spends neither the promise nor "no mark": Johnson/Desc/Sound/AtOcEnd.lean:66 | :70: not restated here.)

Limits. Terms and their small laws. NO MEMBER IS SHOWN.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.HbookFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Means
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart)

variable {P₁ P₀ Cells Tok : Type}

/-- The statement in the first chain's state. -/
def stFirst (a : P₀ × First.S) : Statement := a.2.st

theorem hst_first : ∀ a : P₀ × First.S, stFirst a = a.2.st := fun _ => rfl

/-- The table that the reader of words (wordsFirst) reads. -/
def tabFirst (arr : ℕ → ℕ → ℕ) (a : P₀ × First.S) (w : Wit Cells Tok MsgT) : ℕ → MsgT :=
  tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w

/-- The words made off it are that reader's. -/
theorem words_tabFirst (arr : ℕ → ℕ → ℕ) (a : P₀ × First.S) (w : Wit Cells Tok MsgT) :
    wordsOn (stFirst a) (tabFirst arr a w) = wordsFirst arr a.2.st a.2.book w :=
  (wordsFirst_is arr a.2.st a.2.book w).symm

/-- **htab**: it reads a witness's messages and pads alone. -/
theorem htab_first (arr : ℕ → ℕ → ℕ) : ∀ (a : P₀ × First.S) (w w' : Wit Cells Tok MsgT),
    (∀ n, w'.msg n = w.msg n) → (∀ j t, w'.pad j t = w.pad j t) →
    tabFirst arr a w' = tabFirst arr a w := by
  intro a w w' hm hp
  funext n
  unfold tabFirst tabAt
  split
  · funext mask row place
    unfold Wit.tab
    rw [hm, hp]
  · rfl

/-- **hbook, fenced, at tabFirst.** -/
theorem hbook_tabFirst (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (get : P₁ → P₀ × First.S)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (h₂ : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → (get p).2.failed = none →
      ∀ (z : ℕ) (T : Tree), (get p).2.book.trees[z]? = some T → T.number = z)
    (h₃ : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → (get p).2.failed = none →
      ∀ o, o < (get p).2.st.oracles.size →
        ∃ q : ℕ × ℕ, (get p).2.book.place[o]? = some q ∧ q.1 < (get p).2.book.trees.size) :
    ∀ p y, ocEnd get N₁ Mg₁ links ps p y → (get p).2.failed = none → (get p).2.st.codes = cs →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh →
      tabFirst arr (get p) w n = w.tab cs sh (arr j t) j t :=
  hbook_first cs arr get N₁ Mg₁ links ps h₂ h₃

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.words_tabFirst
#print axioms VerifiableInference.Desc.Sound.htab_first
#print axioms VerifiableInference.Desc.Sound.hbook_tabFirst
