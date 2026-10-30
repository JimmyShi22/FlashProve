-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PileOneJoint.lean: TWO SENTENCES "all rows on the table are true" ARE ONE
WHEREVER EVERY MASK ENTRY THAT A ROW NAMES LIES WITHIN ITS TABLE: ours, at the reader whose mask
entries are CUT TO THE TABLE (`rwBook`, Johnson/Desc/K13/Law/ReaderByBook.lean: what our layer
`fillK13` lays at `pile` and `pileOne`), and the one at the plain reader (`witOf` … `wordsOn`:
what the structure `JointSays`, Johnson/Desc/Sound/PointAtLayers.lean, asks at
`pileOne`). Statements with their proofs. Why. `JointSays.pileOne` is an EQUATION OF FUNCTIONS,
over every state and witness. At the composed filling it does not close: at a state one of whose
rows names a mask entry beyond its table the cut reader answers 0 and the plain one the words' own
entry. Inside the fact "K13.pileWithin" the two agree.
  `rowsTrue_cut`: the two at one matrix, WHERE `rowsWithinC s = true`: row by row, by `cutSame`
    (Johnson/Desc/K13/Law/CutSame.lean).
  `pileOne_joint`: **in `JointSays.pileOne`'s own letters**: at stOf₁ a := a.2.st and tabP₁ a w :=
  the table through the state's own book; WHERE `pileWithinC a.2 = true` and the matrix is the one
    by numbers (hmat: an equation on a letter of the filling's data; at `matOfCells` it is by the
    make).
  `hpile_of`: ONE DIRECTION, FENCED: from the plain reader's sentence to the filling's own
  `pileOne`, at every p that a condition R admits whose state bears no mark: WHERE R gives
  `pileWithinC`: the form that was chosen in the equation's place.
What is not claimed. That the equation of functions is false: no state is exhibited here. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.CutSame
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.K13.Law.StepBack
import Johnson.Desc.K13.Law.FillK13Laws
import Johnson.Desc.Sound.WordsAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (Words wordsOn tableSize)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT wordsFirst tabAt seatBy noFirst)

section
variable {Pp Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)

/-- The test says what it says. -/
theorem rowsWithinC_says (s : S) : rowsWithinC s = true ↔
    ∀ r ∈ s.rows, ∀ t ∈ r.masks, t.1.index < tableSize s.st t.1.oracle .mask := by
  unfold rowsWithinC
  simp only [List.all_eq_true, decide_eq_true_eq, tableSizeC_eq]

/-- **The cut reader and the plain one**, at one matrix. -/
theorem rowsTrue_cut (mat : Cells → Fin nR → (Fin k → Bool) → GE) (x : Pp × S)
    (w : Desc.Wit Cells Tok MsgT) (h : rowsWithinC x.2 = true) :
    RowsTrue (rwBook arr mat x) x.2 w ↔
      RowsTrue (fun w' : Desc.Wit Cells Tok MsgT =>
        witOf (mat w'.cells) (wordsFirst arr x.2.st x.2.book w')) x.2 w := by
  have hw := (rowsWithinC_says x.2).1 h
  unfold RowsTrue
  exact forall₂_congr fun r hr => cutSame x.2.st _ (mat w.cells) r (hw r hr)

/-- **In the other structure's own letters.** -/
theorem pileOne_joint (mat : Cells → Fin nR → (Fin k → Bool) → GE) (matC : Cells → ℕ → ℕ → GE)
    (hmat : ∀ c, mat c = matBy k (matC c)) (a : Pp × S) (w : Desc.Wit Cells Tok MsgT)
    (h : pileWithinC a.2 = true) :
    RowsTrue (rwBook arr mat a) a.2 w ↔
      RowsTrue (nR := nR) (k := k) (fun w' : Desc.Wit Cells Tok MsgT =>
        witOf (matBy k (matC w'.cells))
          (wordsOn a.2.st (tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w'))) a.2 w := by
  have hr : rowsWithinC a.2 = true := by
    unfold pileWithinC at h
    exact (Bool.and_eq_true _ _ ▸ h).2
  rw [rowsTrue_cut arr mat a w hr]
  unfold RowsTrue
  show (∀ r ∈ a.2.rows, Holds ρg (witOf (mat w.cells) (wordsFirst arr a.2.st a.2.book w)) r) ↔ _
  rw [hmat w.cells]
  rfl

/-- **ONE DIRECTION, FENCED: what the law at the shared chain's first point asks of kind K13's
files** (its named premise hpile, but for the clauses that are not spent): at a filling whose
`pileOne` is our layer's; stOf₁ and tabP₁: that law's letters, with what they are at the first
chain's state. -/
theorem hpile_of {P₁ : Type} {Mg : First.Meaning Pp (Desc.Wit Cells Tok MsgT)}
    (mat : Cells → Fin nR → (Fin k → Bool) → GE) (matC : Cells → ℕ → ℕ → GE)
    (hM : ∀ x y w, Mg.pileOne x y w ↔ RowsTrue (rwBook arr mat x) x.2 w)
    (hmat : ∀ c, mat c = matBy k (matC c)) (get : P₁ → Pp × S) (R : P₁ → Prop)
    (stOf₁ : Pp × S → Statement) (tabP₁ : Pp × S → Desc.Wit Cells Tok MsgT → ℕ → MsgT)
    (hst : ∀ a, stOf₁ a = a.2.st)
    (htab : ∀ a w, tabP₁ a w = tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w)
    (hW : ∀ p, R p → (get p).2.failed = none → pileWithinC (get p).2 = true) :
    ∀ p y w, R p → (get p).2.failed = none →
      RowsTrue (nR := nR) (k := k) (fun w' : Desc.Wit Cells Tok MsgT =>
        witOf (matBy k (matC w'.cells)) (wordsOn (stOf₁ (get p)) (tabP₁ (get p) w')))
        (get p).2 w → Mg.pileOne (get p) y w := by
  intro p y w hr hm h
  refine (hM _ y w).2 ((pileOne_joint arr mat matC hmat (get p) w (hW p hr hm)).2 ?_)
  unfold RowsTrue at h ⊢
  intro r hrow
  have h1 : Holds ρg (witOf (matBy k (matC w.cells))
      (wordsOn (stOf₁ (get p)) (tabP₁ (get p) w))) r := h r hrow
  rw [hst, htab] at h1
  exact h1

/-- The same where the plain reader's number of rows is written otherwise: n' with n' = nR. -/
theorem hpile_at {P₁ : Type} {Mg : First.Meaning Pp (Desc.Wit Cells Tok MsgT)} {n' : ℕ}
    (he : n' = nR) (mat : Cells → Fin nR → (Fin k → Bool) → GE) (matC : Cells → ℕ → ℕ → GE)
    (hM : ∀ x y w, Mg.pileOne x y w ↔ RowsTrue (rwBook arr mat x) x.2 w)
    (hmat : ∀ c, mat c = matBy k (matC c)) (get : P₁ → Pp × S) (R : P₁ → Prop)
    (stOf₁ : Pp × S → Statement) (tabP₁ : Pp × S → Desc.Wit Cells Tok MsgT → ℕ → MsgT)
    (hst : ∀ a, stOf₁ a = a.2.st)
    (htab : ∀ a w, tabP₁ a w = tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w)
    (hW : ∀ p, R p → (get p).2.failed = none → pileWithinC (get p).2 = true) :
    ∀ p y w, R p → (get p).2.failed = none →
      RowsTrue (nR := n') (k := k) (fun w' : Desc.Wit Cells Tok MsgT =>
        witOf (matBy k (matC w'.cells)) (wordsOn (stOf₁ (get p)) (tabP₁ (get p) w')))
        (get p).2 w → Mg.pileOne (get p) y w := by
  subst he
  exact hpile_of arr mat matC hM hmat get R stOf₁ tabP₁ hst htab hW

end

end VerifiableInference.Desc.K13.Law
