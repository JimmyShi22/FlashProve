-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/HpileAt9.lean: THE NAMED PREMISE hpile OF THE LAW AT THE SHARED CHAIN's
FIRST POINT (K14's files'; read in a text of this project that is not in this repository: "one
direction, fenced"), AT THE COMPOSED FILLING `mgAll 𝔇 Mg` (Johnson/Desc/Sound/MgAll.lean).
One statement with its proof: a call of `hpile_at` (Johnson/Desc/K13/Law/PileOneJoint.lean).
  `hpile_at9`: at every p that a condition R admits whose state bears no mark: the plain reader's
  "all rows on the table are true" gives `(mgAll 𝔇 Mg).pileOne`. THREE PREMISES: hn: the data's
    number of rows is the kind's numbers' `matrixRows`; hmat: the data's matrix is the one by
    numbers; hW: R gives "K13.pileWithin"'s test. The clause "the promise at the chain's end
    holds" of that premise is not spent: so it is not asked.
What is not claimed. hn, hmat, hW at any data or condition. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.K13.Law.PileOneJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll CellsQ tabAt seatBy noFirst)
open VerifiableInference.Desc.K13 (pileWithinC)
open VerifiableInference.Desc.K13.Law (RowsTrue witOf matBy hpile_at)

/-- **hpile at the composed filling.** -/
theorem hpile_at9 {Xi P Tok P₁ : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    (matC : CellsQ rows cols → ℕ → ℕ → GE) (hn : 𝔇.P13.lin.matrixRows = nR)
    (hmat : ∀ c, 𝔇.mat13 c = matBy 𝔇.P13.lin.kCol (matC c)) (get : P₁ → P × S) (R : P₁ → Prop)
    (hW : ∀ p, R p → (get p).2.failed = none → pileWithinC (get p).2 = true) :
    ∀ p y w, R p → (get p).2.failed = none →
      RowsTrue (nR := 𝔇.P13.lin.matrixRows) (k := 𝔇.P13.lin.kCol)
        (fun w' : Wit (CellsQ rows cols) Tok MsgT =>
          witOf (matBy 𝔇.P13.lin.kCol (matC w'.cells))
            (wordsOn (get p).2.st
              (tabAt (get p).2.st.codes 𝔇.arr (seatBy noFirst (get p).2.book) (get p).2.st w')))
        (get p).2 w → (mgAll 𝔇 Mg).pileOne (get p) y w :=
  hpile_at 𝔇.arr hn 𝔇.mat13 matC (fun _ _ _ => Iff.rfl) hmat get R (fun a => a.2.st)
    (fun a w => tabAt a.2.st.codes 𝔇.arr (seatBy noFirst a.2.book) a.2.st w) (fun _ => rfl)
    (fun _ _ => rfl) hW

end HashBuild
