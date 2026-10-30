-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RidesRows.lean: THE SECOND CUT: OF THE SIXTEEN ITEMS OF THE
MERGE's FIFTH TIE (RidesAtMerge.lean) SIX RIDE BACK AT THE COMPOSED MEANING: the five
classes of rows and the pile. Theorems with their proofs.

  classRows_same   the rows of a class are read off the statement and the book of trees alone
  row_back         **"row m c"**, every m and c: across the merge's accepting step, both ways
  pile_back        **"pile"**: likewise
  six_back         the six of the sixteen, in the fifth tie's letters

Why they ride. At mgAll the sentence "row m c" reads the verifier's state's statement and book
(rowSays at wordsAtFirst); "pile" reads these and the pending rows (RowsTrue at rwBook; S.rows is
out.pending wherever the state does not stand at the chain's end). The merge's accepting step
leaves statement, book and out (leavesSeven) and stands in the head's part on both sides. The
oracles' strings are read by neither.

Limits. Ten of the sixteen are not here: the six runs of forms, the two sentences "worth", the two
pins. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Top.H0.MergeLaw.Law
import Johnson.Top.H0.MergeLaw.Says
import Johnson.Top.H0.MergeLaw.RidesAtMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Sound (MgData mgAll mgAll_row mgAll_pile CellsQ MsgT meansQ Frame)
open VerifiableInference.Desc.First (S Item RowClass Numbers Meaning classRows)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- The rows of a class are read off the statement and the book alone. -/
theorem classRows_same (N : Numbers) (m : ℕ) (c : RowClass) {s s' : S} (h1 : s'.st = s.st)
    (h2 : s'.book = s.book) : classRows N m c s' = classRows N m c s := by
  unfold classRows
  rw [h1, h2]

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {Pm : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView} (h : headMergeDecide Pm s rs = .ok s')
include h

/-- **"row m c" across the merge's accepting step.** -/
theorem row_back (m : ℕ) (c : RowClass) (z : P) (y y' : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).row m c (z, s') y' w ↔ (mgAll 𝔇 Mg).row m c (z, s) y w := by
  obtain ⟨h1, h2, _⟩ := leavesSeven Pm s rs [] s' h
  rw [mgAll_row]
  show OnBytes.Means.AllSay _ s'.st (classRows 𝔇.N m c s')
      (Sound.wordsFirst 𝔇.arr s'.st s'.book w) ↔
    OnBytes.Means.AllSay _ s.st (classRows 𝔇.N m c s) (Sound.wordsFirst 𝔇.arr s.st s.book w)
  rw [classRows_same 𝔇.N m c h1 h2, h1, h2]

/-- **"pile" across the merge's accepting step.** -/
theorem pile_back (z : P) (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).pile (z, s') y' w ↔ (mgAll 𝔇 Mg).pile (z, s) y w := by
  obtain ⟨h1, h2, _, _, _, h6, _⟩ := leavesSeven Pm s rs [] s' h
  obtain ⟨a, a', _, _, _, _, _, ha, ha', _⟩ := decide_inv h
  have hr : s'.rows = s.rows := by
    unfold S.rows
    rw [ha, ha', h6]
  have hw : K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, s') w = K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, s) w := by
    unfold K13.Law.rwBook
    show (⟨_, K13.Law.maskCut s'.st (Sound.wordsFirst 𝔇.arr s'.st s'.book w)⟩ : K13.Law.Wit _ _ _) =
      ⟨_, K13.Law.maskCut s.st (Sound.wordsFirst 𝔇.arr s.st s.book w)⟩
    rw [h1, h2]
  rw [mgAll_pile]
  show (∀ r ∈ s'.rows, K13.Law.Holds _ (K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, s') w) r) ↔
    ∀ r ∈ s.rows, K13.Law.Holds _ (K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, s) w) r
  rw [hr, hw]

end

/-- **The six of the sixteen, in the fifth tie's letters**: "pile", and "row m c" at every class. -/
theorem six_back {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    {Pm : HeadMergeP} {Fr : Frame} (N : Numbers) (z : P) (a b : S × Fr.E.Str)
    (h : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) (w : Wit (CellsQ rows cols) Tok MsgT)
    (i : Item) (hi : i = .pile ∨ ∃ m c, i = .row m c)
    (hb : meansQ N (mgAll 𝔇 Mg) (fun s => (z, s)) i b w) :
    meansQ N (mgAll 𝔇 Mg) (fun s => (z, s)) i a w := by
  obtain ⟨rs, h⟩ := h
  rcases hi with rfl | ⟨m, c, rfl⟩
  · exact (pile_back 𝔇 Mg h z _ _ w).1 hb
  · exact (row_back 𝔇 Mg h m c z _ _ w).1 hb

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.six_back
#print axioms VerifiableInference.Desc.First.MergeLaw.row_back
#print axioms VerifiableInference.Desc.First.MergeLaw.pile_back
