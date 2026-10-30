-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/BatCatchesProof.lean: the batching's converse at a proximity test's own batching,
in the form of Johnson/Desc/K12/Law/BatJoint.lean.

Johnson/Desc/K12/Law/BatJoint.lean states, and proves nothing: if no witness whose encoding is
within e positions of the word y holds words of which all the rows hold (NoneNear), then the values
of the drawn element at which the batched claim has a witness (BadDraws) are at most lst times one
less than the number of rows (BatCatches), lst a bound on the list of witnesses within e of y. This
file proves it (batCatchesAt : BatCatchesAt), and the stronger form without the three premises that
the proof does not spend (batCatches_bare).

The road. The witnesses within e of y are a finite family, at most lst by ListAt at y, and stand in
front of the drawn element. A witness's tables hold, on the blocks, the words that are read off them
(laidOn_wordsOf: of all tables). rIn_iff turns a witness of the relation at the batched claim into
"near, and the batched row holds of the witness's tables". catches_list (CatchesList.lean)
bounds the count.

Main theorems: laidOn_wordsOf, batCatches_bare, batCatchesAt.

What is not claimed. The game's form and the reading of the draw. That ListAt holds at a radius.
Nothing on the word y. Nothing on soundness.
-/
import Johnson.Desc.K12.Law.BatJoint
import Johnson.Desc.Means.CatchesList

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open OnBytes.Means

/-- All tables hold, on the blocks, the words that are read off them. -/
theorem laidOn_wordsOf (S : Statement) (L : GroupLayout) (T : Tables GE) :
    LaidOn S L (wordsOf S L T) T where
  main_at := fun o i first hf hk hm idx _ => by
    simp only [wordsOf, hf, hk, hm, Bool.false_eq_true, if_false]
  mask_at := fun o i first hf hm idx _ => by
    simp only [wordsOf, hf, hm]
  kept_at := fun o i hf hk idx _ => by
    simp only [wordsOf, hf, hk, if_true]

/-- The batching's converse, without the three premises that nothing spends. -/
theorem batCatches_bare (s : Sg) (e lst : ℕ) (S' : Statement) (g : Nat) (L : GroupLayout)
    (rows : Array Row) (y : s.cIn.Word) (hlist : s.cIn.ListAt e lst)
    (ht : combineAt S' g ⟨L, rows⟩ = true)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l)
    (hz : 2 ^ L.logEllZk = s.Z.l) : BatCatches s e lst S' g L rows y := by
  intro hnone
  obtain ⟨G, hG, hL, hOk, hr⟩ := combineAt_gives ht
  have h1 := catches_list rdE (W := s.cIn.N.Wit)
    (fun w => offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e) lst (hlist y)
    (fun w => tabOf s w.1) (fun w => wordsOf S' L (tabOf s w.1)) S' g G L rows hG hL hOk hr
    (fun w _ => laidOn_wordsOf S' L _) hnone
  refine le_trans (cnt_mono fun θ hθ => ?_) h1
  obtain ⟨x, row, e1, e2, e3, w, hw⟩ := hθ
  obtain ⟨hnear, hsays⟩ := (rIn_iff s S' L row e y w hk hh hl hz e3).1 hw
  exact ⟨x, row, w, e1, e2, hnear, hsays⟩

theorem batCatchesAt : BatCatchesAt :=
  fun s e lst S' g L rows y _ _ hlist ht hk hh hl hz _ =>
    batCatches_bare s e lst S' g L rows y hlist ht hk hh hl hz

end H2K.ClaimSays

#print axioms H2K.ClaimSays.batCatches_bare
#print axioms H2K.ClaimSays.batCatchesAt
