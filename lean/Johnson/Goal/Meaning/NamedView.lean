-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/NamedView.lean: THE TEST namedB (Johnson/Goal/Meaning/NamedAsk.lean) READS THE
PUBLIC PART THROUGH ITS SHAPE's VIEW ALONE (xShapeOf, Johnson/Desc/Ok/PlanWritten/XShape.lean): so
where the view and the request's layout are two written values, the test's accepting is one closed
fact. Definitions and theorems, proved.

  tailV V k, entryV t a   segment k's tail in the view (the empty one where the view has none), and
    an entry's label, rows and columns.
  namedV V layout   namedB's own text, read off the view.
  namedB_view   namedB X layout = namedV (xShapeOf X) layout: AT EVERY X AND EVERY layout: no
    premise.
  named_closed   xShapeOf Z.p.X = V, Z.first.layout = L, namedV V L = true: then namedAt Z = true.
    General in V and L.

OBJECT: namedB, namedAt.
LETTERS: V, L: free: no written value is named here.

What is not claimed. That namedV accepts at any V and L. Of the view, the lists of symbol arrays
(gtTree) and the head's part are not read. As at namedB: a segment at which no tail stands
contributes an empty list: the test is idle there, it does not reject. The full size alone (25
segments; linkK). No soundness.
-/
import Johnson.Goal.Meaning.NamedAsk
import Johnson.Desc.Ok.PlanWritten.XShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.NamedAsk

open OnBytes OnBytes.Model
open VerifiableInference.Desc (arrayOf)
open VerifiableInference.Desc.K3Asks (nMat symRowsAt colsAt)
open VerifiableInference.PlanWritten (XShape TailView tailView xShapeOf)

/-- Segment k's tail in the view; the empty one where the view has none. -/
def tailV (V : XShape) (k : Nat) : TailView := ((V.1[k]?).getD none).getD (0, [], [])

/-- Entry a of a tail's list in the view: label, rows, columns. -/
def entryV (t : TailView) (a : Nat) : Nat × Nat × Nat := t.2.1.getD a (0, 0, 0)

/-- **THE TEST, READ OFF THE VIEW.** -/
def namedV (V : XShape) (layout : Params.ReqLayout) : Bool :=
  (List.range 25).all fun k => (List.range (tailV V k).1).all fun a =>
    match arrayOf layout (linkK ((entryV (tailV V k) a).1 / 256))
        (nameK ((entryV (tailV V k) a).1 % 256)) with
    | none => false
    | some A => A.sizeI == ((entryV (tailV V k) a).2.1 + 2) / 3 &&
        A.sizeC == (entryV (tailV V k) a).2.2

theorem all_range_congr {n : Nat} {f g : Nat → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).all f = (List.range n).all g := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun H k hk => (h k hk) ▸ H k hk, fun H k hk => (h k hk).symm ▸ H k hk⟩

/-- Below 25 the view's tail is the view of the plan's. -/
theorem tailV_at (X : Verify.Public) {k : Nat} (hk : k < 25) :
    tailV (xShapeOf X) k = tailView (tlK X k) := by
  unfold tailV xShapeOf tlK
  simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
  cases VerifiableInference.Desc.First.Look.tlAt X k <;> rfl

/-- An entry of the view is the entry's three numbers. -/
theorem entryV_at (t : HTailF2) (a : Nat) :
    entryV (tailView t) a =
      ((t.mats.getD a {}).aId, (t.mats.getD a {}).m, (t.mats.getD a {}).k) := by
  unfold entryV tailView
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases t.mats[a]? <;> rfl

/-- **THE TEST READS THE PUBLIC PART THROUGH THE VIEW ALONE**: at every public part and layout. -/
theorem namedB_view (X : Verify.Public) (layout : Params.ReqLayout) :
    namedB X layout = namedV (xShapeOf X) layout := by
  unfold namedB namedV
  refine all_range_congr fun k hk => ?_
  rw [tailV_at X hk]
  have e1 : (tailView (tlK X k)).1 = nMat (tlK X k) := rfl
  rw [e1]
  refine all_range_congr fun a _ => ?_
  rw [entryV_at]
  rfl

/-- **FROM TWO PINS AND ONE CLOSED FACT.** -/
theorem named_closed {Z : ProofFile.Pub} {V : XShape} {L : Params.ReqLayout}
    (hx : xShapeOf Z.p.X = V) (hl : Z.first.layout = L) (hv : namedV V L = true) :
    namedAt Z = true := by
  unfold namedAt
  rw [namedB_view, hx, hl]
  exact hv

end Meaning.NamedAsk

#print axioms Meaning.NamedAsk.namedB_view
#print axioms Meaning.NamedAsk.named_closed
