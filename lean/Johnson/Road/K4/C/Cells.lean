-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Cells.lean: DEFINITIONS OF HYPOTHESES, and one statement with its proof.

Not shown here. That an input's cells are the entries of the matrices of which a law speaks; that a
list of points is a part of another. CellsOn has an example by its own text (cellsOn_self: the
matrices that are made of the cells); of CellsAre and PtsPart at a run no example is known.
No property is claimed.

Three hypotheses that the laws of this folder share. They tie what the honest side of the
sub-protocol K4 reads (Johnson/Desc/K4/Honest/Front.lean: K4In.cell; a list of named points) to the
library's notation for the same things (Johnson/Road/FormsKeysMat.lean: Mats; the verifier's list
of points, pointsOf, OnBytes/Model/Layer.lean).

  CellsOn    on the matrices that G names, inside their rows and columns, the matrices' entries are
             the input's cells, read in the field.
  CellsAre   the same on every matrix of the segment's list but the matrix of the lookup's planes.
  PtsPart    whatever the first list holds under a name, the second holds under that name.
  cellsOn_self   the matrices that are made of the cells meet CellsOn.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Road.FormsKeysMat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (matIx)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In matsOf)

/-- **On the matrices that G names the entries are the input's cells.** mats: the rows and the
columns of each matrix. This defines a hypothesis; the definition claims nothing. -/
def CellsOn (G : ℕ → Prop) (mats : Array (ℕ × ℕ)) (cell : ℕ → ℕ → ℕ → F) (Mm : Mats Cb.Gl.E) :
    Prop :=
  ∀ i, G i → ∀ r c, r < (mats.getD i (0, 0)).1 → c < (mats.getD i (0, 0)).2 →
    Mm i r c = Reading.gl.val (ofF (cell i r c))

/-- **The same on every matrix but that of the lookup's planes.** This defines a hypothesis; the
definition claims nothing. -/
def CellsAre (Q : K4Pub) (w : K4In) (Mm : Mats Cb.Gl.E) : Prop :=
  CellsOn (fun i => i ≠ (matIx Q.P.y).iB) (matsOf Q) w.cell Mm

/-- **Whatever the first list holds under a name, the second holds under that name.** This defines a
hypothesis; the definition claims nothing. -/
def PtsPart (pt pts : List (String × Array E)) : Prop :=
  ∀ n p, (pt.find? fun q => q.1 == n) = some p → (pts.find? fun q => q.1 == n) = some p

/-- An example: the matrices that are made of the cells. -/
theorem cellsOn_self (G : ℕ → Prop) (mats : Array (ℕ × ℕ)) (cell : ℕ → ℕ → ℕ → F) :
    CellsOn G mats cell fun i r c => Reading.gl.val (ofF (cell i r c)) :=
  fun _ _ _ _ _ _ => rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.cellsOn_self
