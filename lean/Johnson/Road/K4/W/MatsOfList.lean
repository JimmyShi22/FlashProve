-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/MatsOfList.lean: CONDITIONAL.

Not shown here. `DataIsList` FORCES THE LIST L TO BE 0 OUTSIDE THE SIZES OF THE SUB-PROOF's PLAN tl:
nothing here ties tl to any public parameters. (Of tl it reads the number of matrices, their rows
and columns, and which array holds a matrix's symbols; the radix 2 ^ 20 and the shift 2 ^ 17 are the
library's constants at every tl.) THAT THE SYMBOLS WHICH ANY DATA HOLD ARE THE PACKING OF ANY LIST
OF INTEGERS: `DataIsList` is a hypothesis, and it is the whole content: at a run's data no example
is known. Which list of names, which plan and which data a caller lays is the caller's. Nothing on
soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import: no module under
Johnson/Goal/, Johnson/D/ or ThirdParty/, and none whose name holds RecCompile. It imports nothing
of the honest side (Johnson/Desc/ProofFile/Honest/).

The matrices that are unpacked from the data's symbols (`matsOfData`,
Johnson/Desc/Sound/DataMats.lean) are the images of a list of integer matrices AT EVERY TRIPLE OF
INDICES, IN RANGE OR NOT, where the symbols are that list's packing: both sides are 0 outside the
sizes by the way they are made, so no hypothesis "in range" is asked. Definitions, and statements
with their proofs: unfolding, and one call of the library's `matsOf_base`
(Johnson/Road/Rows/LayerStart.lean). General in the sizes: nothing here is at the full size alone.

  `matsOfData_matsOf`   `matsOfData` is the library's `matsOf` at the cells that are read off the
      data's symbols: the two texts test the same three bounds.
  `DataIsList tl names Dt L`   there are small integers whose packing the data's symbols are
      (`BaseAt`, Cb/Pv/Tail/Base.lean), and, laid as matrices on all numbers (`mzTot`), they are L.
  `mats_of_list`   **so `matsOfData tl names Dt = castM L`.**
  `cells_of_list`   so the library's cells read off the two are the same, at every layout and size:
      the hypothesis hC of W/IdnOfField.lean.
-/
import Johnson.Desc.Sound.DataMats
import Johnson.Road.Rows.LayerStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay)
open OnBytes.Road.Rows.Norms (matsOf mzTot matsOf_base castM)
open Cb.Pv.Tail (BaseAt cellValS)
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.First.Look (cellJ szOf)
open VerifiableInference.Desc.Sound (GQ matsOfData symOfData)

variable {tl : HTailF2} {names : Array (ℕ × String)} {Dt : Bound GQ} {L : Mats ℤ}

/-- `matsOfData` is the library's `matsOf` at the cells read off the data's symbols. -/
theorem matsOfData_matsOf (tl : HTailF2) (names : Array (ℕ × String)) (Dt : Bound GQ) :
    matsOfData tl names Dt =
      matsOf (s := szOf tl)
        (Sum.elim (fun _ : Unit => (0 : GQ)) (cellValS (symOfData tl names Dt))) := by
  funext a r c
  unfold matsOfData matsOf cellJ
  by_cases h : a < (szOf tl).NM
  · by_cases hc : c < (szOf tl).k a
    · by_cases hr : r < (szOf tl).m a
      · simp [h, hc, hr]
      · simp [h, hc, hr]
    · simp [h, hc]
  · simp [h]

/-- **The data's symbols are the packing of the list L.** This defines a hypothesis; the definition
claims nothing. -/
def DataIsList (tl : HTailF2) (names : Array (ℕ × String)) (Dt : Bound GQ) (L : Mats ℤ) : Prop :=
  ∃ Mz, BaseAt (symOfData tl names Dt) Mz ∧ mzTot Mz = L

/-- **The matrices off the data are the images of the list, at every triple of indices.**
CONDITIONAL: on h. -/
theorem mats_of_list (h : DataIsList tl names Dt L) : matsOfData tl names Dt = castM L := by
  obtain ⟨Mz, hB, rfl⟩ := h
  rw [matsOfData_matsOf, matsOf_base hB]
  rfl

/-- **The library's cells read off the two are the same.** CONDITIONAL: on h. -/
theorem cells_of_list (h : DataIsList tl names Dt L) (D : Dim) (y : Lay) :
    cellsOf D (cellsAt y (matsOfData tl names Dt)) = cellsOf D (cellsAt y (castM L)) := by
  rw [mats_of_list h]

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.matsOfData_matsOf
#print axioms OnBytes.Road.K4.W.mats_of_list
#print axioms OnBytes.Road.K4.W.cells_of_list
