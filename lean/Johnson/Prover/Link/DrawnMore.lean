-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DrawnMore.lean: THE OTHER TWO PLACES THAT READ "elems.headD (0, 0, 0)" FOR A
CHALLENGE READ WHAT drawnOf | drawnE READ: pointW (Johnson/Prover/Link/TabOf.lean) and lastOut's own
(Johnson/Prover/Link/BodyAll.lean). So the laws of Johnson/Prover/Link/DrawnLaw.lean serve all four.
Statements and proofs.

  pointW_drawnOf   each coordinate of pointW is drawnOf of a round that sampled what D says
  toE_headD        the triple that lastOut hands to shownAll, read in the field as shownAll reads it
                   (toE), is drawnE

Not shown here. That a list is never empty where these are read. Nothing on what any value that is
sent discloses. Nothing on soundness or any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.DrawnLaw
import Johnson.Prover.Link.TabOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice

theorem pointW_drawnOf (D : ℕ → Fmt.Drawn) (o k : ℕ) :
    pointW D o k = (List.range k).map fun n => drawnOf ⟨[], D (o + 1 + n)⟩ := rfl

theorem toE_headD (d : Fmt.Drawn) : toE (d.elems.headD (0, 0, 0)) = drawnE d :=
  (readE_ofTriple _).symm

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.pointW_drawnOf
#print axioms Johnson.Prover.Link.toE_headD
