-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/ReadsTie.lean

The vector of reads of an honest prover meets the third clause of the smallness test's tie, for any
list of tables.

The smallness test ties the reads to the cells. The third clause of that tie, as
Johnson/Desc/Kinds/Law/TieReads.lean spells it ("TieThird tl u3 A a"): at every place that a table
of tl's closed list names, row 0 of the array u3 in the table of cells A holds the sum of the
table's stretch of the integers a under the table's weights, read by "Reading.gl".

Main theorems:
* "gl_ofInt": "Reading.gl" reads the program's image of an integer as the integer's image.
* "tieThird_sent": if p has the sizes of tl's matrices, tl's tables end at or below n and no entry
  lies in two of them, and row 0 of the array u3 of A holds, below n, "readAt" at tl's tables and
  the integers cell, read by "Reading.gl": then "TieThird tl u3 A cell".

Limits. As in Johnson/HonestTrace/Reads.lean. One clause of the tie: nothing on its clauses on the
matrices' packed arrays and on the integers' size.

Ground. This file imports Johnson/Desc/K8/Honest/Arrays.lean, through
Johnson/HonestTrace/Reads.lean: it can be built only where the files under Johnson/Desc/K8/Honest/
lie.

Not claimed: that a verifier accepts a proof made of these entries (completeness of the protocol);
anything on soundness or on what a proof shows of the cells.
-/
import Johnson.HonestTrace.Reads
import Johnson.Road.FormsKeysQK
import Johnson.Desc.Kinds.Law.TieReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (CellsAt)

local notation "readAtP" => VerifiableInference.Desc.First.K8.Honest.readAt

/-- The reading "Reading.gl" reads integers as integers. -/
theorem gl_ofInt (z : ℤ) : Reading.gl.val (ofInt z) = (z : Cb.Gl.E) := Road.gl_numerals.ofInt z

/-- **The third clause of the smallness test's tie at the honest vector.** "Honest" says how the
vector is made of the integers; these are any. -/
theorem tieThird_sent {p : Par} {tl : HTailF2} {n : ℕ} (P : ParFits p tl.mats)
    (L : TablesLie tl.mats tl.funs n) {cell : CellsAt} {u3 : ℕ} {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (S : ∀ i < n, A u3 0 i = Reading.gl.val (readAtP p tl.funs.toList cell i)) :
    VerifiableInference.Desc.Kinds.Head.Law.TieThird tl u3 A cell := by
  intro k Fn hk c sg pos hp
  have H := holds_sent Reading.gl gl_ofInt P L (cell := cell)
    (W := ⟨fun _ => 0, fun a _ i => A a 0 i⟩) (iU3 := u3) (K3 := 0) (fun i hi => by
      show A u3 0 (i % 0) = _
      rw [Nat.mod_zero, S i hi])
  have e2 : A u3 0 (pos % 0) = _ := H Fn (Array.mem_of_getElem? hk) c sg pos hp
  rw [Nat.mod_zero] at e2
  exact e2

#print axioms gl_ofInt
#print axioms tieThird_sent

end OnBytes.HonestTrace
