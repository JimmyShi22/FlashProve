-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/KindAt355.lean: kind K13, the members' batching: closed facts on
the library's written list of the first chain's places at the full size (`P5J.At.ps`): the kind
stands at number 355 and nowhere else in that list; and which of two items are open at that border.
Statements with their proofs, four of them evaluations in Lean's kernel; no definition.

  `k13_kind_written`, `k13_ps_length`   the two evaluations beneath the next statement
  `k13_number_of_kind`   where the written list has a place of the kind K13, the number is 355. That
     number 355 is such a place is `m3_place` (FromThreadAt.lean of this folder)
  `m3_pinI_open`   the item "pinI" is open at the border number 355
  `m3_pileOne_shut`   the item "pileOne", which the row at 355 owes, is not open there: so the
     evaluation of "open at 355" can say no

Related: `ps_K13_one`, `ps_K13_some` (Found355.lean of this folder) say of the same list that every
place of the kind K13 on it is the kind's one place, and that there is one; they do not give the
number.

Limits.
  * The list is the proof file's first chain's, at the full size. Nothing is said of the shared
    chain, of the second chain or of the key file's description.
  * The four evaluations raise the depth of recursion (the option maxRecDepth).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (Item start)

set_option maxRecDepth 1000000 in
/-- Of the numbers below 358 none but 355 has, in the written list of places, a place of the kind
K13. By the kernel. -/
theorem k13_kind_written :
    ((List.range 358).all fun b =>
      match P5J.At.ps[b]? with
      | some p => p.kind != KindName.K13 || b == 355
      | none => true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written list has 358 places. By the kernel. -/
theorem k13_ps_length : P5J.At.ps.length = 358 := by
  decide +kernel

/-- **Where the written list has a place of the kind K13, the number is 355.** -/
theorem k13_number_of_kind {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K13) : b = 355 := by
  have hb : b < 358 := by
    rw [← k13_ps_length]
    exact (List.getElem?_eq_some_iff.1 hp).1
  have q := List.all_eq_true.1 k13_kind_written b (List.mem_range.2 hb)
  rw [hp] at q
  have q' : (p.kind != KindName.K13 || b == 355) = true := q
  rw [hk] at q'
  simpa using q'

set_option maxRecDepth 100000 in
/-- The item "pinI" is open at the border number 355. By the kernel. -/
theorem m3_pinI_open :
    Item.pinI ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 355 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The item "pileOne", which the row at 355 owes, is not open there. By the kernel. -/
theorem m3_pileOne_shut :
    decide (Item.pileOne ∈
      fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 355) = false := by
  decide +kernel

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_kind_written
#print axioms ProofFile.Honest.K13.k13_ps_length
#print axioms ProofFile.Honest.K13.k13_number_of_kind
#print axioms ProofFile.Honest.K13.m3_pinI_open
#print axioms ProofFile.Honest.K13.m3_pileOne_shut
