-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/Sane.lean: the row claim_read_same_index over declarations, with the two
conditions that are owed beside it, under one name.

Why. `ClaimByDecls` (Reads/DeclRow.lean) is the form in which the row is to be shown. Alone it can
be met idly (`decl_dead`, `decl_free_val_member`, Reads/TeethMore.lean [not in this library]).
Letters without a state
with closed tables meet it. At a map val that is no reading's, a text that does wrong meets it. So
`NotEmpty` and `IsReading` (Reads/Stated.lean) are owed beside it. Whoever shows the row of a
description is to show the three together.

What is here.
  `ClaimSane L decls`: `ClaimByDecls L decls`, `NotEmpty L` and `IsReading L`. It is to speak of the
    one written description at the release's plan; here it is a statement over letters.
  `sane_gives`: it gives `ClaimReadSameIndex L`, `NotEmpty L` and `IsReading L`. A tool.
  `ne_of_notEmpty`: where the letters are not empty, 1 ≠ 0 in K. A tool.

Toys that meet the statement and toys at which it fails are in
Reads/TeethMore.lean [not in this library].

Limits. As in Reads/Stated.lean and Reads/DeclRow.lean: the letters are free, and the statement is
worth what their making is worth. It is proved of no description. Nothing on soundness.


-/
import Johnson.Desc.Reads.DeclRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open OnBytes (E)

variable {K : Type} [CommRing K]

/-- **claim_read_same_index over declarations, with what is owed beside it.** The row over
declarations; the letters are not empty; the letter val is a reading's map. -/
def ClaimSane (L : Letters K) (decls : L.Link → L.State → List (ReadDecl E)) : Prop :=
  ClaimByDecls L decls ∧ NotEmpty L ∧ IsReading L

/-- It gives the row of Reads/Stated.lean with the same two conditions. -/
theorem sane_gives (L : Letters K) (decls : L.Link → L.State → List (ReadDecl E))
    (H : ClaimSane L decls) : ClaimReadSameIndex L ∧ NotEmpty L ∧ IsReading L :=
  ⟨claim_of_decls L decls H.1, H.2.1, H.2.2⟩

/-- Where the letters are not empty, 1 ≠ 0 in K: some form's part in U3 has a value that is not
0. -/
theorem ne_of_notEmpty (L : Letters K) (H : NotEmpty L) : (1 : K) ≠ 0 := by
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ H.1
  obtain ⟨s, -, f, -, v, hv⟩ := H.2 l hl
  intro h10
  refine hv ?_
  rw [← mul_one (u3Value L.val (L.iU3 l) (L.cols l) f v), h10, mul_zero]

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.sane_gives
#print axioms VerifiableInference.Reads.ne_of_notEmpty
