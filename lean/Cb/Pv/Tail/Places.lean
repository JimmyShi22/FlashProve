-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Tail/Places.lean: from a place of the vector of reads to the read that stands there.

Cb/Pv/Tail/Tables.lean turns tables into reads: segment sg of table number n at column c stands at
the place `start + c * (m / len) + sg` of the vector of reads. A frame that names the late entries
by their places in that vector needs the way back (the map `it` of Cb/Pv/Tail/InLink.lean).

Main names:
  `Named t pos`: some table, column and segment stand at the place pos.
  `JU t N`: the places below N that are named.
  `itU`: a read at a column that stands at a named place.
  `htab_places`: the entry of the vector at a named place is the value of that read at that column:
    the third law of Cb/Pv/Tail/InLink.lean, at the vector's own places.

Limits: `itU` is found by choice. Nothing here says that only one table, column and segment stand at
a place, or that every place below N is named: neither is needed for the law.

Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.Claims
import Cb.Pv.Tail.Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail

/-- Some table, column and segment stand at the place pos of the vector of reads. -/
def Named (t : TSize) (pos : ℕ) : Prop :=
  ∃ (n : ℕ) (T : Tab) (c sg : ℕ), t.tabs[n]? = some T ∧ T.mat < t.NM ∧ c < t.k T.mat ∧
    sg < t.m T.mat / T.len ∧ pos = T.start + c * (t.m T.mat / T.len) + sg

/-- The places below N that are named. -/
abbrev JU (t : TSize) (N : ℕ) : Type := {pos : Fin N // Named t pos}

noncomputable instance (t : TSize) (N : ℕ) : Fintype (JU t N) := Fintype.ofFinite _

/-- A read at a column that stands at a named place. -/
noncomputable def itU {t : TSize} {N : ℕ} (j : JU t N) : JTab t.size :=
  ⟨⟨j.2.choose_spec.choose.mat, j.2.choose_spec.choose_spec.choose_spec.choose_spec.2.1⟩,
    ⟨t.enc j.2.choose_spec.choose.mat j.2.choose
        j.2.choose_spec.choose_spec.choose_spec.choose,
      t.enc_lt j.2.choose_spec.choose_spec.choose_spec.choose_spec.1
        j.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1⟩,
    ⟨j.2.choose_spec.choose_spec.choose,
      j.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1⟩⟩

/-- The entry at a named place is the value of the read that stands there. -/
theorem htab_places {K : Type} [CommRing K] {t : TSize} {N : ℕ} (u3 : ℕ → K) (j : JU t N) :
    u3 j.1 = tabOf t u3 (itU j).1 (itU j).2.1 (itU j).2.2 := by
  have h := j.2.choose_spec.choose_spec.choose_spec.choose_spec
  show u3 j.1 = tabOf t u3 j.2.choose_spec.choose.mat
    (t.enc j.2.choose_spec.choose.mat j.2.choose j.2.choose_spec.choose_spec.choose_spec.choose)
    j.2.choose_spec.choose_spec.choose
  unfold tabOf
  rw [t.dec_enc h.1 rfl h.2.2.2.1]
  exact congrArg u3 h.2.2.2.2

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.htab_places
