-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowsMembers.lean: the claims that the seven sumchecks of a layers' sub-proof
themselves leave (their own rows) are members of the lists that K4's two runs return.

  `gatedForms_rows`: the two product layers' own rows are members of the gated products' group.
  `front_rows`: where the run "front" returns (fs, G): the own rows of the squares' product layer
    and of the two product layers of the gated products are members of fs; and so is the own row of
    the token sumcheck of the row products, which the run makes itself: it is what ownClaim returns
    at the ledger in front, on the summand at the values that this ledger shows.
  `back_rows`: where the run "back" returns (fs, G): the batched sumcheck's own row o.K.rowS is a
    member of fs; and so is the merge's own row, which the run makes itself by ownClaim at the
    ledger in front; G is the ledger that ownClaim leaves, with the join's debt paid.
Limits. From a return. Memberships of lists and equations on ledgers: nothing on what a form is
worth, on a world, on a draw, on soundness or on hiding. The sumcheck of the terms leaves no own row
in these lists.


-/
import OnBytes.Desc.First.K4.ClaimsLaws
import Johnson.Road.K4.NormsFormsZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Level)
open OnBytes.Model.Layer (Pub Env Own)
open OnBytes.Desc.First.K4 (gatedForms normsForms formsFrontWith formsBack ownClaim rowsSummand
  front back front_some mem_front normsForms_shape)

/-- The two product layers' own rows are members of the gated products' group. -/
theorem gatedForms_rows {P : Pub} {v : Env} {hd : Level} {hd2 : Option Level} {l : List Aff}
    (h : gatedForms P v hd hd2 = some l) :
    hd.row ∈ l ∧ ∀ o2, hd2 = some o2 → o2.row ∈ l := by
  unfold gatedForms at h
  obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨o, a4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e2, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t2, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
  have e' : hd.row :: a ++ o.row :: b = l := Option.some.inj h
  subst e'
  refine ⟨by simp, fun o2 h2 => ?_⟩
  obtain rfl : o = o2 := Option.some.inj (a4.symm.trans h2)
  simp

/-- **The own rows in the list of the run "front".** -/
theorem front_rows {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork} {fs : Array Aff}
    (h : formsFrontWith rows P g o F = some (fs, G)) :
    o.H.wpl.row ∈ fs.toList ∧ o.hd.row ∈ fs.toList ∧
      (∀ o2, o.hd2 = some o2 → o2.row ∈ fs.toList) ∧
      ∃ sh rowV F',
        ((Array.range (4 * P.y.NI)).mapM fun i => F.shown (o.H.tV.sEnd + i)) = some sh ∧
        ownClaim o.H.tV.p (rowsSummand P.y o.H sh) {} F = some (rowV, F') ∧
        rowV = o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {} ∧ rowV ∈ fs.toList := by
  have h0 := h
  unfold formsFrontWith at h0
  obtain ⟨sh, a1, h1⟩ := Option.bind_eq_some_iff.mp h0
  obtain ⟨⟨rowV, F1⟩, a2, h2⟩ := Option.bind_eq_some_iff.mp h1
  dsimp only at h2
  obtain ⟨pp, a3, h3⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨rowL, F2⟩, a4, h4⟩ := Option.bind_eq_some_iff.mp h3
  dsimp only at h4
  obtain ⟨l, a5, h5⟩ := Option.bind_eq_some_iff.mp h4
  have e5 : fs = l.toArray := (congrArg Prod.fst (Option.some.inj h5)).symm
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, b1, -, -, b4, -⟩ := front_some a5
  obtain ⟨m1, -, m3, -, -, m6, -⟩ := mem_front a5
  obtain ⟨f, ef⟩ := normsForms_shape b1
  obtain ⟨r5, r6⟩ := gatedForms_rows b4
  rw [e5]
  refine ⟨m1 g2 b1 _ (by rw [ef]; simp), m6 g89 b4 _ r5, fun o2 h2' => m6 g89 b4 _ (r6 o2 h2'),
    sh, rowV, F1, a1, a2, (Desc.First.K4.ownClaim_some a2).1, m3⟩

/-- **The own rows in the list of the run "back".** -/
theorem back_rows {o : Own} {F G : Fork} {fs : Array Aff} (h : formsBack o F = some (fs, G)) :
    o.K.rowS ∈ fs.toList ∧
      ∃ rowM F', ownClaim o.wo.toWsMerged.p o.wo.toWsMerged.fvp {} F = some (rowM, F') ∧
        rowM ∈ fs.toList ∧ G = F'.paid o.H.fo.owedJoin := by
  unfold formsBack at h
  obtain ⟨⟨rowM, F1⟩, a1, h1⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h1
  have e := Option.some.inj h1
  have e1 : fs = (back o rowM).toArray := (congrArg Prod.fst e).symm
  have e2 : G = F1.paid o.H.fo.owedJoin := (congrArg Prod.snd e).symm
  rw [e1]
  exact ⟨by simp [back], rowM, F1, a1, by simp [back], e2⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.front_rows
#print axioms OnBytes.Road.K4.back_rows
