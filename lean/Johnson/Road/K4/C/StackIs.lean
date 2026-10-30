-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StackIs.lean: CONDITIONAL.

Not shown here. THAT THE MAKER RETURNS: a hypothesis, of which no example is known here. Nothing on
what the tables hold. Nothing on soundness, on completeness or on any other property.
No property is claimed.

The hypothesis `StackIs` (C/StackEnds.lean) where the maker of the batched sumcheck's data returns
(`stackData`, Johnson/Desc/K4/Honest/Stack.lean): by the makers' own text.

  `sides_parts`   what `Sides.of` lays: the layout, the lookup's token point, the table of gated
      products.
  `stackIs_of`   StackIs Q w p.rt SD tb at the two tables tb of the first product layer; and SD.S.zt
      = ztOf Q p.
-/
import Johnson.Road.K4.C.StackEnds
import Johnson.Road.K4.C.RowMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest

/-- What `Sides.of` lays. -/
theorem sides_parts {Q : K4Pub} {w : K4In} {p : Pts} {S : Sides} (h : Sides.of Q w p = some S) :
    S.v.y = Q.P.y ∧ S.zt = ztOf Q p ∧ ∃ tb : Tab × Tab, gatedTabs Q w = some tb ∧
      S.hh = (Array.range tb.1.size).map fun i => mulE (tb.1.getD i zeroE) (tb.2.getD i zeroE) := by
  unfold Sides.of at h
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨TS, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Z, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨cls, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨x, lfc⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨opens, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨gl, gr⟩, hg, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ends, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  exact ⟨envOf_y hv, rfl, (gl, gr), hg, rfl⟩

/-- **StackIs where the maker returns.** CONDITIONAL: on the return. -/
theorem stackIs_of {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) :
    SD.S.zt = ztOf Q p ∧ ∃ tb : Tab × Tab, StackIs Q w p.rt SD tb := by
  unfold stackData at h
  obtain ⟨S, hS, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hy, hz, tb, ht, hh⟩ := sides_parts hS
  unfold stackDataOn at h
  obtain ⟨R, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨bl, places⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  by_cases hc : (ceilLog2 places != S.Q.hp.lamS || p.om.size != 2 ||
      S.opens.size != S.Q.hp.NCL - (if (S.Q.g == 0) = true then 1 else 0)) = true
  · rw [if_pos hc] at h
    simp at h
  · rw [if_neg hc] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sides, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    exact ⟨hz, tb, { y := hy, tabs := ht, hh := hh, hZ := rfl, hR := rfl }⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.sides_parts
#print axioms OnBytes.Road.K4.C.stackIs_of
