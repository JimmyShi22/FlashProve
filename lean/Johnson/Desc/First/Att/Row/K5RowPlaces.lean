-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowPlaces.lean: kind K5's lot, forward: a law on a list: of 25 links
(values of OnBytes.Model.Stages.LinkH: "one link of the chain: a sub-proof"), layers and attention
in turn and the head last, the text of H2K5.k5Places (Johnson/Desc/ProofFile/Lot/K5.lean) picks the
twelve (2 g + 1, "A" ++ toString g, g). At every array of links with these properties. NOTHING IS
EVALUATED.
Main name: H2K5.Row.places_of_named. Its user: Johnson/Desc/First/Att/Row/K5RowSeat.lean.
IS IT EMPTY HERE? Its premises are what another file's theorems end in, in scope, where the ground
is made (IM.ground_gets | ground_named, Johnson/IMR/PureJoin.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Lot.K5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes.Model.Stages (LinkH)

/-- Of 25 segments, layers and attention in turn and the head last, the attention segments are the
twelve. -/
theorem places_of_named (B : Array LinkH) (hs : B.size = 25)
    (hN : ∀ g, g < 12 → ∃ l l', B[2 * g]? = some l ∧ l.kind = 0 ∧ B[2 * g + 1]? = some l' ∧ l'.kind = 1 ∧ l'.g = g ∧
      l'.name = "A" ++ toString g)
    (hH : ∃ l, B[24]? = some l ∧ l.kind = 2) :
    ((B.toList.zipIdx.filter fun x => x.1.kind == 1).map fun x => (x.2, x.1.name, x.1.g)) =
      (List.range 12).map fun g => (2 * g + 1, "A" ++ toString g, g) := by
  obtain ⟨a0, b0, ha0, ka0, hb0, kb0, gb0, nb0⟩ := hN 0 (by omega)
  obtain ⟨a1, b1, ha1, ka1, hb1, kb1, gb1, nb1⟩ := hN 1 (by omega)
  obtain ⟨a2, b2, ha2, ka2, hb2, kb2, gb2, nb2⟩ := hN 2 (by omega)
  obtain ⟨a3, b3, ha3, ka3, hb3, kb3, gb3, nb3⟩ := hN 3 (by omega)
  obtain ⟨a4, b4, ha4, ka4, hb4, kb4, gb4, nb4⟩ := hN 4 (by omega)
  obtain ⟨a5, b5, ha5, ka5, hb5, kb5, gb5, nb5⟩ := hN 5 (by omega)
  obtain ⟨a6, b6, ha6, ka6, hb6, kb6, gb6, nb6⟩ := hN 6 (by omega)
  obtain ⟨a7, b7, ha7, ka7, hb7, kb7, gb7, nb7⟩ := hN 7 (by omega)
  obtain ⟨a8, b8, ha8, ka8, hb8, kb8, gb8, nb8⟩ := hN 8 (by omega)
  obtain ⟨a9, b9, ha9, ka9, hb9, kb9, gb9, nb9⟩ := hN 9 (by omega)
  obtain ⟨a10, b10, ha10, ka10, hb10, kb10, gb10, nb10⟩ := hN 10 (by omega)
  obtain ⟨a11, b11, ha11, ka11, hb11, kb11, gb11, nb11⟩ := hN 11 (by omega)
  obtain ⟨h, hh, kh⟩ := hH
  have e : B.toList = [a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, a8, b8, a9, b9, a10, b10, a11, b11, h] := by
    apply List.ext_getElem?
    intro i
    rw [Array.getElem?_toList]
    rcases Nat.lt_or_ge i 25 with hi | hi
    · interval_cases i
      · exact ha0
      · exact hb0
      · exact ha1
      · exact hb1
      · exact ha2
      · exact hb2
      · exact ha3
      · exact hb3
      · exact ha4
      · exact hb4
      · exact ha5
      · exact hb5
      · exact ha6
      · exact hb6
      · exact ha7
      · exact hb7
      · exact ha8
      · exact hb8
      · exact ha9
      · exact hb9
      · exact ha10
      · exact hb10
      · exact ha11
      · exact hb11
      · exact hh
    · rw [Array.getElem?_eq_none (by omega), List.getElem?_eq_none (by simpa using hi)]
  rw [e]
  show (([(a0, 0), (b0, 1), (a1, 2), (b1, 3), (a2, 4), (b2, 5), (a3, 6), (b3, 7), (a4, 8), (b4, 9), (a5, 10), (b5, 11), (a6, 12), (b6, 13), (a7, 14), (b7, 15), (a8, 16), (b8, 17), (a9, 18), (b9, 19), (a10, 20), (b10, 21), (a11, 22), (b11, 23), (h, 24)].filter fun x : LinkH × ℕ => x.1.kind == 1).map fun x => (x.2, x.1.name, x.1.g)) =
    [(1, "A" ++ toString 0, 0), (3, "A" ++ toString 1, 1), (5, "A" ++ toString 2, 2), (7, "A" ++ toString 3, 3), (9, "A" ++ toString 4, 4), (11, "A" ++ toString 5, 5), (13, "A" ++ toString 6, 6), (15, "A" ++ toString 7, 7), (17, "A" ++ toString 8, 8), (19, "A" ++ toString 9, 9), (21, "A" ++ toString 10, 10), (23, "A" ++ toString 11, 11)]
  simp only [List.filter_cons, List.filter_nil, ka0, kb0, ka1, kb1, ka2, kb2, ka3, kb3, ka4, kb4, ka5, kb5, ka6, kb6, ka7, kb7, ka8, kb8, ka9, kb9, ka10, kb10, ka11, kb11, kh, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, gb0, nb0, gb1, nb1, gb2, nb2, gb3, nb3, gb4, nb4, gb5, nb5, gb6, nb6, gb7, nb7, gb8, nb8, gb9, nb9, gb10, nb10, gb11, nb11]

end H2K5.Row

#print axioms H2K5.Row.places_of_named
