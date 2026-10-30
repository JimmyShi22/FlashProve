-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/G4/FlatLaws.lean: from a round of plain data to the view's round and back gives the round.
Main theorems: mapM_elementOfGot, FlatRound.ofRV_rv, Flat.view_rounds_length.
Not claimed. Nothing on the program's run.
-/
import OnBytes.G4.Flat

namespace OnBytes.G4

/-- Elements, spelled as items read, are read back as they were. -/
theorem mapM_elementOfGot (l : List E) :
    (l.map fun x => Fmt.ItemValue.e x.triple).mapM elementOfGot = some l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, ih, elementOfGot, E.ofTriple_triple]

/-- Triples of elements are read back as the elements. -/
theorem map_ofTriple_triple (l : List E) : (l.map E.triple).map E.ofTriple = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, E.ofTriple_triple]

/-- From a round to the view's round and back. -/
theorem FlatRound.ofRV_rv (r : FlatRound) : FlatRound.ofRV r.rv = some r := by
  show (if ([] : List Nat).isEmpty && ([] : List Int).isEmpty && (none : Option ByteArray).isNone then
      ((r.sent.map fun x => Fmt.ItemValue.e x.triple).mapM elementOfGot).map fun sent =>
        (⟨sent, (r.drawn.map E.triple).map E.ofTriple⟩ : FlatRound)
    else none) = some r
  rw [mapM_elementOfGot, map_ofTriple_triple]
  rfl

/-- The view has as many rounds as the plain data. -/
theorem Flat.view_rounds_length (t : Flat) : t.view.rounds.length = t.rounds.length := by
  simp [Flat.view]

end OnBytes.G4

#print axioms OnBytes.G4.FlatRound.ofRV_rv
#print axioms OnBytes.G4.Flat.view_rounds_length
