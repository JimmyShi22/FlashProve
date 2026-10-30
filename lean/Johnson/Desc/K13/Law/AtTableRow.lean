-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableRow.lean: what Johnson/Desc/K13/Law/AtTable.lean asks of the table of
joints at K13's row (`RowM3`), as ONE TEST WITH CODE on the table's rows and open sets; and that
test at the two lists of segments that the table's own walk reads. A definition, a statement with
its proof, two members.
Main names:
  `rowM3B M links ps k`: the test: nine clauses, none reads the plan's numbers. M: a filling of the
    table's door.
  `rowM3_of_test`: a yes gives `RowM3 N M links ps k` at every N that has as many trees and messages
    behind the block as in front (two equations on N: premises).
  `rowM3_small`, `rowM3_full`: **members OF THE TEST**, at the empty filling (the two equations on N
    stay premises; no N made of a plan stands here): the driver's own list of places
    (`First.flatPlaces true links true`) at five segments (layers, attention, layers, attention, the
    head) and block number 75; at twenty-five segments and block number 355: by the kernel's own
    evaluation of the test.
  `rowM3B_front`, `rowM3B_behind`, `rowM3B_shifted`, `rowM3B_made`: tries: the test says no at the
    block in front (K12's), at the block behind (W's commitment), at the list of places without the
    chain's front (the numbers shift by one), and at a filling of the door that has an item made at
    K13's own place (clause 8: it is open behind, was not open in front, and is not `frontOk`).

What is not claimed. That a real plan's segments are one of these two lists: they are written here
as a program that walks the table writes them (its `small` and `full`; that program is not
shown here). No try reaches clauses 3, 4, 5, 7 and 9 alone. At a filling
of the door that holds several kinds' items: no member. Nothing on `FillM3`. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtTable
import Johnson.Desc.Sound.SpineList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (ModelPart Item Pub Numbers More)
open VerifiableInference.Desc.Sound (insQ outsQ openAfter insL outsL openL openIsList)

/-- No pin with a sample but the index masks'. -/
def noOtherPin : Item → Bool
  | .pin _ _ => false
  | .pinKept _ => false
  | .pinV => false
  | _ => true

/-- **`RowM3` as a test with code.** -/
def rowM3B (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((insL links ps k).all fun i => i == .pile || i == .pinW || i == .pinI || i == .unmarked) &&
    ((outsL links ps k).contains .pileOne && (outsL links ps k).contains .pinW &&
      (outsL links ps k).contains .pinI) &&
    ((openL (insL links ps) (outsL links ps) (First.start links) k).all
      (insL links ps k).contains) &&
    (ps[k + 1]?.all fun p' => First.standAt links p' == .mem) &&
    (openAt links ps k).contains .pinI &&
    (openAt links ps (k + 1)).all noOtherPin &&
    (First.rowSegs (openAt links ps (k + 1))).isEmpty &&
    (((First.pubSets M links ps)[k + 1]?.getD []).all fun q =>
      q == .frontOk || ((First.pubSets M links ps)[k]?.getD []).contains q) &&
    ((First.pubOfItems (openAt links ps (k + 1))).all fun q => q == .indexIs || q == .indexThere)

/-- **A yes of the test gives what is asked of the table**, at every N that has as many trees and
messages behind the block as in front. -/
theorem rowM3_of_test (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (h : rowM3B M links ps k = true) (N : Numbers)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?) :
    RowM3 N M links ps k := by
  unfold rowM3B at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, ⟨h2a, h2b⟩, h2c⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, List.contains_iff_mem.1 h5, ?_, ?_, ?_, ?_, hT, hM⟩
  · intro i hi
    have := List.all_eq_true.1 h1 i hi
    simpa [Bool.or_eq_true, or_assoc] using this
  · exact List.contains_iff_mem.1 h2a
  · exact List.contains_iff_mem.1 h2b
  · exact List.contains_iff_mem.1 h2c
  · intro i hi
    have hm := (openIsList Item (insL links ps) (outsL links ps) (First.start links) k i).1 hi
    exact List.contains_iff_mem.1 (List.all_eq_true.1 h3 i hm)
  · intro p' hp'
    rw [hp'] at h4
    exact eq_of_beq h4
  · intro t ht
    obtain ⟨i, hi, hti⟩ := List.mem_flatMap.1 ht
    have hb := List.all_eq_true.1 h6 i hi
    cases i with
    | pinI => exact List.mem_singleton.1 hti
    | pin m u => exact absurd (show false = true from hb) Bool.false_ne_true
    | pinKept m => exact absurd (show false = true from hb) Bool.false_ne_true
    | pinV => exact absurd (show false = true from hb) Bool.false_ne_true
    | _ => exact absurd (show t ∈ ([] : List (ℕ × ℕ)) from hti) List.not_mem_nil
  · exact List.isEmpty_iff.1 h7
  · intro q hq
    rcases Bool.or_eq_true _ _ ▸ List.all_eq_true.1 h8 q hq with e | e
    · exact Or.inl (eq_of_beq e)
    · exact Or.inr (List.contains_iff_mem.1 e)
  · intro q hq
    rcases Bool.or_eq_true _ _ ▸ List.all_eq_true.1 h9 q hq with e | e
    · exact Or.inl (eq_of_beq e)
    · exact Or.inr (eq_of_beq e)

/-- Five segments, as the table's walk writes its small list. -/
def linksSmall : List ModelPart := [.layers, .attention, .layers, .attention, .head]

/-- Twenty-five, as it writes its full list. -/
def linksFull : List ModelPart :=
  (List.range 24).map (fun i => if i % 2 == 0 then ModelPart.layers else ModelPart.attention) ++ [.head]

set_option maxRecDepth 1000000 in
/-- **A member of the test** (the numbers' half is a premise): the small list; K13's block has the
number 75 of 78. -/
theorem rowM3_small (N : Numbers)
    (hT : N.treesAt (First.flatPlaces true linksSmall true)[75 + 1]? =
      N.treesAt (First.flatPlaces true linksSmall true)[75]?)
    (hM : N.msgsAt (First.flatPlaces true linksSmall true)[75 + 1]? =
      N.msgsAt (First.flatPlaces true linksSmall true)[75]?) :
    RowM3 N {} linksSmall (First.flatPlaces true linksSmall true) 75 :=
  rowM3_of_test _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
/-- **A member of the test** (the numbers' half is a premise): the full list; K13's block has the
number 355 of 358. -/
theorem rowM3_full (N : Numbers)
    (hT : N.treesAt (First.flatPlaces true linksFull true)[355 + 1]? =
      N.treesAt (First.flatPlaces true linksFull true)[355]?)
    (hM : N.msgsAt (First.flatPlaces true linksFull true)[355 + 1]? =
      N.msgsAt (First.flatPlaces true linksFull true)[355]?) :
    RowM3 N {} linksFull (First.flatPlaces true linksFull true) 355 :=
  rowM3_of_test _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
/-- A try: at the block in front the test says no. -/
theorem rowM3B_front :
    rowM3B {} linksSmall (First.flatPlaces true linksSmall true) 74 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A try: at the block behind it says no. -/
theorem rowM3B_behind :
    rowM3B {} linksSmall (First.flatPlaces true linksSmall true) 76 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A try: at the list without the chain's front the number 75 is another block's. -/
theorem rowM3B_shifted :
    rowM3B {} linksSmall (First.flatPlaces false linksSmall true) 75 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A try: a filling of the door with an item that is made at K13's own place. -/
theorem rowM3B_made :
    rowM3B { rows := fun _ p => if p.kind == .K13 then { makes := [(none, "K13.try")] } else {} }
      linksSmall (First.flatPlaces true linksSmall true) 75 = false := by
  decide +kernel

end VerifiableInference.Desc.K13.Law
