-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/K4MarksWide.lean: one definition, and statements on lists with
their proofs. General in the ground.

What is here. THE LIST OF K4's WIDER MARKS AT THE FIRST CHAIN AT THE FULL SIZE: `k4Marks`
(Law/K4Marks.lean) with `k4MarkWide` (Law/MarkWide.lean) in the stead of `k4Mark`: for each group g
below 12 whose plan the ground holds, the wider mark at that plan, at the written place ⟨1, some (2
g), 3, K4⟩. THE PLACES ARE THOSE OF `k4Marks`, ONE FOR ONE AND IN THE SAME ORDER
(`k4MarksWide_places`): so the two lists are equally long, and what Law/K4Marks.lean says of its
list's places holds of this one.

  `k4MarksWide Zp G₀`   the list; the first argument is not read.
  `k4MarksWide_places`   **the same places as `k4Marks`.**
  `k4MarksWide_length_eq`, `k4MarksWide_length`   as many; twelve, where the ground holds all twelve
      plans.
  `k4MarksWide_mem`, `k4MarksWide_mem_any`, `k4MarksWide_of_mem`   what is in the list.
  `k4MarksWide_place`, `k4MarksWide_kind`   where its marks stand.

Not shown here. ONE FILE OF THIS FOLDER THAT IS NAMED BELOW IS NO PART OF THE LIBRARY YET:
Law/K4MarksTwelve.lean. That the ground holds a plan at any group (h4 is a hypothesis;
Law/K4MarksTwelve.lean has it under the library's hypothesis on the public files, at the ground of
the base that the library's maker returns): WHERE THE GROUND HAS NO PLAN AT A GROUP THE TEXT LEAVES
THE MARK OUT AND SAYS NOTHING. THE PUBLIC PART IS NOT READ: it is there so that every kind's list
has the same two arguments. WHETHER THE ROUND OF THE POINT OVER THE LAYERS WITH ROUTED EXPERTS IS
LISTED AT THE FULL SIZE (it is just where ll − 1 = 1: `k4Wide_point`, Law/MarkWide.lean) IS NOT
SHOWN HERE (that ll − 1 = 1 there: Law/Live/AtFull.lean, conditional). WHAT A MARK's SILENCE GIVES
AT ANY STATE OF THE VERIFIER (Law/Live/TapeOfMark.lean and Law/Live/LiveOfYes.lean, conditional).
Each share is a written pair of numbers and no bound. THE FULL SIZE ALONE: the bound 12 is the full
size's number of groups.

Kin. Other kinds' lists of marks with the same two arguments: `k3Marks`
(Honest/K3/Good/MarksList.lean), `k5Marks` (Honest/K5/MarksList.lean), `part4Marks`
(Honest/K6/K6Marks.lean). THE FRAME's LIST OF ALL KINDS' MARKS HOLDS THIS LIST: `marksHead`
(Honest/Law/MarksHead.lean) has it as one of its stretches, and `k4_sub`
(Honest/Law/MarksHeadSub.lean) says that each of its marks is a member: both files are the frame's
writers' and no part of the library yet. Six of the eight statements are Law/K4Marks.lean's of the
like names, to the letter but for the two names of the mark and the list: `…_length`, `…_mem`,
`…_mem_any`, `…_of_mem`, `…_place`, `…_kind`.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWide
import Johnson.Desc.ProofFile.Honest.K4.Law.K4Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open VerifiableInference.Desc (Place)

/-- **K4's wider marks at the first chain at the full size.** The first argument, the public part,
is not read. Each share is a written pair of numbers and no bound (`k4MarkWide`). The 0 at r0 is a
filler: the mark does not read that field (`k4MarkWide_blind`). -/
def k4MarksWide (_ : ProofFile.Pub) (G₀ : ProofFile.Ground) : List Mark :=
  (List.range 12).filterMap fun g => (G₀.W.G[g]?).map fun hp =>
    k4MarkWide ⟨G₀.W.layers, hp, g, 2 * g, 3, 0, 2 * g⟩

variable {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **THE PLACES ARE THOSE OF `k4Marks`, ONE FOR ONE AND IN THE SAME ORDER.** -/
theorem k4MarksWide_places (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    (k4MarksWide Zp G₀).map (·.place) = (k4Marks Zp G₀).map (·.place) := by
  unfold k4MarksWide k4Marks
  rw [List.map_filterMap, List.map_filterMap]
  refine List.filterMap_congr fun g _ => ?_
  cases G₀.W.G[g]? with
  | none =>
    show (none : Option Place) = none
    rfl
  | some hp =>
    show some (k4MarkWide ⟨G₀.W.layers, hp, g, 2 * g, 3, 0, 2 * g⟩).place =
      some (k4Mark ⟨G₀.W.layers, hp, g, 2 * g, 3, 0, 2 * g⟩).place
    rw [k4MarkWide_place]

/-- The two lists are equally long. -/
theorem k4MarksWide_length_eq (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    (k4MarksWide Zp G₀).length = (k4Marks Zp G₀).length := by
  have e := congrArg List.length (k4MarksWide_places Zp G₀)
  rw [List.length_map, List.length_map] at e
  exact e

/-- CONDITIONAL: on h4. Where the ground holds a plan at each group below 12, the list has twelve
marks. -/
theorem k4MarksWide_length (h4 : ∀ g, g < 12 → (G₀.W.G[g]?).isSome = true) :
    (k4MarksWide Zp G₀).length = 12 :=
  (k4MarksWide_length_eq Zp G₀).trans (k4Marks_length h4)

/-- CONDITIONAL: on hg and hh. The wider mark of a group whose plan is there is in the list. -/
theorem k4MarksWide_mem {g : Nat} (hg : g < 12) {hp : OnBytes.Model.Layer.HPlan2}
    (hh : G₀.W.G[g]? = some hp) :
    k4MarkWide ⟨G₀.W.layers, hp, g, 2 * g, 3, 0, 2 * g⟩ ∈ k4MarksWide Zp G₀ := by
  unfold k4MarksWide
  refine List.mem_filterMap.2 ⟨g, List.mem_range.2 hg, ?_⟩
  rw [hh]
  rfl

/-- CONDITIONAL: on hg and hh. The same, whatever stands in r0 and seg. -/
theorem k4MarksWide_mem_any {g : Nat} (hg : g < 12) {hp : OnBytes.Model.Layer.HPlan2}
    (hh : G₀.W.G[g]? = some hp) (a s : Nat) :
    k4MarkWide ⟨G₀.W.layers, hp, g, 2 * g, 3, a, s⟩ ∈ k4MarksWide Zp G₀ := by
  rw [k4MarkWide_blind G₀.W.layers hp g (2 * g) 3 a 0 s (2 * g)]
  exact k4MarksWide_mem hg hh

/-- CONDITIONAL: on hm. **Every mark of the list is the wider mark of a group below 12 whose plan is
there.** -/
theorem k4MarksWide_of_mem {m : Mark} (hm : m ∈ k4MarksWide Zp G₀) :
    ∃ (g : Nat) (hp : OnBytes.Model.Layer.HPlan2), g < 12 ∧ G₀.W.G[g]? = some hp ∧
      m = k4MarkWide ⟨G₀.W.layers, hp, g, 2 * g, 3, 0, 2 * g⟩ := by
  unfold k4MarksWide at hm
  obtain ⟨g, hg, e⟩ := List.mem_filterMap.1 hm
  obtain ⟨hp, hh, rfl⟩ := Option.map_eq_some_iff.1 e
  exact ⟨g, hp, List.mem_range.1 hg, hh, rfl⟩

/-- CONDITIONAL: on hm. A mark of the list stands at the written place of its group. -/
theorem k4MarksWide_place {m : Mark} (hm : m ∈ k4MarksWide Zp G₀) :
    ∃ g, g < 12 ∧ m.place = (⟨1, some (2 * g), 3, .K4⟩ : Place) := by
  obtain ⟨g, _, hg, -, rfl⟩ := k4MarksWide_of_mem hm
  exact ⟨g, hg, rfl⟩

/-- CONDITIONAL: on hm. Every mark of the list stands at a place of the kind K4. -/
theorem k4MarksWide_kind {m : Mark} (hm : m ∈ k4MarksWide Zp G₀) : m.place.kind = .K4 := by
  obtain ⟨_, _, e⟩ := k4MarksWide_place hm
  rw [e]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4MarksWide
#print axioms ProofFile.Honest.K4.k4MarksWide_places
#print axioms ProofFile.Honest.K4.k4MarksWide_length_eq
#print axioms ProofFile.Honest.K4.k4MarksWide_length
#print axioms ProofFile.Honest.K4.k4MarksWide_mem
#print axioms ProofFile.Honest.K4.k4MarksWide_mem_any
#print axioms ProofFile.Honest.K4.k4MarksWide_of_mem
#print axioms ProofFile.Honest.K4.k4MarksWide_place
#print axioms ProofFile.Honest.K4.k4MarksWide_kind
