-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/K4Marks.lean: one definition, and statements on lists with
their proofs. General in the ground.

What is here. THE MARKS OF THE FEED-FORWARD LAYERS' OWN ROUNDS (the sub-protocol K4) AT THE PROOF
FILE's FIRST CHAIN AT THE FULL SIZE, AS ONE LIST, read off the ground (`ProofFile.Ground`: the segments'
structures that the library's maker yields from the public part; of it the list reads the field W
alone). A mark (`Mark`, Honest/Law/Marks.lean) is a place, a test on the challenges and a stated
number: it names an event on the challenges of which the verifier has no test; it is counted, not
tested by the verifier (that the verifier rejects nothing where a mark speaks is not said: the head
of Law/Mark.lean). A mark is silent where its test returns none. (It is not the verifier's own sign
of a failure, which other files of this folder, no part of the library yet, call a mark too.)
`k4Marks Zp G₀`: for each group g below 12 whose plan hp the ground has (G₀.W.G[g]?), the mark
`k4Mark` (Law/Mark.lean) at the public data with P := G₀.W.layers, hp, g, link := 2 g, piece := 3,
r0 := 0, seg := 2 g. THE EVENT, where la ≤ muV (Law/Mark.lean says what the list of rounds is else):
in one of la + 2 lt listed rounds of K4's own member the sampled element shows as 0 or as 1. The
fields are laid as the frame's list of falls lays those of `k4Fall`, but for r0, which is an
argument there. `k4Mark_blind`: the mark reads neither hp nor r0 nor seg: by unfolding.

  `k4Marks`   **the list.**
  `k4Mark_blind`   **the mark reads neither hp nor r0 nor seg.**
  `k4Marks_mem`, `k4Marks_mem_any`   the mark of a group whose plan is there is in the list; at
      every r0 and seg.
  `k4Marks_of_mem`   every mark of the list is such a one.
  `k4Marks_place`, `k4Marks_kind`   its place; the place's kind is K4.
  `k4_filterMap_range`, `k4Marks_length`   where all twelve look-ups return, twelve marks.

Not shown here. SIX FILES OF THIS FOLDER THAT ARE NAMED BELOW ARE NO PART OF THE LIBRARY YET:
Law/K4MarksTwelve.lean, Law/K4MarksSeat.lean, Law/K4MarksHead.lean, Law/MarksWideHead.lean,
Law/MarkDebt.lean, Law/MarkPlan.lean. THE PUBLIC PART IS NOT READ: it is there so that every kind's
list has the same two arguments; in `k4Marks_mem`, `k4Marks_mem_any` and `k4Marks_length` it is an
implicit letter that stands in the conclusion alone: a caller without an expected type names it (Zp
:= …). THE 0 AT r0 IS A FILLER (`k4Mark_blind`; `k4Marks_mem_any`). WHERE THE GROUND HAS NO PLAN AT
A GROUP THE TEXT LEAVES THE MARK OUT AND SAYS NOTHING: `k4Marks_length` takes as a hypothesis that
the look-ups return; under the library's hypothesis on the public files, at the ground of the base
that the library's maker returns, they do: `k4Marks_twelve` (Law/K4MarksTwelve.lean). THE NUMBERS
12, 2 g AND 3 ARE WRITTEN: THE FULL SIZE ALONE; that a member of the chain stands at each of these
places: `k4Marks_member` (Law/K4MarksTwelve.lean), under the library's hypothesis on the public
files. NO BOUND, NO FILLING AND NO STATEMENT ON A RUN OR A STATE THAT ITS WRITERS KNOW OF TAKES THIS
LIST: the statements over it that they know are on lists alone (Law/K4MarksTwelve.lean,
Law/K4MarksSeat.lean, Law/K4MarksHead.lean; Law/K4MarksWide.lean and Law/MarksWideHead.lean draw the
wider list's places and length from this one's). EACH MARK's SHARE IS A WRITTEN PAIR OF NUMBERS AND
NO BOUND; it is not evaluated here, and nothing is added up here. THE BOUND AT A MEMBER IS OWED:
`k4_markDebt_table` (Law/MarkDebt.lean) has the frame's sentence `MarkDebt` at `k4Mark Q`, at the
number `(k4Mark Q).share.val`, under three hypotheses, and between it and a member of the chain
stand, one by one: that the data of the member's rounds have the entries of the verifier's table of
K4's rounds, and each round's kind its name's (hent, hkind); that la ≤ muV, or the three hypotheses
on the plan's makers from which Law/MarkPlan.lean has it, AT THE GROUND's LAYERS under the library's
hypothesis on the public files: not shown here, nor, as a statement, in any file that its writers
know of (the first of the three stands as a step inside the proof of `llLam_at_base`,
Law/Live/AtBase.lean; the comparison is the first clause of the library's test `pointsB`,
Johnson/Desc/First/K4/Returns/Points.lean, a hypothesis there); and the kit of typed challenges:
that sentence stands at `Run.ckP .two` alone. WHAT THE SILENCE OF A MARK OF THIS LIST GIVES AT ANY
STATE OF THE VERIFIER IS NOT SHOWN HERE, NOR IN ANY FILE THAT ITS WRITERS KNOW OF; of the wider
mark's silence: Law/Live/TapeOfMark.lean and Law/Live/LiveOfYes.lean, conditional.

Kin. Other kinds' lists of marks with the same two arguments, the public part and the ground:
`k3Marks` (Honest/K3/Good/MarksList.lean), `k5Marks` (Honest/K5/MarksList.lean), `part4Marks`
(Honest/K6/K6Marks.lean). The frame's list of all kinds' marks (`marksHead`,
Honest/Law/MarksHead.lean) holds K4's WIDER list (`k4MarksWide`, Law/K4MarksWide.lean), not this
one. The frame's list of falls is `fallsHead` (Honest/Law/FallsHead.lean). `k4_filterMap_range` IS
PROVED A SECOND TIME ELSEWHERE: `length_filterMap_range` of that same file, which is not imported
here, has the same statement and the same proof.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Mark

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open VerifiableInference.Desc (Place)

/-- **K4's marks at the first chain at the full size.** The first argument, the public part, is not
read. Each share is a written pair of numbers and no bound (`k4Mark`). The 0 at r0 is a filler: the
mark does not read that field (`k4Mark_blind`). -/
def k4Marks (_ : ProofFile.Pub) (G₀ : ProofFile.Ground) : List Mark :=
  (List.range 12).filterMap fun g => (G₀.W.G[g]?).map fun hp =>
    k4Mark ⟨G₀.W.layers, hp, g, 2 * g, 3, 0, 2 * g⟩

/-- **THE MARK READS NEITHER hp NOR r0 NOR seg**: at two public data that agree in the four other
fields it is one structure. -/
theorem k4Mark_blind (P : OnBytes.Model.Layer.Pub) (hp hp' : OnBytes.Model.Layer.HPlan2)
    (g link piece a a' s s' : Nat) :
    k4Mark ⟨P, hp, g, link, piece, a, s⟩ = k4Mark ⟨P, hp', g, link, piece, a', s'⟩ :=
  rfl

variable {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- CONDITIONAL: on hg and hh. The mark of a group whose plan is there is in the list. -/
theorem k4Marks_mem {g : Nat} (hg : g < 12) {hp : OnBytes.Model.Layer.HPlan2}
    (hh : G₀.W.G[g]? = some hp) :
    k4Mark ⟨G₀.W.layers, hp, g, 2 * g, 3, 0, 2 * g⟩ ∈ k4Marks Zp G₀ := by
  unfold k4Marks
  refine List.mem_filterMap.2 ⟨g, List.mem_range.2 hg, ?_⟩
  rw [hh]
  rfl

/-- CONDITIONAL: on hg and hh. The same, whatever stands in r0 and seg. -/
theorem k4Marks_mem_any {g : Nat} (hg : g < 12) {hp : OnBytes.Model.Layer.HPlan2}
    (hh : G₀.W.G[g]? = some hp) (a s : Nat) :
    k4Mark ⟨G₀.W.layers, hp, g, 2 * g, 3, a, s⟩ ∈ k4Marks Zp G₀ := by
  rw [k4Mark_blind G₀.W.layers hp hp g (2 * g) 3 a 0 s (2 * g)]
  exact k4Marks_mem hg hh

/-- **Every mark of the list is the mark of a group below 12 whose plan is there.** -/
theorem k4Marks_of_mem {m : Mark} (hm : m ∈ k4Marks Zp G₀) :
    ∃ (g : Nat) (hp : OnBytes.Model.Layer.HPlan2), g < 12 ∧ G₀.W.G[g]? = some hp ∧
      m = k4Mark ⟨G₀.W.layers, hp, g, 2 * g, 3, 0, 2 * g⟩ := by
  unfold k4Marks at hm
  obtain ⟨g, hg, e⟩ := List.mem_filterMap.1 hm
  obtain ⟨hp, hh, rfl⟩ := Option.map_eq_some_iff.1 e
  exact ⟨g, hp, List.mem_range.1 hg, hh, rfl⟩

/-- A mark of the list stands at the written place of its group. -/
theorem k4Marks_place {m : Mark} (hm : m ∈ k4Marks Zp G₀) :
    ∃ g, g < 12 ∧ m.place = (⟨1, some (2 * g), 3, .K4⟩ : Place) := by
  obtain ⟨g, _, hg, -, rfl⟩ := k4Marks_of_mem hm
  exact ⟨g, hg, rfl⟩

/-- **Every mark of the list stands at a place of the kind K4.** -/
theorem k4Marks_kind {m : Mark} (hm : m ∈ k4Marks Zp G₀) : m.place.kind = .K4 := by
  obtain ⟨_, _, e⟩ := k4Marks_place hm
  rw [e]

/-- A law on lists: where the function returns at every number below n, nothing is left out. (The
frame's Honest/Law/FallsHead.lean, has the same law as `length_filterMap_range`; that file is not
imported here.) -/
theorem k4_filterMap_range {α : Type} (k : Nat → Option α) :
    ∀ n, (∀ g, g < n → (k g).isSome = true) → ((List.range n).filterMap k).length = n
  | 0, _ => by simp
  | n + 1, h => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (h n (Nat.lt_succ_self n))
    have e : [n].filterMap k = [a] := by simp [ha]
    rw [List.range_succ, List.filterMap_append, List.length_append,
      k4_filterMap_range k n (fun g hg => h g (by omega)), e, List.length_singleton]

/-- CONDITIONAL: on h4. **Where all twelve look-ups return, the list has twelve marks.** -/
theorem k4Marks_length (h4 : ∀ g, g < 12 → (G₀.W.G[g]?).isSome = true) :
    (k4Marks Zp G₀).length = 12 := by
  unfold k4Marks
  exact k4_filterMap_range _ 12 fun g hg => by
    obtain ⟨hp, hh⟩ := Option.isSome_iff_exists.1 (h4 g hg)
    show (Option.map _ (G₀.W.G[g]?)).isSome = true
    rw [hh]
    rfl

end ProofFile.Honest.K4


#print axioms ProofFile.Honest.K4.k4Marks
#print axioms ProofFile.Honest.K4.k4Mark_blind
#print axioms ProofFile.Honest.K4.k4Marks_mem
#print axioms ProofFile.Honest.K4.k4Marks_mem_any
#print axioms ProofFile.Honest.K4.k4Marks_of_mem
#print axioms ProofFile.Honest.K4.k4Marks_place
#print axioms ProofFile.Honest.K4.k4Marks_kind
#print axioms ProofFile.Honest.K4.k4_filterMap_range
#print axioms ProofFile.Honest.K4.k4Marks_length
