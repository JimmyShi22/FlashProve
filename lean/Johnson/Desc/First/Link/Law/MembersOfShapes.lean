-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/MembersOfShapes.lean: THE LIST OF THE MEMBERS' SAMPLES, AS A TERM, AND `TiedOwes`' FIELD «members» FROM
`ShapesAre`. A definition and theorems.

Why. `numBy`, `rowsTied_of` (TiedAtK10.lean) and `tied_laid_in` (TiedLaidIn.lean) keep as a LETTER the list es of all pairs
(member, number of one of its samples), without repeats, in the order in which the group's members stand. No term
was written for it.

What is said, at `groupLayK cs lo s e kb hM hZ`:
  `esOf`: the written list's members (`membersOf lo`), in the list's order, each with its one sample (a message of `sigOf`
    has one sample: `portZ`'s S is Unit).
  `esOf_nodup`, `esOf_all`: no pair twice; every pair is there. `esOf_length`: as many as the members.
  `esOf_fst`: the pairs' members are `membersOf lo`, in order.
  `members_of_shapes`: **`ShapesAre T G lo kb no` ⊢ G.members.toList = (esOf ..).map fun x => no x.1.1**: the field
    «members» at es := esOf.

Limits. `ShapesAre` is shown of no verifier's state here. Nothing on the two counts (plain, gens). Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.CubeOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb
open VerifiableInference.Desc.First.Close

variable (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ) (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)

/-- **The members' samples**: the written list's members in order, each with its one sample. -/
def esOf : List (Σ a : (groupLayK cs lo s e kb hM hZ).G.A, ((sigOf cs lo).om a.1).Z.S) :=
  (membersOf lo).attach.map fun i => ⟨⟨i.1, mem_members.1 i.2⟩, ()⟩

theorem esOf_length : (esOf cs lo s e kb hM hZ).length = (membersOf lo).length := by
  simp [esOf]

/-- The pairs' members are the written list's, in order. -/
theorem esOf_fst : (esOf cs lo s e kb hM hZ).map (fun x => x.1.1) = membersOf lo := by
  unfold esOf
  rw [List.map_map]
  exact List.attach_map_subtype_val _

theorem esOf_nodup : (esOf cs lo s e kb hM hZ).Nodup := by
  refine List.Nodup.of_map (fun x => x.1.1) ?_
  rw [esOf_fst]
  exact members_nodup lo

theorem esOf_all (x : Σ a : (groupLayK cs lo s e kb hM hZ).G.A, ((sigOf cs lo).om a.1).Z.S) :
    x ∈ esOf cs lo s e kb hM hZ := by
  obtain ⟨a, u⟩ := x
  exact List.mem_map.2 ⟨⟨a.1, mem_members.2 a.2⟩, List.mem_attach _ _, rfl⟩

variable {cs lo s e kb hM hZ}

/-- **TiedOwes' FIELD «members», FROM ShapesAre.** -/
theorem members_of_shapes {T : Statement} {G : Group} {no : Fin lo.length → ℕ}
    (H : ShapesAre T G lo kb no) :
    G.members.toList = (esOf cs lo s e kb hM hZ).map fun x => no x.1.1 := by
  have e1 : ((esOf cs lo s e kb hM hZ).map fun x => no x.1.1) =
      ((esOf cs lo s e kb hM hZ).map fun x => x.1.1).map no := by
    rw [List.map_map]
    rfl
  rw [H.members, e1]
  exact congrArg (List.map no) (esOf_fst cs lo s e kb hM hZ).symm

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.esOf
#print axioms VerifiableInference.Desc.LinkJoin.esOf_length
#print axioms VerifiableInference.Desc.LinkJoin.esOf_fst
#print axioms VerifiableInference.Desc.LinkJoin.esOf_nodup
#print axioms VerifiableInference.Desc.LinkJoin.esOf_all
#print axioms VerifiableInference.Desc.LinkJoin.members_of_shapes
