-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/MemsAt.lean: THE MEMBERS AT A PLACE's SEATS: one Lean structure on the plan's
side, a test with code, and the lemma "the test's yes gives the structure". It names no block and no
filling.
IN PLAIN WORDS. A sending of kind K1 (its parameters: P) lays its messages into trees; message j
sits at tenant `(layOf P).part j` of tree `nT + (layOf P).tree j`, nT the trees in front. The table
of joints speaks of a list ms of members: shapes with radii, each at a seat. `MemsAt` says that the
list and the place fit: at the seat of every message that has an out-of-domain (OOD) sample a member
sits; every member that sits there has that message's shape and the radius `rad j`; the members'
code table is the place's.
Main names:
  `MemsAt cs ms P rad nT`: the structure: `codes`, `sits`, `entry`.
  `memsAtB cs ms P rad nT`: THE TEST, on plain values.
  `memsAt_of`: its yes gives the structure. `memsAt_iff`: and no more than the structure.
  `MemsAt.shape`, `MemsAt.radius`: `entry`'s two halves, in the form in which `sealed_at`
    (Johnson/Desc/K1/Law/SealedNoColl.lean) asks them.
Who spends it: `sits`: `shown_new`'s "a member sits there" (ShownNew.lean) · `entry` and `codes`:
`sealed_at`'s shape and radius at each member at the seat: for "held", "no collision" and "shown" at
a sending's new tenants.
WHY A TEST OF ITS OWN. By reading: no other test on the plan gives `entry`. The test "no member has
a fault" (`seatsFitB`, Johnson/Desc/PlanMem.lean, through `seatFaultAt`, SeatAt.lean) compares a
member's shape with the description's tenant by WORD COUNTS (main rows times degree; mask rows times
three; the code's length): three main rows of degree 1 and one of degree 3 pass alike, the numbers
of the codes and the count of answers are not compared, and NO TEST READS A MEMBER's RADIUS.
What is not claimed. That the test says yes at any plan: IT HAS NOT RUN. That nT is the number of
trees in front of the place, or rad the plan's radii. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.K1.Law.Port6
import Johnson.Desc.K1.Law.BookAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc.Sound (Mem SitsAt)

/-- **The list of members and the place fit.** -/
structure MemsAt (cs : Codes) (ms : List Mem) (P : Par) (rad : ℕ → ℕ) (nT : ℕ) : Prop where
  /-- the members' code table is the place's -/
  codes : cs = P.codes
  /-- at the seat of every message that has an OOD sample a member sits -/
  sits : ∀ j : Fin (shapesOf P).length, sampledAt P j →
    ∃ x ∈ ms, SitsAt x (nT + (layOf P).tree.getD j.val 0) ((layOf P).part.getD j.val 0)
  /-- every member that sits there has the message's shape and radius -/
  entry : ∀ j : Fin (shapesOf P).length, sampledAt P j → ∀ x ∈ ms,
    SitsAt x (nT + (layOf P).tree.getD j.val 0) ((layOf P).part.getD j.val 0) →
    x.1.l.get x.2 = (shapeAt P j, rad j.val)

/-- **The test.** -/
def memsAtB (cs : Codes) (ms : List Mem) (P : Par) (rad : ℕ → ℕ) (nT : ℕ) : Bool :=
  decide (cs = P.codes) && (List.finRange (shapesOf P).length).all fun j =>
    !decide (sampledAt P j) ||
      ((ms.any fun x =>
          x.1.seat x.2 == (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) &&
        ms.all fun x =>
          !(x.1.seat x.2 == (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) ||
            x.1.l.get x.2 == (shapeAt P j, rad j.val))

/-- **The test says just the structure.** -/
theorem memsAt_iff {cs : Codes} {ms : List Mem} {P : Par} {rad : ℕ → ℕ} {nT : ℕ} :
    memsAtB cs ms P rad nT = true ↔ MemsAt cs ms P rad nT := by
  unfold memsAtB
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨hc, h⟩
    have key : ∀ j : Fin (shapesOf P).length, sampledAt P j →
        (ms.any fun x => x.1.seat x.2 ==
          (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) = true ∧
        (ms.all fun x => !(x.1.seat x.2 ==
          (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) ||
            x.1.l.get x.2 == (shapeAt P j, rad j.val)) = true := by
      intro j hj
      have h1 := h j (List.mem_finRange j)
      rw [decide_eq_true hj, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h1
      exact h1
    refine ⟨hc, fun j hj => ?_, fun j hj x hx hs => ?_⟩
    · obtain ⟨x, hx, e⟩ := List.any_eq_true.1 (key j hj).1
      exact ⟨x, hx, eq_of_beq e⟩
    · have h2 := List.all_eq_true.1 (key j hj).2 x hx
      have hs' : x.1.seat x.2 =
          (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0) := hs
      rw [hs', beq_self_eq_true, Bool.not_true, Bool.false_or] at h2
      exact eq_of_beq h2
  · rintro ⟨hc, h1, h2⟩
    refine ⟨hc, fun j _ => ?_⟩
    by_cases hj : sampledAt P j
    · rw [decide_eq_true hj, Bool.not_true, Bool.false_or, Bool.and_eq_true]
      refine ⟨?_, List.all_eq_true.2 fun x hx => ?_⟩
      · obtain ⟨x, hx, e⟩ := h1 j hj
        have e' : x.1.seat x.2 =
            (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0) := e
        exact List.any_eq_true.2 ⟨x, hx, by rw [e', beq_self_eq_true]⟩
      · by_cases hs : x.1.seat x.2 =
            (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)
        · rw [h2 j hj x hx hs, beq_self_eq_true, Bool.or_true]
        · rw [beq_false_of_ne hs, Bool.not_false, Bool.true_or]
    · rw [decide_eq_false hj, Bool.not_false, Bool.true_or]

/-- **The test's yes gives the structure.** -/
theorem memsAt_of {cs : Codes} {ms : List Mem} {P : Par} {rad : ℕ → ℕ} {nT : ℕ}
    (h : memsAtB cs ms P rad nT = true) : MemsAt cs ms P rad nT := memsAt_iff.1 h

/-- The member's shape is the message's. -/
theorem MemsAt.shape {cs : Codes} {ms : List Mem} {P : Par} {rad : ℕ → ℕ} {nT : ℕ}
    (h : MemsAt cs ms P rad nT) (j : Fin (shapesOf P).length) (hj : sampledAt P j) (x : Mem)
    (hx : x ∈ ms) (hs : SitsAt x (nT + (layOf P).tree.getD j.val 0) ((layOf P).part.getD j.val 0)) :
    (x.1.l.get x.2).1 = shapeAt P j := by
  rw [h.entry j hj x hx hs]

/-- The member's radius is the message's. -/
theorem MemsAt.radius {cs : Codes} {ms : List Mem} {P : Par} {rad : ℕ → ℕ} {nT : ℕ}
    (h : MemsAt cs ms P rad nT) (j : Fin (shapesOf P).length) (hj : sampledAt P j) (x : Mem)
    (hx : x ∈ ms) (hs : SitsAt x (nT + (layOf P).tree.getD j.val 0) ((layOf P).part.getD j.val 0)) :
    (x.1.l.get x.2).2 = rad j.val := by
  rw [h.entry j hj x hx hs]

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.memsAt_iff
#print axioms VerifiableInference.Desc.K1.memsAt_of
#print axioms VerifiableInference.Desc.K1.MemsAt.shape
#print axioms VerifiableInference.Desc.K1.MemsAt.radius
