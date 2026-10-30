-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/LayoutTies.lean: THE TIE OF LETTERS `Meaning.ShapesTied` FROM A TEST WITH CODE. One
statement, proved.

  **`shapesTied_of_B`**: a yes of `shapesTiedB` (Johnson/Road/K4/LayoutTiesB.lean) at the plain
    lists L gives `Meaning.ShapesTied` (Johnson/Goal/Meaning/LaidInsideSeats.lean) at the members
    `msOf L` (Johnson/Desc/Sound/PlanMemProofs.lean). By `mem_msOf`: a member of `msOf L` is shape
    number i and seat number i of an entry of L, i below the number of the entry's shapes.

OBJECT: no block's text: public letters. USERS: K4PlanTests.lean · K4PlanClosed.lean · K4PlanAt.lean
(this folder); meant: whoever spends `Meaning.seat_inside_members`. LETTERS: all seven, free.

Limits. `shapesTiedB` has run at two toys alone: that it says yes at the real plan's letters is
shown nowhere. (Where this and lean/THEOREM.md
differ, the page holds.) The other direction (the tie gives the test's yes) is not said. Nothing on
soundness.
K04_law IS NOT PROVED BY THIS.
-/
import Johnson.Road.K4.LayoutTiesB
import Johnson.Goal.Meaning.LaidInsideSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Road.K4.LayoutTies
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.Desc (MemberLists padKey)
open VerifiableInference.Desc.Sound (msOf mem_msOf seatOf numOf)

/-- **A yes of the test gives the tie of letters at the members of the plain lists.** -/
theorem shapesTied_of_B {codes : OnBytes.Codes} {shape : ReqShape} {layout : ReqLayout}
    {num arr : ℕ → ℕ → ℕ} {L : MemberLists} {grp : ℕ → List (ℕ × ℕ)}
    (h : shapesTiedB codes shape layout num arr L grp = true) :
    Meaning.ShapesTied codes shape layout num arr (msOf L) grp := by
  intro l as A m hl hA hm k hk y hy hg hn
  unfold shapesTiedB at h
  obtain ⟨p, hp, e⟩ := mem_msOf L y hy
  obtain ⟨s, i⟩ := y
  simp only at e
  subst e
  have hx : (as, l) ∈ layout.link.zipIdx := List.mem_zipIdx_iff_getElem?.2 hl
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h (as, l) hx) A hA
  simp only [hm] at h1
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h1 k
    (List.mem_range.2 hk)) p hp) i.val (List.mem_range.2 i.isLt)
  have hg' : p.2.getD i.val (0, 0) ∈ grp k := hg
  have hn' : arr (p.2.getD i.val (0, 0)).1 (p.2.getD i.val (0, 0)).2 = num l A.message := hn
  have e1 : p.1.getD i.val default = p.1.get i := List.getD_eq_getElem _ _ i.isLt
  rw [Bool.or_eq_true, Bool.or_eq_true] at h2
  rcases h2 with (h2 | h2) | h2
  · have hc : (grp k).contains (p.2.getD i.val (0, 0)) = true := List.contains_iff_mem.2 hg'
    rw [hc] at h2
    cases h2
  · exact absurd hn' (bne_iff_ne.1 h2)
  · rw [e1] at h2
    exact beq_iff_eq.1 h2

end Johnson.Road.K4.LayoutTies

#print axioms Johnson.Road.K4.LayoutTies.shapesTied_of_B
