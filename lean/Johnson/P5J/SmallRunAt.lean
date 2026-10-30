-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/SmallRunAt.lean: THE SEGMENT's SORT AND ITS RUN's NAME, CLOSED: at each of the 25
segments of the full size's written list (`P5J.fullLinks`, Johnson/P5J/MeansQ.lean) the table's name
"small" at the approximate range proof's place stands for just one run: "K8.equations", one place in
front. A test with code, its value by the kernel, two negative tests, and the statement.

  `smallRunB links l`: the list has a sort at l, and `First.runsOf` at that sort, at place 5 + o and
    the name "small", is [(4 + o, "K8.equations")], o := if l = 24 then 1 else 0.
  `smallRun_all`: it says yes at all l < 25: `decide +kernel`.
  **`smallRun_at`**: ∀ l ≤ 24, ∃ sub, fullLinks[l]? = some sub ∧ runsOf sub (5 + o) "small" = ….
  NEGATIVE TESTS: `smallRun_beyond`: at l = 25 it says no (no segment) · `smallRun_turned`: at the
    list with the head's segment in front it says no at 0 (the head's place is one further).

OBJECT: the written list and the table's map of names. USER: Johnson/K8Q21R/SmallRunAtLinks.lean;
meant: a field of K8LeftC. LETTERS: none.
Limits. A closed fact on the table's own word. It holds at the bytes of `runsOf`
(Johnson/Desc/First/Borders.lean) over which it is compiled. Nothing on soundness.
-/
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc.First (ModelPart runsOf)

/-- The test at one segment. -/
def smallRunB (links : List ModelPart) (l : ℕ) : Bool :=
  match links[l]? with
  | some sub =>
    runsOf sub (5 + if l = 24 then 1 else 0) "small" ==
      [(4 + if l = 24 then 1 else 0, "K8.equations")]
  | none => false

theorem smallRun_all : (List.range 25).all (smallRunB fullLinks) = true := by decide +kernel

/-- Beyond the list it says no. -/
theorem smallRun_beyond : smallRunB fullLinks 25 = false := by decide +kernel

/-- With the head's segment in front it says no there. -/
theorem smallRun_turned : smallRunB (ModelPart.head :: fullLinks) 0 = false := by decide +kernel

/-- **The segment's sort and its run's name.** -/
theorem smallRun_at (l : ℕ) (hl : l ≤ 24) :
    ∃ sub, fullLinks[l]? = some sub ∧
      runsOf sub (5 + if l = 24 then 1 else 0) "small" =
        [(4 + if l = 24 then 1 else 0, "K8.equations")] := by
  have h := List.all_eq_true.1 smallRun_all l (List.mem_range.2 (by omega))
  unfold smallRunB at h
  cases e : fullLinks[l]? with
  | none => rw [e] at h; cases h
  | some sub =>
    rw [e] at h
    exact ⟨sub, rfl, by simpa using h⟩

end P5J

#print axioms P5J.smallRun_all
#print axioms P5J.smallRun_beyond
#print axioms P5J.smallRun_turned
#print axioms P5J.smallRun_at
