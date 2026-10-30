-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirstLast.lean: WHAT THE KEY FILE's THIRD CHAIN's START ASKS OF THE FIRST CHAIN's LAST
STATE (`Last₁`, E2E/KeyThreadsLaid.lean: five clauses) FOLLOWS FROM A TEST ON THE FIRST CHAIN's
SHAPE; and that test accepts E2E/KeyShapeAtFull.lean's last term. Definitions, statements and
proofs. A test of the verifier's on a state: NOTHING IS SHOWN OF ANY PROVER.

  **`last₁S`**: the five clauses on the shape: a claim is laid; a mask's number just where masks are
    sent ahead; the three numbers (E2E/KeyShapeDoor.lean's `numbersS`); the codes; as many roots as
    the book has trees.
  **`last₁_of_S`**: where it accepts a state's shape, `Last₁` holds of the state.
  **`last_full`**: it accepts `T19`, at the written codes and shape. By Lean's kernel. `last_early`:
    a negative test: it rejects `T17`.

Limits.
- One direction: enough, not needed.
- That a run's last state has the shape `T19` is not shown here.


-/
import E2E.KeyShapeAtFull
import E2E.KeyThreadsLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (FirstState)
open AtPublicFiles.KeyShape (Pub1)

/-- **What the third chain's start asks of the first chain's last state, on the shape.** -/
def last₁S (codes : Codes) (S : LinShape) (a : Sh₁B) : Bool :=
  match a.2.back.door with
  | some l =>
    (l.mask.isSome == S.masksAhead) && numbersS S a.1.st l && decide (a.1.st.codes = codes) &&
      (a.1.roots == a.1.book.trees.length)
  | none => false

/-- **Where it accepts a state's shape, the five clauses hold of the state.** -/
theorem last₁_of_S (Q : Pub1) (cs codes : Codes) (s : FirstState)
    (h : last₁S codes Q.one.lin (sh₁B Q cs s) = true) : Last₁ codes Q.one.lin s := by
  unfold last₁S at h
  have e : (sh₁B Q cs s).2.back.door = s.lin.map (linSh Q.one.lin cs) :=
    door_of_back Q.one.lin cs s
  rw [e] at h
  cases hl : s.lin with
  | none =>
    rw [hl] at h
    cases h
  | some l =>
    rw [hl] at h
    have h' : (((l.mask.isSome == Q.one.lin.masksAhead) &&
        numbersS Q.one.lin (stSh s.d.st) (linSh Q.one.lin cs l) &&
        decide (s.d.st.codes = codes)) &&
        (s.d.roots == (s.d.book.trees.toList.map treeSh).length)) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h'
    rw [numbersS_eq] at b
    rw [List.length_map, Array.length_toList] at d
    exact ⟨l, hl, a, b, c, d⟩

namespace Full

/-- **It accepts the last term.** -/
theorem last_full : last₁S CF SF T19 = true := by decide +kernel

/-- A negative test: in front of "w.1.send" it rejects. -/
theorem last_early : last₁S CF SF T17 = false := by decide +kernel

end Full

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.last₁_of_S
#print axioms AtPublicFiles.AtFiles.Full.last_full
#print axioms AtPublicFiles.AtFiles.Full.last_early
