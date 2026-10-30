-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/ShapeAtNo.lean: THE CLAUSE "shape" OF "the statement's group at
a link is the written list's" (`ShapesAre`, kind K10): THE MESSAGE AT A MEMBER's NUMBER HAS THE
WRITTEN LIST's SHAPE: at a state, from one fact along the fold and a test with code on public data.
GENERAL IN THE LINK: no bound on its number. A definition with code and theorems. A law file; no
running text imports it.
  `shape_at_no`     one number: atFirstShapes M s = true (the fold's fact "msgShapes") · o below the
                    number of the statement's messages · M[o]? = some sh ⊢ (s.st.oracles[o]?).map
                    (·.shape) = some sh. By the door's msgShape_at
                    (Johnson/Desc/K12/Door/MsgShapes.lean).
  `shapesNoB M n lo no`   THE TEST, ON PUBLIC DATA: at every place i of lo: no i lies below n, and
                    the plan's list of shapes has lo's i-th shape at no i.
  `shape_clause`    the test's yes at n := N.msgsAt p · the promise's bookAt N p s · atFirstShapes
                    M s ⊢ ∀ i, (s.st.oracles[no i]?).map (·.shape) = some (lo.get i).1.
  `shapesNoB_yes`, `shapesNoB_shape`, `shapesNoB_late`   THE TEST CAN SAY NO: by Lean's kernel at
                    small written lists.

Limits. The test is evaluated at no plan here. bookAt and
atFirstShapes are premises on the state. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Look.K3MaskOkTools
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open VerifiableInference.OnPublicFiles (bookAt_sizes)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S Numbers bookAt)
open VerifiableInference.Desc.K12.Door (atFirstShapes msgShape_at)

/-- One number. -/
theorem shape_at_no {s : S} {M : List OracleShape} (hshapes : atFirstShapes M s = true) {o : ℕ}
    {sh : OracleShape} (ho : o < s.st.oracles.size) (hM : M[o]? = some sh) :
    (s.st.oracles[o]?).map (·.shape) = some sh :=
  (msgShape_at hshapes o ho).trans hM

/-- **THE TEST**, on public data. -/
def shapesNoB (M : List OracleShape) (n : ℕ) (lo : List (OracleShape × ℕ))
    (no : Fin lo.length → ℕ) : Bool :=
  (List.finRange lo.length).all fun i => decide (no i < n) && M[no i]? == some (lo.get i).1

/-- **The clause "shape", at every member.** -/
theorem shape_clause {s : S} {M : List OracleShape} {N : Numbers} {p : Option Place}
    {lo : List (OracleShape × ℕ)} {no : Fin lo.length → ℕ}
    (hT : shapesNoB M (N.msgsAt p) lo no = true) (hbook : bookAt N p s = true)
    (hshapes : atFirstShapes M s = true) (i : Fin lo.length) :
    (s.st.oracles[no i]?).map (·.shape) = some (lo.get i).1 := by
  have h := List.all_eq_true.1 hT i (List.mem_finRange i)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact shape_at_no hshapes (by rw [(bookAt_sizes hbook).2]; exact h.1) h.2

/-! ## The test can say no -/

/-- Two small shapes. -/
def shA : OracleShape := { mainRows := 1 }
def shB : OracleShape := { mainRows := 2 }

theorem shapesNoB_yes : shapesNoB [shA, shB] 2 [(shB, 7), (shA, 7)]
    (fun i => if i.val = 0 then 1 else 0) = true := by decide +kernel

theorem shapesNoB_shape : shapesNoB [shA, shB] 2 [(shB, 7), (shA, 7)] (fun i => i.val) = false := by
  decide +kernel

theorem shapesNoB_late : shapesNoB [shA, shB] 1 [(shB, 7), (shA, 7)]
    (fun i => if i.val = 0 then 1 else 0) = false := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shape_at_no
#print axioms VerifiableInference.Desc.LinkJoin.shape_clause
#print axioms VerifiableInference.Desc.LinkJoin.shapesNoB_yes
#print axioms VerifiableInference.Desc.LinkJoin.shapesNoB_shape
#print axioms VerifiableInference.Desc.LinkJoin.shapesNoB_late
