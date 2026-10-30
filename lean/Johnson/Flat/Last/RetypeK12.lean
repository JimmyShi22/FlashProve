-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RetypeK12.lean: THE PROXIMITY TEST's BLOCK, CARRIED TO ANOTHER TYPE OF CLAIMS
(`Block.retype`, Johnson/Desc/Block.lean), IS THE PROXIMITY TEST's BLOCK AT THAT TYPE: an equation
of blocks, field by field.

Why. A file's description lays its later chains carried to the file's own type of claims
(`Chain.retype`). The law of the last chain's third block is said of `(proximityTestKind X p : Block T Cl).inside
enter leave` at the file's type Cl; the seat types the block at Unit and the frame carries it. That
the two are ONE block is what the list of the last chain's pieces asks (`last_list_at`,
Johnson/Flat/Last/LastCut.lean: its premise hc).
  `retype_andThen`, `retype_at`, `retype_asks`, `retype_inside`: carrying goes through the four
    makers of blocks that the kind's frame uses.
  `retype_stagesFrom`, `retype_k12`: so through the frame's text (Johnson/Desc/K12/Frame.lean).
  `retype_onOwn`: **`(onOwn (proximityTestKind X p : Block T12 Cl)).retype = onOwn (proximityTestKind X p : Block T12 Cl')`**.
Beside it: Johnson/Flat/Last/AnyClaims.lean has that the two blocks RUN alike (name, rounds,
decision); here all nine fields.
`retype_k12`'s proof writes out no text of the frame:
so it does not hang on the frame's words.

Limits. Equations of records. Nothing on what the block does. Nothing on soundness.
-/
import Johnson.Desc.K12.Frame
import Johnson.Desc.K12.Seat.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S T Cl Cl' : Type}

theorem retype_andThen (name : String) (p q : Block S Cl) :
    ((p.andThen name q).retype : Block S Cl') = (p.retype).andThen name (q.retype) := by
  have e : ((p.planOk && q.planOk) && (p.claims ++ q.claims).isEmpty) =
      ((p.planOk && p.claims.isEmpty) && (q.planOk && q.claims.isEmpty)) := by
    have a : (p.claims ++ q.claims).isEmpty = (p.claims.isEmpty && q.claims.isEmpty) := by
      cases p.claims <;> rfl
    rw [a]
    cases p.planOk <;> cases q.planOk <;> cases p.claims.isEmpty <;> cases q.claims.isEmpty <;> rfl
  exact congrArg
    (fun x => ({ ((p.andThen name q).retype : Block S Cl') with planOk := x } : Block S Cl')) e

theorem retype_inside (enter : S → Except String T) (b : Block T Cl)
    (leave : S → T → Except String S) :
    ((b.inside enter leave).retype : Block S Cl') = (b.retype).inside enter leave := by
  have e : ((b.planOk && b.claims.isEmpty && b.after.isEmpty) && true) =
      ((b.planOk && b.claims.isEmpty) && true && b.after.isEmpty) := by
    cases b.planOk <;> cases b.claims.isEmpty <;> cases b.after.isEmpty <;> rfl
  exact congrArg
    (fun x => ({ ((b.inside enter leave).retype : Block S Cl') with planOk := x } : Block S Cl')) e

namespace K12
open Fmt.M1 (Stage)

theorem retype_at (x : Part T) (name : String) (place : Place) (l : Laid) :
    ((x.at name place l : Block T Cl).retype : Block T Cl') = x.at name place l :=
  congrArg (fun y => ({ (x.at name place l : Block T Cl') with planOk := y } : Block T Cl'))
    (Bool.and_true x.planOk)

theorem retype_asks (name : String) (place : Place) (ok : T → Bool) :
    ((asks name place ok : Block T Cl).retype : Block T Cl') = asks name place ok := rfl

theorem retype_stagesFrom (X : Parts T) (p : P12) :
    ∀ (rest : List Stage) (j : Nat) (cur : Stage) (l : Laid),
      ((stagesFrom X p j cur rest l : Block T Cl).retype : Block T Cl') =
        stagesFrom X p j cur rest l
  | [], j, cur, l => by
    unfold stagesFrom
    exact retype_at _ _ _ _
  | next :: rest, j, cur, l => by
    unfold stagesFrom
    rw [retype_andThen, retype_andThen, retype_andThen, retype_andThen, retype_at, retype_at,
      retype_at, retype_asks, retype_stagesFrom X p rest]

/-- Carrying goes through the frame's last step: the name, the place, what stands before and a
further test on the plan are laid over. -/
theorem retype_named (b : Block T Cl) (b' : Block T Cl') (A : Bool) (n : String) (pl : Place)
    (bf : List (Nat × Nat)) (h : (b.retype : Block T Cl') = b') :
    (({ b with name := n, place := pl, before := bf, planOk := A && b.planOk } :
      Block T Cl).retype : Block T Cl') =
      { b' with name := n, place := pl, before := bf, planOk := A && b'.planOk } := by
  subst h
  exact congrArg (fun x => ({ (b.retype : Block T Cl') with
    name := n, place := pl, before := bf, planOk := x } : Block T Cl')) (Bool.and_assoc _ _ _)

/-- **The proximity test's block, carried, is the proximity test's block.** -/
theorem retype_k12 (X : Parts T) (p : P12) :
    ((proximityTestKind X p : Block T Cl).retype : Block T Cl') = proximityTestKind X p := by
  unfold proximityTestKind
  rcases p.nums.stages with _ | ⟨first, rest⟩
  · rfl
  · rcases H2U.roundsOfNums p.nums with _ | rs
    · rfl
    · rcases H2U.testOracles p.nums with _ | os
      · rfl
      · refine retype_named _ _ _ _ _ _ ?_
        rw [retype_andThen, retype_andThen, retype_andThen, retype_at, retype_at, retype_asks,
          retype_stagesFrom]

/-- **The request's own test at its seat, carried, is the request's own test at its seat.** -/
theorem retype_onOwn (X : Parts T12) (p : P12) :
    ((Seat.onOwn (proximityTestKind X p : Block T12 Cl)).retype : Block Third.S₃ Cl') = Seat.onOwn (proximityTestKind X p) := by
  unfold Seat.onOwn
  rw [retype_inside, retype_k12]

end K12

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.retype_andThen
#print axioms VerifiableInference.Desc.retype_inside
#print axioms VerifiableInference.Desc.K12.retype_k12
#print axioms VerifiableInference.Desc.K12.retype_onOwn
