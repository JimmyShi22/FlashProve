-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ReachHeld.lean: shape_reach (Honest/Thread/Shape.lean) WHERE THE STRONG Carries FAILS AT
SOME MEMBERS. General in the record Shape, the list of members and the set U of those members;
nothing is evaluated.

* ReachHeld Z ft bs start U: Reach, where at each member in U the step that was taken has the
  member's named tests on values passing at its own rounds and columns.
* ReachHeld.reach: it is a Reach.
* **shape_reachU**: where every member has the strong Carries or lies in U with CarriesU: along a
  state so reached the shape's run, where it returns, returns that state's shape.

Limits. Implications. That a thread's states are so reached, and at which U, is the caller's. Nothing
on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc
open ProofFile.Honest
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

variable {S Cl P : Type}

/-- **Reached, with the values held at the members in U.** -/
inductive ReachHeld (Z : Shape S) (ft : Nat) (bs : List (Block S Cl)) (start : P → S)
    (U : Nat → Prop) : Nat → P × S → Prop
  | zero (z : P) : ReachHeld Z ft bs start U 0 (z, start z)
  | succ {k : Nat} {z : P} {s s' : S} {b : Block S Cl} {R : List Fmt.RoundView} {c : List OpenedColumn} :
      ReachHeld Z ft bs start U k (z, s) → bs[k]? = some b → R.length = b.rounds.length →
      b.step ft s R c = .ok (s', c.length) →
      (U k → Z.vals k s (R.map noDigest) (b.shown ft R c) = true) →
      ReachHeld Z ft bs start U (k + 1) (z, s')

/-- It is a Reach. -/
theorem ReachHeld.reach {Z : Shape S} {ft : Nat} {bs : List (Block S Cl)} {start : P → S}
    {U : Nat → Prop} {k : Nat} {a : P × S} (h : ReachHeld Z ft bs start U k a) :
    Reach ft bs start k a := by
  induction h with
  | zero z => exact Reach.zero z
  | succ _ hb hR hs _ ih => exact Reach.succ ih hb ⟨_, _, hR, hs⟩

/-- **shape_reach, WITH THE WEAK Carries AT THE MEMBERS IN U.** -/
theorem shape_reachU (Z : Shape S) {ft : Nat} {bs : List (Block S Cl)} {start : P → S}
    {U : Nat → Prop} (hC : ∀ j, Carries bs ft Z j ∨ (U j ∧ CarriesU bs ft Z j)) {b : Nat}
    {a : P × S} (h : ReachHeld Z ft bs start U b a) :
    ∀ e, Z.run b (Z.sh (start a.1)) = .ok e → e = Z.sh a.2 := by
  induction h with
  | zero z =>
    intro e he
    exact (Except.ok.inj he).symm
  | @succ k z s s' blk R c _ hb _ hs hv ih =>
    intro e he
    have he' : (Z.run k (Z.sh (start z))).bind (Z.g k) = .ok e := he
    cases hk : Z.run k (Z.sh (start z)) with
    | error w =>
      rw [hk] at he'
      cases he'
    | ok e' =>
      rw [hk] at he'
      have e1 := ih e' hk
      subst e1
      rcases hC k with hS | ⟨hu, hW⟩
      · exact hS _ hb _ _ _ _ _ _ hs he'
      · exact hW _ hb _ _ _ _ _ _ hs he' (hv hu)

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.ReachHeld.reach
#print axioms Johnson.AtFull.Shape.Scope.shape_reachU
