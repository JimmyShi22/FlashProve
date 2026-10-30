-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/HeadWalk.lean: where the record of the smallness test in the plan of the output
head's sub-proof comes from, and a bound on the head's number of position bits.

The plan (Head.planH2, OnBytes/Model/HeadPlan.lean) makes that record by HTailF2.shape, which is
shapeF (OnBytes/Model/Tail.lean), and then passes it through addTrees and ownerHeld. Both keep the
list of matrices and the number tau of combinations. The plan's last test refuses 2 ^ 30 or more
scalars; the number of position bits is at most the number of scalars.

Statements.
  ownerHeld_keeps  the comparison with the plan of the last group of layers keeps the matrices and
                   tau.
  needed_true      a test that has let the run pass was true.
  planH2_walk      where planH2 returns hp: shapeF has returned a record tl1 from which hp.tl has
                   its matrices and tau, and the number of scalars at tl1 is below 2 ^ 30.
  lt_le_slots      the number of position bits is at most the number of scalars.
  head_walk        where publicOf returns X: the record X.H.tl has the matrices and tau of the value
                   of shapeF at the settings' tau and lidb, and X.hS.lt < 2 ^ 30.

It rests on OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean (addTreesF_keeps), FoPublicA.lean
(borderMeans_keeps) and FoPublic.lean (public_H).

Limits. The list of matrices and the list of arrays that are read from another sub-proof stand under
"there are": which they are is not said. The bound on lt is far from sharp: the scan of the
configuration file refuses a line lt outside 4 to 16, but that this line's number is X.hS.lt is not
shown here. No toy: that publicOf returns at a configuration is shown by no term here. Nothing on
soundness or on hiding.
The program does not import this file.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify
open OnBytes OnBytes.Model Fo.BatRows

/-- The comparison with the plan of the last group of layers keeps the matrices and tau. -/
theorem ownerHeld_keeps {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (h : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : tl'.mats = tl.mats ∧ tl'.tau = tl.tau := by
  unfold Head.ownerHeld at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨tlB, hbm, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    obtain rfl := Except.ok.inj h
    exact Fo.Pub.borderMeans_keeps hbm
  · obtain ⟨_, h1, _⟩ := bindE_ok h
    cases h1

/-- A test that has let the run pass was true. -/
theorem needed_true {t : Bool} {why : String} {u : Unit} (h : Head.needed t why = .ok u) :
    t = true := by
  unfold Head.needed at h
  split at h
  · assumption
  · cases h

/-- The plan's record has the matrices and tau of a value of shapeF. -/
theorem planH2_walk {g : Settings} {h : Head.Shape} {L : Head.HL} {b : Head.Border}
    {O : Head.Owner} {NGr lkW : Nat} {hp : Head.HPlanH2}
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) :
    ∃ (m : Array TMat) (f : Array T2Foreign) (tl1 : HTailF2),
      ({ tau := g.tau, lidb := g.lidb } : HTailF2).shapeF m (Array.replicate m.size none) f
        #[false, false, true, false] g.tau = .ok tl1 ∧
      hp.tl.mats = tl1.mats ∧ hp.tl.tau = tl1.tau ∧ Head.slotsH h L tl1 lkW < 2 ^ 30 := by
  unfold Head.planH2 at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl1, hsh, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tla, Fa, Ta⟩, hadd, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨Tp, _, e⟩ := bindE_ok e
    obtain ⟨tlF, ho, e⟩ := bindE_ok e
    obtain ⟨_, hm, e⟩ := bindE_ok e
    obtain rfl := Except.ok.inj e
    obtain ⟨a1, a2⟩ := addTreesF_keeps _ _ _ _ _ _ _ _ hadd
    obtain ⟨o1, o2⟩ := ownerHeld_keeps ho
    exact ⟨_, _, tl1, hsh, o1.trans a1, o2.trans a2, of_decide_eq_true (needed_true hm)⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1

/-- The number of position bits is at most the number of scalars. -/
theorem lt_le_slots (h : Head.Shape) (L : Head.HL) (tl : HTailF2) (lkW : Nat) :
    h.lt ≤ Head.slotsH h L tl lkW := by
  have e : tscSlots h.lt 2 2 = 1 + (1 + (h.lt + 0) * 2 + 2 + 2) := rfl
  unfold Head.slotsH
  omega

/-- **The head's walk.** -/
theorem head_walk {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (hX : publicOf pol KL lay = .ok X) :
    (∃ (m : Array TMat) (f : Array T2Foreign) (tl1 : HTailF2),
      ({ tau := X.P.settings.tau, lidb := X.P.settings.lidb } : HTailF2).shapeF m
        (Array.replicate m.size none) f #[false, false, true, false] X.P.settings.tau = .ok tl1 ∧
      X.H.tl.mats = tl1.mats ∧ X.H.tl.tau = tl1.tau) ∧
      X.hS.lt < 2 ^ 30 := by
  obtain ⟨H0, h1, h2⟩ := Fo.Pub.public_H hX
  obtain ⟨m, f, tl1, hsh, hm, ht, hs⟩ := planH2_walk h1
  have e : X.H.tl = H0.tl := by rw [h2]
  exact ⟨⟨m, f, tl1, hsh, by rw [e]; exact hm, by rw [e]; exact ht⟩,
    Nat.lt_of_le_of_lt (lt_le_slots X.hS X.HLy tl1 X.P.lkW) hs⟩

end OnBytes.Model.Verify

#print axioms OnBytes.Model.Verify.ownerHeld_keeps
#print axioms OnBytes.Model.Verify.planH2_walk
#print axioms OnBytes.Model.Verify.lt_le_slots
#print axioms OnBytes.Model.Verify.head_walk
