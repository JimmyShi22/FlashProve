-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPlanH.lean.
The list of matrices in the plan of the output head's sub-proof.

MadeH (OnBytes/Tie/Pv/Lookup/Ends/FoKeysH.lean) asks that the smallness test in the head's plan has
the list of matrices that Head.matsH makes, and counts them. This file gets both from the run
equation of Head.planH2 (OnBytes/Model/HeadPlan.lean), through the routines that make and hand on
the smallness test.

* piecesF_keeps, shape_mats: HTailF2.shape puts the list of matrices that it is given, and its
  length, into the record.
* addTrees_keeps, borderMeans_mats, ownerHeld_keeps: the making of the list of arrays, and the
  comparison with the owner's record, keep both.
* planH2_mats: if Head.planH2 g h L b O NGr lkW returns hp, then the owner has a matrix number
  O.iXO, hp.tl.mats = Head.matsH h L b (1 + NGr) (that matrix's aId), and
  hp.tl.NM = hp.tl.mats.size.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.BatRows
import OnBytes.Model.HeadPlan

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model Fo.BatRows

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "thrown" : tactic => `(tactic| first
  | (cases e; done)
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "passed" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· thrown); obtain ⟨_, _, e⟩ := bindE_ok e))

theorem piecesF_keeps (tl r : HTailF2) (e : tl.piecesF = .ok r) :
    r.mats = tl.mats ∧ r.NM = tl.NM := by
  unfold HTailF2.piecesF at e
  obtain ⟨bz, _, e⟩ := bindE_ok e
  passed
  passed
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact ⟨rfl, rfl⟩

theorem shape_mats (tl r : HTailF2) (m : Array TMat) (txOf : Array (Option Nat))
    (f : Array T2Foreign) (hasU : Array Bool) (tau : Nat) (e : tl.shape m txOf f hasU tau = .ok r) :
    r.mats = m ∧ r.NM = m.size := by
  unfold HTailF2.shape HTailF2.shapeF at e
  dsimp only at e
  passed
  passed
  obtain ⟨_, _, e⟩ := bindE_ok e
  passed
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  passed
  passed
  exact piecesF_keeps _ r e

theorem addTrees_keeps (tl : HTailF2) (F : Fork) (T : Tail2) (nU aTX : Array Nat) (hb hbLine : Nat)
    (r : HTailF2 × Fork × Tail2) (e : tl.addTrees F T nU aTX hb hbLine = .ok r) :
    r.1.mats = tl.mats ∧ r.1.NM = tl.NM := by
  unfold HTailF2.addTrees HTailF2.addTreesF at e
  dsimp only at e
  passed
  passed
  passed
  passed
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  passed
  obtain ⟨_, _, e⟩ := bindE_ok e
  passed
  obtain ⟨_, _, e⟩ := bindE_ok e
  passed
  cases e
  exact ⟨rfl, rfl⟩

theorem borderMeans_mats {tl tl' : HTailF2} {iF o i : Nat}
    (h : tl.borderMeans iF o i = .ok tl') : tl'.mats = tl.mats ∧ tl'.NM = tl.NM := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      exact ⟨rfl, rfl⟩

theorem ownerHeld_keeps (O : Head.Owner) (NGr : Nat) (tl r : HTailF2) (Fp : Fork) (Tp : Tail2)
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok r) : r.mats = tl.mats ∧ r.NM = tl.NM := by
  unfold Head.ownerHeld at e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl1, h1, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl : tl1 = r := Except.ok.inj e
    exact borderMeans_mats h1
  · thrown

/-- The list of matrices in the head's plan. -/
theorem planH2_mats (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) :
    ∃ stream, O.tl.mats[O.iXO]? = some stream ∧
      hp.tl.mats = Head.matsH h L b (1 + NGr) stream.aId ∧ hp.tl.NM = hp.tl.mats.size := by
  unfold Head.planH2 at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · rename_i stream hs
    obtain ⟨st, hst, e⟩ := bindE_ok e
    obtain rfl : stream = st := Except.ok.inj hst
    obtain ⟨tl0, h0, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, h1, e⟩ := bindE_ok e
    dsimp only at e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨Tp1, _, e⟩ := bindE_ok e
    obtain ⟨tl2, h2, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl := Except.ok.inj e
    obtain ⟨a1, a2⟩ := shape_mats _ _ _ _ _ _ _ h0
    obtain ⟨b1, b2⟩ := addTrees_keeps _ _ _ _ _ _ _ _ h1
    obtain ⟨c1, c2⟩ := ownerHeld_keeps _ _ _ _ _ _ h2
    have hm : tl2.mats = Head.matsH h L b (1 + NGr) stream.aId := by rw [c1, b1, a1]
    refine ⟨stream, hs, hm, ?_⟩
    show tl2.NM = tl2.mats.size
    rw [c2, b2, a2, hm]
  · thrown

end Fo
