-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoMadeTail.lean: the record of the smallness test in each of the three
plans holds, as its lookup's numbers, what Forest.shape makes of the test's two calls, but for the
numbers of padding keys, which are left as they are.

 - MadeZ tl: Fo.Made (OnBytes/Tie/Pv/Lookup/Ends/FoShapes.lean) at the two calls of tl, tl.lidb and
   tl.f9.
 - ZKeep a b: b has a's z1, z2, lidb and f9. ZKeep.made: so MadeZ passes from a to b.
 - piecesF_madeZ, shapeF_madeZ: where HTailF2.piecesF, HTailF2.shapeF return tl': MadeZ tl'.
 - addTreesF_zkeep, borderMeans_zkeep, ownerIs_zkeep, seamPlan_zkeep, ownerHeld_zkeep: the plans'
   later steps keep the four fields.
 - planG_madeZ, seamShape_madeZ, planA_madeZ, planH2_madeZ: so MadeZ at the record in what
   Layer.planG, Attention.Seam.shape, Attention.plan and Head.planH2 return.
The walks of the routines follow OnBytes/Tie/Pv/Lookup/Ends/FoTailCore.lean's and
OnBytes/Tie/Pv/Lookup/Ends/FoPlanSize.lean's, which keep other fields.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a plan is made.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoMadeLay
import OnBytes.Tie.Pv.Lookup.Ends.FoPlanSize
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicANm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Tie.Pv.Tail.Port
open Fo.BatRows (bindE_ok ite_ok)

/-- The record of a smallness test's lookup is what Forest.shape makes of the test's two calls, but
for its numbers of padding keys. -/
def MadeZ (tl : HTailF2) : Prop := Made #[tl.z1.call, tl.z2.call] tl.lidb tl.f9

/-- b has a's two calls, cap on a tree's depth and record of the lookup's numbers. -/
def ZKeep (a b : HTailF2) : Prop := b.z1 = a.z1 ∧ b.z2 = a.z2 ∧ b.lidb = a.lidb ∧ b.f9 = a.f9

theorem ZKeep.made {a b : HTailF2} (h : ZKeep a b) (ha : MadeZ a) : MadeZ b := by
  unfold MadeZ
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  exact ha

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

/-! ### the plan's steps -/

theorem piecesF_madeZ {tl tl' : HTailF2} (e : tl.piecesF = .ok tl') : MadeZ tl' := by
  unfold HTailF2.piecesF at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  alive
  obtain ⟨f9, hs, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact ⟨f9, hs, rfl⟩

theorem shapeF_madeZ {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (e : tl.shapeF m txOf f hasU tau = .ok tl') : MadeZ tl' := by
  unfold HTailF2.shapeF at e
  dsimp only at e
  alive
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  alive
  exact piecesF_madeZ e

theorem addTreesF_zkeep {tl tl' : HTailF2} {F F' : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    ZKeep tl tl' := by
  obtain ⟨-, -, e⟩ := addTreesF_fits tl tl' F F' T T' nU aTX hb hbLine h
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem borderMeans_zkeep {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (e : tl.borderMeans iF ownerNo index = .ok tl') : ZKeep tl tl' := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem ownerIs_zkeep (tl : HTailF2) (no : Nat) : ZKeep tl (tl.ownerIs no) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### the three plans -/

theorem planG_madeZ (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : MadeZ hp.tl := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have k1 : MadeZ tl1 := (addTreesF_zkeep hA).made (shapeF_madeZ hS)
  have k2 : MadeZ (tl1.ownerIs g) := (ownerIs_zkeep tl1 g).made k1
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact k2
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact (borderMeans_zkeep hB).made k2
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem seamShape_madeZ {g : Settings} {m : Array TMat} {tau col0F ktO aO : Nat}
    {s : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s) :
    MadeZ s.tl := by
  unfold Attention.Seam.shape at e
  dsimp only at e
  alive
  alive
  obtain ⟨tl, hS, e⟩ := bindE_ok e
  cases e
  exact shapeF_madeZ hS

theorem seamPlan_zkeep {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') : ZKeep s.tl s'.tl := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, hr, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact addTreesF_zkeep hr

theorem planA_madeZ (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) : MadeZ P.seam.tl := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  exact (seamPlan_zkeep h1).made (seamShape_madeZ h0)

theorem ownerHeld_zkeep {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : ZKeep tl tl' := by
  unfold Head.ownerHeld at e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hB, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl := pureE_ok e
    exact borderMeans_zkeep hB
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

theorem planH2_madeZ (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : MadeZ hp.tl := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact (ownerHeld_zkeep hO).made ((addTreesF_zkeep hA).made (shapeF_madeZ hS))
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

end Fo
