-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPlanSize.lean.
The record of the smallness test in each of the three plans counts its own list of matrices.

Main names:
  `planG_size`: Layer.planG P g O = .ok hp gives hp.tl.NM = hp.tl.mats.size.
  `planA_size`: Attention.plan settings i cf = .ok P gives P.seam.tl.NM = P.seam.tl.mats.size.
  `planH2_size`: Head.planH2 .. = .ok hp gives hp.tl.NM = hp.tl.mats.size.
By Fo.shapeF_size, where the record is made, and Fo.Core of the plans' later steps
(OnBytes/Tie/Pv/Lookup/Ends/FoTailCore.lean).
It is the premise hN of Fo.topOf_eq (OnBytes/Tie/Pv/Lookup/Ends/FoTopOf.lean) at a plan's record,
of Fo.door_rows, Fo.g_door_rows, Fo.a_door_rows and Fo.h_door_rows
(OnBytes/Tie/Pv/Lookup/Ends/FoRowsRun.lean), and of Fo.g_bat_rows, Fo.a_bat_rows and Fo.h_bat_rows
(OnBytes/Tie/Pv/Lookup/Ends/FoBatRun.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailCore

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model
open Fo.BatRows (bindE_ok ite_ok)

theorem pureE_ok {ε α : Type} {a b : α} (h : (pure a : Except ε α) = .ok b) : b = a :=
  (Except.ok.inj h).symm

theorem planG_size (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : hp.tl.NM = hp.tl.mats.size := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have k1 : tl1.NM = tl1.mats.size := (addTreesF_core hA).size (shapeF_size hS).1
  have k2 : (tl1.ownerIs g).NM = (tl1.ownerIs g).mats.size := (ownerIs_core tl1 g).size k1
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
      exact (borderMeans_core hB).size k2
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

theorem seamShape_size {g : Settings} {m : Array TMat} {tau col0F ktO aO : Nat}
    {s : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s) :
    s.tl.NM = s.tl.mats.size := by
  unfold Attention.Seam.shape at e
  dsimp only at e
  alive
  alive
  obtain ⟨tl, hS, e⟩ := bindE_ok e
  cases e
  exact (shapeF_size hS).1

theorem seamPlan_core {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') : Core s.tl s'.tl := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, hr, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact addTreesF_core hr

theorem planA_size (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) :
    P.seam.tl.NM = P.seam.tl.mats.size := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  exact (seamPlan_core h1).size (seamShape_size h0)

theorem ownerHeld_core {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : Core tl tl' := by
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
    exact borderMeans_core hB
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

theorem planH2_size (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : hp.tl.NM = hp.tl.mats.size := by
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
    exact (ownerHeld_core hO).size ((addTreesF_core hA).size (shapeF_size hS).1)
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

end Fo
