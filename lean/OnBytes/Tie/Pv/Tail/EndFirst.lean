-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndFirst.lean: the state of a sub-proof behind the draw of the batching element:
it has one coefficient for each slot, and its number of claims in the plan is the number that was
set (OnBytes/Model/Hide.lean: slots, setPlanClaims; OnBytes/Model/Trees.lean: t2Batch).

Definitions, statements and proofs. The theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndInv.lean) ask of the state that objectsF takes that it has one coefficient
for each slot, and read the plan's number of claims off it.
Main names:
  `slots_sized`: setting up the slots gives one coefficient for each slot.
  `change_ok`, `getL_ok`, `setL_ok`: what it says of three calls that they have returned.
  `setPlanClaims_ok`: the state behind is the state before, but for the number that is set.
  `t2Batch_keeps`: where t2Batch returns: the coefficients of the slots, the number of slots and the
    plan's number of claims are those before; that number is not 0.
  `first_state`: behind setPlanClaims n and t2Batch: one coefficient for each slot if there was one
    before; the plan's number of claims is n, and n is not 0.
Limits: the steps between the setting up of the slots and setPlanClaims, and those between t2Batch
and objectsF, differ by the kind of sub-proof and are not followed here.
OnBytes/Tie/Pv/Tail/EndInv.lean has rules for many of them.
-/
import OnBytes.Tie.Pv.Tail.EndDraw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

/-- Setting up the slots gives one coefficient for each slot. -/
theorem slots_sized (F : Fork) (n : Nat) : (F.slots n).LS.size = (F.slots n).ns := by
  simp [Fork.slots]

theorem change_ok (f : Fork → Option Fork) (F G : Fork) (c c' : Ctx) (u : Unit) :
    SubM.change f F c = .ok ((u, G), c') ↔ f F = some G ∧ c' = c := by
  simp only [SubM.change]
  cases f F with
  | none => simp [liftOption_none]
  | some H => simp [liftOption_some, eq_comm]

theorem getL_ok (x L L' : LinkCtx) (F F' : Fork) (c c' : Ctx) :
    (get : LinkM LinkCtx) L F c = .ok (((x, L'), F'), c') ↔
      x = L ∧ L' = L ∧ F' = F ∧ c' = c := by
  show (Except.ok (((L, L), F), c) : Except Failure (((LinkCtx × LinkCtx) × Fork) × Ctx)) = _ ↔ _
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

theorem setL_ok (N L L' : LinkCtx) (F F' : Fork) (c c' : Ctx) (u : PUnit) :
    (set N : LinkM PUnit) L F c = .ok (((u, L'), F'), c') ↔ L' = N ∧ F' = F ∧ c' = c := by
  show (Except.ok (((PUnit.unit, N), F), c) : Except Failure (((PUnit × LinkCtx) × Fork) × Ctx)) =
    _ ↔ _
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- The state behind setPlanClaims. -/
theorem setPlanClaims_ok (n : Nat) (F G : Fork) (c c' : Ctx) (u : Unit)
    (h : SubM.setPlanClaims n F c = .ok ((u, G), c')) : G = { F with planClaimsF := n } := by
  obtain ⟨h1, _⟩ := (change_ok _ _ _ _ _ _).1 h
  exact (Option.some.inj h1).symm

/-- What t2Batch keeps. -/
theorem t2Batch_keeps (used : Nat) (L L' : LinkCtx) (F G : Fork) (c c' : Ctx) (u : Unit)
    (h : t2Batch used L F c = .ok (((u, L'), G), c')) :
    G.LS = F.LS ∧ G.ns = F.ns ∧ G.planClaimsF = F.planClaimsF ∧ F.planClaimsF ≠ 0 := by
  unfold t2Batch at h
  simp only [bindL_ok, subL_ok, getL_ok, setL_ok, LinkM.mustAs, lift_ok, mustAs_ok, ask_ok,
    change_ok, SubM.batchBy, Option.some.injEq] at h
  obtain ⟨_, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, a1, _, _, _, ⟨⟨ha1, rfl, rfl⟩, rfl⟩,
    _, _, _, _, ⟨⟨⟨_, rfl⟩, rfl⟩, rfl⟩, _, _, _, _, ⟨⟨⟨_, rfl⟩, rfl⟩, rfl⟩,
    _, _, Ff, _, ⟨⟨hfill, rfl⟩, rfl⟩, dr, _, Fo, co, ⟨hopen, rfl⟩, _, _, Fb, _, ⟨⟨hb, rfl⟩, rfl⟩,
    _, _, _, _, ⟨⟨⟨hnz, rfl⟩, rfl⟩, rfl⟩, _, _, Fk, _, ⟨⟨hk, rfl⟩, rfl⟩, _, rfl, _⟩ := h
  obtain ⟨_, rfl⟩ := (lift_ok trBatchOpen _ _ _ _ _).1 hopen
  unfold Fork.batchBy at hb
  split_ifs at hb
  obtain rfl := Option.some.inj hb
  subst hfill hk ha1
  exact ⟨rfl, rfl, rfl, by simpa using hnz⟩

/-- Behind setPlanClaims n and t2Batch. -/
theorem first_state (n used : Nat) (L L' : LinkCtx) (F F1 G : Fork) (c c1 c' : Ctx) (u u' : Unit)
    (h1 : SubM.setPlanClaims n F c = .ok ((u, F1), c1))
    (h2 : t2Batch used L F1 c1 = .ok (((u', L'), G), c')) :
    (F.LS.size = F.ns → G.LS.size = G.ns) ∧ G.planClaimsF = n ∧ n ≠ 0 := by
  obtain ⟨e1, e2, e3, e4⟩ := t2Batch_keeps used L L' F1 G c1 c' u' h2
  have e := setPlanClaims_ok n F F1 c c1 u h1
  subst e
  exact ⟨fun hs => by rw [e1, e2]; exact hs, e3, e4⟩

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.slots_sized
#print axioms OnBytes.Tie.Pv.Tail.Port.t2Batch_keeps
#print axioms OnBytes.Tie.Pv.Tail.Port.first_state
