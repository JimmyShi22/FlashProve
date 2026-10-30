-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedHead.lean.
The head sub-proof's routines of the second pass are Fo.Fixed.

States:
  Fixed.liftV: a lifted routine of the channel whose returned value is known beforehand.
  Fixed.getAs, Fixed.held: the two ways in which the head takes a value that hangs on public
    numbers.
  fixed_noteConstant: Head.noteConstant reads the state's constant, to record it; it returns
    nothing, adds nothing and keeps the state.
  Fo.Fixed of Head.claimSquares, claimLedger, claimStream, claimJoin, claimPolicy, claimPlanes, each
    by the tactic fixed, to which this file adds Fixed.getAs and Fixed.held as rules. What Fo.Fixed
    says and what it leaves open stands in the head of OnBytes/Tie/Pv/Lookup/Ends/FoFixed.lean:
    value and list are chosen behind the routine's argument, the head's record R.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixed
import OnBytes.Model.Head

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Head

/-- A lifted routine of the channel whose returned value is known beforehand. -/
theorem Fixed.liftV {α : Type} (b : Blk α) (v : Option α)
    (h : ∀ c a c', b c = .ok (a, c') → v = some a) : Fixed (liftM b : SubM α) :=
  ⟨fun _ => v, fun _ => [], fun F c a G c' hr hs => by
    obtain ⟨a', c1, h1, e⟩ := (lift_ok _ _ _ _).1 hr
    have e1 : a = a' := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨h c a' c1 h1, Added.refl hs, rfl⟩⟩

theorem Fixed.getAs {α : Type} (name : String) (x : Option α) :
    Fixed (liftM (Head.getAs name x) : SubM α) :=
  Fixed.liftV _ x fun c a c' h => by
    unfold Head.getAs at h
    cases x with
    | none => cases h
    | some b =>
      have e : (b, c) = (a, c') := Except.ok.inj h
      rw [(Prod.mk.inj e).1]

theorem Fixed.held {α : Type} (x : Except String α) : Fixed (liftM (Head.held x) : SubM α) :=
  Fixed.liftV _ x.toOption fun c a c' h => by
    unfold Head.held at h
    cases x with
    | error n => cases h
    | ok b =>
      have e : (b, c) = (a, c') := Except.ok.inj h
      rw [← (Prod.mk.inj e).1]
      rfl

macro_rules | `(tactic| fixed_rule) => `(tactic| with_reducible first
  | exact Fixed.getAs _ _ | exact Fixed.held _)

theorem fixed_noteConstant (g : String) : Fixed (Head.noteConstant g) :=
  Fixed.unit fun F c a G c' hr hs => by
    unfold Head.noteConstant at hr
    obtain ⟨s, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 hr
    have e : ((F, F), c) = ((s, F1), c1) := Except.ok.inj h1
    have e1 : F = F1 := congrArg (fun x : (Fork × Fork) × Ctx => x.1.2) e
    unfold Head.noteH at h2
    obtain ⟨_, _, _, e3⟩ := (lift_ok _ _ _ _).1 h2
    have e2 : G = F1 := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e3
    rw [e2, ← e1]
    exact ⟨Added.refl hs, rfl⟩

theorem fixed_claimSquares (R : Head.Run) : Fixed (Head.claimSquares R) := by fixed
theorem fixed_claimLedger (R : Head.Run) : Fixed (Head.claimLedger R) := by fixed
theorem fixed_claimStream (R : Head.Run) : Fixed (Head.claimStream R) := by fixed
theorem fixed_claimPolicy (R : Head.Run) : Fixed (Head.claimPolicy R) := by fixed
theorem fixed_claimJoin (R : Head.Run) : Fixed (Head.claimJoin R) := by fixed
theorem fixed_claimPlanes (R : Head.Run) : Fixed (Head.claimPlanes R) := by fixed

end Fo
