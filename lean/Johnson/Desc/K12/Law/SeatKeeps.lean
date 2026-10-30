-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.Seat.Own
import Johnson.Desc.K12.AtFinish
import Johnson.Desc.SeatGuard
import Johnson.Desc.K12.FrameLaws
/-
Johnson/Desc/K12/Law/SeatKeeps.lean: THE SEATED BLOCK KEEPS K12's «before» AND DECLARED ROUNDS: at the four seats of a proximity test (onGu · onGomega · onOwn · atFinish), under a guard (Block.guarded) and at another type of claims (Block.retype). Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  k12_before: where the block's test on the plan says yes, the block's «before» is the place's.
  Keeps b' b: b' has b's «before» and declared rounds. keeps_inside · keeps_guarded · keeps_retype · Keeps.trans: by unfolding.
  keeps_onGu · keeps_onGomega · keeps_onOwn · keeps_atFinish.
  seat_pays: what BeforeK12.lean's premises hbef | hrd | hr ask, for any block that keeps proximityTestKind X p's.
Limits: it says nothing of how a description's maker lays the seats, nor of any other wrapper than the three named.

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem k12_before {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : (proximityTestKind X p : Block T Cl).before = p.before := by
  unfold proximityTestKind at hp ⊢
  split
  · rfl
  · simp at hp

/-- b' has b's «before» and declared rounds. -/
def Keeps {S T Cl Cl' : Type} (b' : Block S Cl') (b : Block T Cl) : Prop :=
  b'.before = b.before ∧ b'.rounds = b.rounds

theorem Keeps.trans {S T U Cl Cl' Cl'' : Type} {a : Block S Cl} {b : Block T Cl'} {c : Block U Cl''}
    (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem keeps_inside {S T Cl : Type} (enter : S → Except String T) (b : Block T Cl)
    (leave : S → T → Except String S) : Keeps (Block.inside enter b leave) b := ⟨rfl, rfl⟩

theorem keeps_guarded {S Cl : Type} (same : S → S → Bool) (but : Place → Bool) (b : Block S Cl) :
    Keeps (b.guarded same but) b := ⟨rfl, rfl⟩

theorem keeps_retype {S Cl Cl' : Type} (b : Block S Cl) : Keeps (b.retype (Cl' := Cl')) b :=
  ⟨rfl, rfl⟩

theorem keeps_onGu (b : Block T12 Unit) : Keeps (Seat.onGu b) b := ⟨rfl, rfl⟩
theorem keeps_onGomega (b : Block T12 Unit) : Keeps (Seat.onGomega b) b := ⟨rfl, rfl⟩
theorem keeps_onOwn {Cl : Type} (b : Block T12 Cl) : Keeps (Seat.onOwn b) b := ⟨rfl, rfl⟩
theorem keeps_atFinish (p : P12) : Keeps (atFinish p) (proximityTestKind guardedProximityTestParts p : Block T12 Unit) :=
  ⟨rfl, rfl⟩

/-- What the law of «sent in time» asks of the seated block. -/
theorem seat_pays {S T Cl Cl' : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (b : Block S Cl')
    (hk : Keeps b (proximityTestKind X p : Block T Cl)) :
    b.before = p.before ∧ H2U.roundsOfNums p.nums = some b.rounds := by
  refine ⟨hk.1.trans (k12_before X p hp), ?_⟩
  rw [hk.2]
  exact k12_rounds X p hp

end H2K.Made

#print axioms H2K.Made.k12_before
#print axioms H2K.Made.seat_pays
#print axioms H2K.Made.keeps_atFinish
