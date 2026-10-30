-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillCells.lean: «W.cells = c₀» BESIDE THE THREE. Johnson/RunOne/KeyFillMeet.lean's member_fk₁ and KeyFillRecord.lean's member_fk_rec₁ take the witness's cells c₀ as a letter and hide them behind ∃ W.
  pin_cells               PIN reads of the witness msgOf alone (its msg and pad): the cells may be laid anew
  member_fk₁_cells        member_fk₁ with «W.cells = c₀» in front
  member_fk_rec₁_cells    member_fk_rec₁ with the same
The older theorems are called; no proof is copied.
BY ITSELF THE CONJUNCT IS WORTH NOTHING: none of PIN | hasSmp | NoColl reads W.cells. ITS USE: PINW (Johnson/Desc/Msg.lean: ∃ r, recOf a = some r ∧ decT y.cell r = some w.cells) reads just what these three do not: so it can be laid beside them AT ONE W AND ONE y' (whose stored side is y₀'s). That PINW holds is shown by nothing here.
OBJECT: Wit | msgOf | PIN (Johnson/Desc/Msg.lean) · USER: a member of PINW · LETTERS: as in the two older theorems. Nothing on soundness.
-/
import Johnson.RunOne.KeyFillRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SeedIs)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

/-- **PIN reads of the witness its msg and pad alone.** -/
theorem pin_cells {XI A Cells Tok M Smp Rec : Type} (F : FileDescription XI) (G : Reading A Cells M Smp Rec) (j t : ℕ) (a : A) (y : Strs) (W : Wit Cells Tok M) (c : Cells)
    (h : PIN F G j t a y W) : PIN F G j t a y { W with cells := c } := h

section
open OnBytes.Params VerifiableInference.Desc.Sound
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)

/-- **member_fk₁ with the witness's cells said.** -/
theorem member_fk₁_cells (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ D) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (hst : 0 < (oneAt X).ranges.stages.length)
    (x : Xi) (b : LookupRecord) (y₀ : (fr₁ D).E.Str) (m₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Msg)
    (r₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Rnd) (ρ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Z.D)
    (hsend : ∀ i, Sendable Johnson.Top.H.csKey (six.get i).1 (six.get i).2 (m₀ i, r₀ i)) (c₀ : Cells) :
    ∃ (s : FirstState) (W : Wit Cells Unit Fill.Tab) (y' : (fr₁ D).E.Str), W.cells = c₀ ∧ y'.1 = y₀.1 ∧ ∀ i : Fin six.length, numSix i < 3 →
      PIN (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ D) y') W ∧
      hasSmp (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) = true ∧
      NoColl (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ D) y') := by
  obtain ⟨s, W, y', hy, h⟩ := member_fk₁ X N P D decT recOf t0 t1 t2 n0 n1 n2 f0 f1 f2 hst x b y₀ m₀ r₀ ρ hsend c₀
  exact ⟨s, { W with cells := c₀ }, y', rfl, hy, fun i hi => ⟨pin_cells _ _ _ _ _ _ W c₀ (h i hi).1, (h i hi).2⟩⟩

/-- **member_fk_rec₁ with the witness's cells said.** -/
theorem member_fk_rec₁_cells (I : Fin six.length → Prop) (hI : ∀ i, I i → numSix i < 3) (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ D) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (y₀ : (fr₁ D).E.Str) (a : Xi × FirstState)
    (hrec : ∀ i, I i → ∃ o ρ y, (KeyRows1.plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 a.2.d.st o ρ y) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : (fr₁ D).E.Str), W.cells = c₀ ∧ y'.1 = y₀.1 ∧ ∀ i : Fin six.length, I i →
      PIN (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ D) y') W ∧
      hasSmp (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a = true ∧
      NoColl (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ D) y') := by
  obtain ⟨W, y', hy, h⟩ := member_fk_rec₁ X N P D decT recOf I hI t0 t1 t2 n0 n1 n2 f0 f1 f2 y₀ a hrec c₀
  exact ⟨{ W with cells := c₀ }, y', rfl, hy, fun i hi => ⟨pin_cells _ _ _ _ _ _ W c₀ (h i hi).1, (h i hi).2⟩⟩

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.pin_cells
#print axioms Johnson.RunOne.KeyRows23.member_fk₁_cells
#print axioms Johnson.RunOne.KeyRows23.member_fk_rec₁_cells
