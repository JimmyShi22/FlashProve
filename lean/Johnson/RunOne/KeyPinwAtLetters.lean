-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyPinwAtLetters.lean: THEOREMS; CALLS ALONE. **PINW beside PIN · hasSmp · NoColl, at one witness and one string, at the woven tables' one reading**, AT LETTERS for the stored table's decoder and the record's reading.
OBJECT: PINW (Johnson/Desc/Msg.lean: ∃ r, G.recOf a = some r ∧ G.decT y.cell r = some w.cells) at the tables' files' reading baseK … .h₁ (Johnson/RunOne/KeyFillSeed.lean). USER: none yet (meant: the last call, at the tables' files' written decoder and reading of the record). LETTERS: X N P D · Cells Rec decT recOf · x | a · r · c₀ · y₀.
  member_fk₁_pinw       member_fk₁_cells (Johnson/RunOne/KeyFillCells.lean), and beside its three: PINW: under two premises: the record is read off the instance (hr) · the decoder answers c₀ at EVERY string with y₀'s stored side (hd)
  member_fk_rec₁_pinw   the same at member_fk_rec₁_cells: THE STATE A LETTER, under that theorem's premise that the state holds the sending kind's rows
What is not claimed. That hd holds at any decoder: at letters it can be false: Johnson/RunOne/KeyStoredDecodes.lean pays it at the library's. The called theorems' limits travel: member_fk₁'s state is laid by hand: no state that the blocks reach. «In range». Nothing on soundness.

-/
import Johnson.RunOne.KeyFillCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters
open Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SeedIs)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice
open OnBytes.Params VerifiableInference.Desc.Sound

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)

/-- **PINW beside the three, at one witness and one string.** -/
theorem member_fk₁_pinw (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ D) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (hst : 0 < (oneAt X).ranges.stages.length)
    (x : Xi) (b : LookupRecord) (y₀ : (fr₁ D).E.Str) (m₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Msg)
    (r₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Rnd) (ρ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Z.D)
    (hsend : ∀ i, Sendable Johnson.Top.H.csKey (six.get i).1 (six.get i).2 (m₀ i, r₀ i)) (c₀ : Cells)
    (r : Rec) (hr : recOf x = some r)
    (hd : ∀ y' : (fr₁ D).E.Str, y'.1 = y₀.1 → decT (strsOf (fr₁ D) y').cell r = some c₀) :
    ∃ (s : FirstState) (W : Wit Cells Unit Fill.Tab) (y' : (fr₁ D).E.Str), W.cells = c₀ ∧ y'.1 = y₀.1 ∧
      PINW (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (x, s) (strsOf (fr₁ D) y') W ∧ ∀ i : Fin six.length, numSix i < 3 →
      PIN (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ D) y') W ∧
      hasSmp (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) = true ∧
      NoColl (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ D) y') := by
  obtain ⟨s, W, y', hc, hy, h⟩ := member_fk₁_cells X N P D decT recOf t0 t1 t2 n0 n1 n2 f0 f1 f2 hst x b y₀ m₀ r₀ ρ hsend c₀
  exact ⟨s, W, y', hc, hy, ⟨r, hr, (hd y' hy).trans (congrArg some hc.symm)⟩, h⟩

/-- **The same, the state a letter.** -/
theorem member_fk_rec₁_pinw (I : Fin six.length → Prop) (hI : ∀ i, I i → numSix i < 3) (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ D) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (y₀ : (fr₁ D).E.Str) (a : Xi × FirstState)
    (hrec : ∀ i, I i → ∃ o ρ y, (KeyRows1.plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 a.2.d.st o ρ y) (c₀ : Cells)
    (r : Rec) (hr : recOf a.1 = some r)
    (hd : ∀ y' : (fr₁ D).E.Str, y'.1 = y₀.1 → decT (strsOf (fr₁ D) y').cell r = some c₀) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : (fr₁ D).E.Str), W.cells = c₀ ∧ y'.1 = y₀.1 ∧
      PINW (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ a (strsOf (fr₁ D) y') W ∧ ∀ i : Fin six.length, I i →
      PIN (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ D) y') W ∧
      hasSmp (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a = true ∧
      NoColl (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ D) y') := by
  obtain ⟨W, y', hc, hy, h⟩ := member_fk_rec₁_cells X N P D decT recOf I hI t0 t1 t2 n0 n1 n2 f0 f1 f2 y₀ a hrec c₀
  exact ⟨W, y', hc, hy, ⟨r, hr, (hd y' hy).trans (congrArg some hc.symm)⟩, h⟩

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.member_fk₁_pinw
#print axioms Johnson.RunOne.KeyLetters.member_fk_rec₁_pinw
