-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyPinwStored.lean: THEOREMS; CALLS ALONE. **A member of PINW beside PIN · hasSmp · NoColl at the woven tables' one reading, AT THE LIBRARY's DECODER OF THE STORED TABLE**: Johnson/RunOne/KeyPinwAtLetters.lean's premise on the decoder is paid by Johnson/RunOne/KeyStoredDecodes.lean: the two meet at one string.
OBJECT: PINW (Johnson/Desc/Msg.lean) at baseK … .h₁ (Johnson/RunOne/KeyFillSeed.lean), its letter decT filled with decU: the library's DF.dcd at the stored table read off the cells. USER: none yet (meant: the last call, at the written reading of the record off an instance, recBack, Johnson/Top/Fire/Code/KeyAtName.lean). LETTERS: X N P · DK · recOf (the record's reading: STILL A LETTER) · x | a · M · ρT.
  decU                  fun c r => DF.dcd (fun p => (c p.val).getD (0, [])) r: THE BODY OF THE WRITTEN DECODER of the stored table off its cells (decN ∘ yOf, Johnson/Top/Fire/Code/KeyAtName.lean), under a name of this file's own because it stands six times in a statement. TIED: «decU = decN» is decU_eq (Johnson/RunOne/KeyPinwAtName.lean), by rfl
  «Sendable» HERE IS Johnson.Pack.Sendable (Johnson/Pack/TwoPads.lean), by its full name: this namespace holds an elder notion of the same short name (Johnson/RunOne/KeyMember.lean)
  holdsB_at             the frame's list does not read the stored table's depth
  f0_written | f1_written | f2_written   the frame at the WRITTEN data, at the decoder's depth, holds the trees 0 · 1 · 5 at the three codes' depths (from holds0 | holds1 | holds5, Johnson/RunOne/KeyScopeNums.lean)
  member_pinw_stored    at any data DK: every table M of full messages over the base field, every seed: under member_fk₁_cells's premises, «the instance's record is M's true record at the seed» and «y₀'s stored side is M's stored table»
  member_pinw_rec       the same, the state a letter (member_fk_rec₁_cells's premise)
  member_pinw_written   member_pinw_stored at the written data: its three premises on the frame are paid: left: the three tests on the seats · a stage · the record's reading
What is not claimed. That any reading recOf of an instance answers M's true record (at a letter it is a premise; recBack ∘ keyInstanceOfOutOfDomainSample is meant). That an honest run lays this state, table or record: member_fk₁'s state is laid by hand. «In range». It is a MEMBER (the items can hold together), no law. Nothing on soundness.

-/
import Johnson.RunOne.KeyPinwAtLetters
import Johnson.RunOne.KeyStoredDecodes
import Johnson.RunOne.KeyScopeNums

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
open Johnson.G (writtenKFull)

/-- The library's decoder at the stored table read off the cells. -/
def decU (c : ℕ → Option (ℕ × List UInt64)) (r : DF.Rec) : Option (DF.ix.Row × DF.toDec.En → GE) :=
  DF.dcd (fun p => (c p.val).getD (0, [])) r

/-- The frame's list does not read the stored table's depth. -/
theorem holdsB_at (D : WholeD) (a j k : ℕ) : holdsB (fr₁ (D.at a)) j k = holdsB (fr₁ D) j k := rfl

theorem f0_written : holdsB (fr₁ (writtenKFull.at frS.P.T.a)) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true :=
  (holdsB_at writtenKFull _ _ _).trans holds0
theorem f1_written : holdsB (fr₁ (writtenKFull.at frS.P.T.a)) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true :=
  (holdsB_at writtenKFull _ _ _).trans holds1
theorem f2_written : holdsB (fr₁ (writtenKFull.at frS.P.T.a)) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true :=
  (holdsB_at writtenKFull _ _ _).trans holds5

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) (recOf : Xi → Option DF.Rec)

/-- **A member of PINW beside the three, at the library's decoder.** -/
theorem member_pinw_stored (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ (DK.at frS.P.T.a)) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ (DK.at frS.P.T.a)) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ (DK.at frS.P.T.a)) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (hst : 0 < (oneAt X).ranges.stages.length)
    (x : Xi) (b : LookupRecord) (y₀ : (fr₁ (DK.at frS.P.T.a)).E.Str) (m₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Msg)
    (r₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Rnd) (ρ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Z.D)
    (hsend : ∀ i, Johnson.Pack.Sendable Johnson.Top.H.csKey (six.get i).1 (six.get i).2 (m₀ i, r₀ i))
    (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρT : DF.Z.D)
    (hr : recOf x = some (recOfM DF M ρT)) (h0 : y₀.1 = stored DF M) :
    ∃ (s : FirstState) (W : Wit (DF.ix.Row × DF.toDec.En → GE) Unit Fill.Tab) (y' : (fr₁ (DK.at frS.P.T.a)).E.Str),
      W.cells = DF.ix.view (upM DF M) ∧ y'.1 = stored DF M ∧
      PINW (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (x, s) (strsOf (fr₁ (DK.at frS.P.T.a)) y') W ∧ ∀ i : Fin six.length, numSix i < 3 →
      PIN (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ (DK.at frS.P.T.a)) y') W ∧
      hasSmp (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) = true ∧
      NoColl (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ (DK.at frS.P.T.a)) y') := by
  obtain ⟨s, W, y', hc, hy, h⟩ := member_fk₁_pinw X N P (DK.at frS.P.T.a) decU recOf t0 t1 t2 n0 n1 n2 f0 f1 f2 hst x b y₀ m₀ r₀ ρ hsend
    (DF.ix.view (upM DF M)) (recOfM DF M ρT) hr (fun y' e => stored_decodes DK M ρT y' (e.trans h0))
  exact ⟨s, W, y', hc, hy.trans h0, h⟩

/-- **The same, the state a letter.** -/
theorem member_pinw_rec (I : Fin six.length → Prop) (hI : ∀ i, I i → numSix i < 3) (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ (DK.at frS.P.T.a)) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ (DK.at frS.P.T.a)) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ (DK.at frS.P.T.a)) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (y₀ : (fr₁ (DK.at frS.P.T.a)).E.Str) (a : Xi × FirstState)
    (hrec : ∀ i, I i → ∃ o ρ y, (KeyRows1.plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 a.2.d.st o ρ y)
    (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρT : DF.Z.D)
    (hr : recOf a.1 = some (recOfM DF M ρT)) (h0 : y₀.1 = stored DF M) :
    ∃ (W : Wit (DF.ix.Row × DF.toDec.En → GE) Unit Fill.Tab) (y' : (fr₁ (DK.at frS.P.T.a)).E.Str),
      W.cells = DF.ix.view (upM DF M) ∧ y'.1 = stored DF M ∧
      PINW (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ a (strsOf (fr₁ (DK.at frS.P.T.a)) y') W ∧ ∀ i : Fin six.length, I i →
      PIN (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ (DK.at frS.P.T.a)) y') W ∧
      hasSmp (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a = true ∧
      NoColl (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ (DK.at frS.P.T.a)) y') := by
  obtain ⟨W, y', hc, hy, h⟩ := member_fk_rec₁_pinw X N P (DK.at frS.P.T.a) decU recOf I hI t0 t1 t2 n0 n1 n2 f0 f1 f2 y₀ a hrec
    (DF.ix.view (upM DF M)) (recOfM DF M ρT) hr (fun y' e => stored_decodes DK M ρT y' (e.trans h0))
  exact ⟨W, y', hc, hy.trans h0, h⟩

/-- **At the written data the three premises on the frame are paid.** -/
theorem member_pinw_written (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (hst : 0 < (oneAt X).ranges.stages.length)
    (x : Xi) (b : LookupRecord) (y₀ : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str) (m₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Msg)
    (r₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Rnd) (ρ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Z.D)
    (hsend : ∀ i, Johnson.Pack.Sendable Johnson.Top.H.csKey (six.get i).1 (six.get i).2 (m₀ i, r₀ i))
    (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρT : DF.Z.D)
    (hr : recOf x = some (recOfM DF M ρT)) (h0 : y₀.1 = stored DF M) :
    ∃ (s : FirstState) (W : Wit (DF.ix.Row × DF.toDec.En → GE) Unit Fill.Tab) (y' : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str),
      W.cells = DF.ix.view (upM DF M) ∧ y'.1 = stored DF M ∧
      PINW (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (x, s) (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧ ∀ i : Fin six.length, numSix i < 3 →
      PIN (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧
      hasSmp (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) = true ∧
      NoColl (Fk X N P) (baseK Johnson.Top.H.csKey six numSix atSix decU recOf (KeyRows1.plan₁ (oneAt X)).orc).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (x, s) (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') :=
  member_pinw_stored X N P writtenKFull recOf t0 t1 t2 n0 n1 n2 f0_written f1_written f2_written hst x b y₀ m₀ r₀ ρ hsend M ρT hr h0

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.holdsB_at
#print axioms Johnson.RunOne.KeyLetters.f0_written
#print axioms Johnson.RunOne.KeyLetters.f1_written
#print axioms Johnson.RunOne.KeyLetters.f2_written
#print axioms Johnson.RunOne.KeyLetters.member_pinw_stored
#print axioms Johnson.RunOne.KeyLetters.member_pinw_rec
#print axioms Johnson.RunOne.KeyLetters.member_pinw_written
