-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyPinwAtName.lean: THEOREMS; CALLS ALONE. **THE LAST CALL: a member of PINW beside PIN · hasSmp · NoColl at the woven tables' one reading AT ITS CANONICAL FILLING**: the written decoder decN and the written reading of the record recBack (Johnson/Top/Fire/Code/KeyAtName.lean), at the instance keyInstanceOfOutOfDomainSample r of the stored table's true record r.
OBJECT: (baseAt X decN recBack).h₁ (Johnson/Top/Fire/Code/KeyAtBase.lean). USER: Johnson/RunOne/KeyPinwInScope.lean, which calls both members. LETTERS: X N P · M · ρT · the three sendings' messages, randomness and seeds · y₀.
  DN_eq              LPFD.DN is KeyMemberTableFull.lean's DF (one library decoder, two names)
  decU_eq            **THE TIE THAT WAS OWED**: decU (Johnson/RunOne/KeyPinwStored.lean) IS KeyAtName.lean's decN; the ascription also says that RecFull is DF.Rec and MsgN is DF's type of decoded tables, up to unfolding
  member_pinw_name   at the written data: under the three tests on the seats, a stage, sendable messages, and «y₀'s stored side is M's stored table»: NO PREMISE ON THE RECORD's READING IS LEFT
  member_pinw_name_rec   the same, the state a letter, at a record whose instance is keyInstanceOfOutOfDomainSample r
What is not claimed. The called theorems' limit stays: member_fk₁'s state is laid by hand: no state that the blocks reach. The four public premises are paid in scope in Johnson/RunOne/KeyPinwInScope.lean. «In range»; HeldAtName (Johnson/Top/Fire/Code/KeyAtName.lean). It is a MEMBER, no law. Nothing on soundness.

-/
import Johnson.RunOne.KeyPinwStored
import Johnson.Top.Fire.Code.KeyAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters
open Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState keyInstanceOfOutOfDomainSample)
open VerifiableInference.Desc.K1 (SeedIs)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice OnBytes.Flat
open OnBytes.Params VerifiableInference.Desc.Sound
open Johnson.G (writtenKFull)
open LPFD (DN MsgN decN recBack recBack_instK baseAt)

theorem DN_eq : DN = DF := DF_eq

/-- **The tie that was owed.** -/
theorem decU_eq : (decU : (ℕ → Option (ℕ × List UInt64)) → RecFull → Option MsgN) = decN := rfl

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- **A member of PINW beside the three, at the canonical filling.** -/
theorem member_pinw_name (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (hst : 0 < (oneAt X).ranges.stages.length)
    (b : LookupRecord) (y₀ : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str) (m₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Msg)
    (r₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Rnd) (ρ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Z.D)
    (hsend : ∀ i, Johnson.Pack.Sendable Johnson.Top.H.csKey (six.get i).1 (six.get i).2 (m₀ i, r₀ i))
    (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρT : DF.Z.D) (h0 : y₀.1 = stored DF M) :
    ∃ (s : FirstState) (W : Wit MsgN Unit Fill.Tab) (y' : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str),
      W.cells = DF.ix.view (upM DF M) ∧ y'.1 = stored DF M ∧
      PINW (baseAt X decN recBack).h₁ (keyInstanceOfOutOfDomainSample (recOfM DF M ρT), s) (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧ ∀ i : Fin six.length, numSix i < 3 →
      PIN (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (keyInstanceOfOutOfDomainSample (recOfM DF M ρT), s) (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧
      hasSmp (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (keyInstanceOfOutOfDomainSample (recOfM DF M ρT), s) = true ∧
      NoColl (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (keyInstanceOfOutOfDomainSample (recOfM DF M ρT), s) (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') :=
  member_pinw_written X N P recBack t0 t1 t2 n0 n1 n2 hst (keyInstanceOfOutOfDomainSample (recOfM DF M ρT)) b y₀ m₀ r₀ ρ hsend M ρT (recBack_instK (recOfM DF M ρT)) h0

/-- **The same, the state a letter.** -/
theorem member_pinw_name_rec (I : Fin six.length → Prop) (hI : ∀ i, I i → numSix i < 3) (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (y₀ : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str) (a : Xi × FirstState)
    (hrec : ∀ i, I i → ∃ o ρ y, (KeyRows1.plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 a.2.d.st o ρ y)
    (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρT : DF.Z.D) (ha : a.1 = keyInstanceOfOutOfDomainSample (recOfM DF M ρT)) (h0 : y₀.1 = stored DF M) :
    ∃ (W : Wit MsgN Unit Fill.Tab) (y' : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str),
      W.cells = DF.ix.view (upM DF M) ∧ y'.1 = stored DF M ∧
      PINW (baseAt X decN recBack).h₁ a (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧ ∀ i : Fin six.length, I i →
      PIN (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧
      hasSmp (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a = true ∧
      NoColl (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') :=
  member_pinw_rec X N P writtenKFull recBack I hI t0 t1 t2 n0 n1 n2 f0_written f1_written f2_written y₀ a hrec M ρT
    (ha ▸ recBack_instK (recOfM DF M ρT)) h0

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.DN_eq
#print axioms Johnson.RunOne.KeyLetters.decU_eq
#print axioms Johnson.RunOne.KeyLetters.member_pinw_name
#print axioms Johnson.RunOne.KeyLetters.member_pinw_name_rec
