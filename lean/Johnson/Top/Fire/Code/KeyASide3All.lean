-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASide3All.lean: THE KEY FILE's LAST CHAIN: THE VERIFIER's STATE's SIDE OF
THE INVARIANT FROM THE HISTORY, IN SCOPE, AT EVERY BORDER: NO PREMISE ON A STEP OR ON A START IS
LEFT. KeyASide3AtFk.lean's aSide₃_of_hist with its five premises paid by calls:
  hf    the test on the plan that ties the chains: a part of planOk
  ha1   one answer to a sample: samples_in_scope
  hA    AtOk at atSix · off₂N · off₃N: atOk_six, the ranges' test having four stages in scope
  hoff  off_six
  h12   the shared chain's state's side at its last border: aSide₂_at_all (KeyASide2All.lean)
  ★★ aSide₃_at_all   PROVED: k ≤ 4 · Hist₃ (Fk X N P) D k a · fits ⊢ Tests₃ at the tables' letters
                     (atSix · off₂N · off₃N) at border k, and the codes' lengths in order there:
                     FROM THE SEAT's FACTS ALONE. The sibling of aSide_at_all | aSide₂_at_all.
OBJECT: Tests₃ at Hist₃ (Fk X N P) D k a · USER: none yet; meant: on₃_of_parts (chain 3's members);
row 3.2's caller · LETTERS: none in front but the seat's.
THE STATE's SIDE ALONE: THE ORACLE STRINGS' SIDE (Strings₃) IS NOT HERE. NO MEMBER IS SHOWN: EMPTY
WHERE NOTHING IS REACHED. fits IS A TEST ON THE INSTANCE. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyASide3AtFk
import Johnson.Top.Fire.Code.KeyASide2All
import Johnson.Top.Fire.Code.KeyAtOff
import Johnson.Top.Fire.Code.KeyRoundsAtSeat
import Johnson.RunOne.KeyScopeNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Xi)
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
variable (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}
variable (D : WholeD)

/-- ★★ **The last chain's state's side at every border, from the history and the seat's facts
alone.** -/
theorem aSide₃_at_all (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true)
    (hN : rangesNumbers m = .ok N)
    (k : ℕ) (a : P₃ × St₃) (hk : k ≤ 4) (hist : Hist₃ (Fk X N P) D k a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) :
    T₃ X P atSix off₂N off₃N k a ∧ a.2.st.codes.lengthsOk = true := by
  have hst : (oneAt X).ranges.stages.length = 4 := by
    rw [(one_full hZ hP hm hX hp).1]
    exact Johnson.RunOne.KeyLetters.stages_full
  have hat : AtOk atSix off₂N off₃N ((oneAt X).ranges.stages.length + 2) := by
    rw [hst]
    exact atOk_six
  have h12len : (Fk X N P).shared.blocksInOrder.length = 12 := (lengths_in_scope hZ hP hm hX hp hw).2.1
  exact aSide₃_of_hist X N P D atSix off₂N off₃N (fileOk_of_planOk' _ hp)
    (Johnson.RunOne.KeySendGood.samples_in_scope hZ hP hm hX hp) hat off_six
    (fun a₂ h hf => aSide₂_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN 12 a₂ (Nat.le_refl _)
      (h12len ▸ h) hf) k a hk hist hfit

end

end LPFD

#print axioms LPFD.aSide₃_at_all
