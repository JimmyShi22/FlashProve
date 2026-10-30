-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyPinwInScope.lean: THEOREMS; CALLS ALONE. **IN THE GOALS' SCOPE: a member of PINW beside PIN · hasSmp · NoColl at the woven tables' one reading at its canonical filling, WITH NO PUBLIC PREMISE LEFT BUT SCOPE's**: Johnson/RunOne/KeyPinwAtName.lean's four public premises (three tests on the seats, a stage) are paid by Johnson/RunOne/KeySevenInScope.lean's seven_at.
WORDS. The out-of-domain (OOD) sample on the committed table, its seed and its answers (these files call it the record: recOf · recBack · recOfM · RecFull). What the verifier carries between two blocks: the verifier's state.
OBJECT: (baseAt X decN recBack).h₁. USER: Johnson/RunOne/KeyPinwReached.lean calls member_pinw_scope_rec. WHAT IT SHOWS PAYABLE: the items pinT (PINW) and pin 0 | 1 | 2 among the promises at the first chain's borders can hold together in scope: a law of the first chain's rows that has them among its premises is not true of nothing for their sake. LETTERS: the public files Zp · Z · cfg · m · X N P (as in seven_at) · M · ρT · the three sendings' messages, randomness and seeds · y₀.
  member_pinw_scope       seven_at's seven premises · sendable messages · «y₀'s stored side is M's stored table» ⊢ member_pinw_name's conclusion
  member_pinw_scope_rec   the same, the verifier's state a letter: another file's premise that the state holds the sending kind's rows stays
What is not claimed. member_pinw_scope's state is laid by hand: no state that the blocks reach. That scope's seven hold at any files ([RAN] at the stored full-size public files). «In range». It names no o. A MEMBER, no law. Nothing on soundness.

-/
import Johnson.RunOne.KeyPinwAtName
import Johnson.RunOne.KeySevenInScope

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

/-- **In scope: a member of PINW beside the three, at the canonical filling.** -/
theorem member_pinw_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (hm : Key.madeAt Z Zp.lay cfg = .ok m) (hX : Key.sourceOf m = .ok X) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hw : (Key.descriptionFromSource X N P).wantedOk = true) (hD : (Key.descriptionFromSource X N P).data "key file" = .ok writtenKFull)
    (b : LookupRecord) (y₀ : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str) (m₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Msg)
    (r₀ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Rnd) (ρ : ∀ i : Fin six.length, (OmAt Johnson.Top.H.csKey six i).Z.D)
    (hsend : ∀ i, Johnson.Pack.Sendable Johnson.Top.H.csKey (six.get i).1 (six.get i).2 (m₀ i, r₀ i))
    (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρT : DF.Z.D) (h0 : y₀.1 = stored DF M) :
    ∃ (s : FirstState) (W : Wit MsgN Unit Fill.Tab) (y' : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str),
      W.cells = DF.ix.view (upM DF M) ∧ y'.1 = stored DF M ∧
      PINW (baseAt X decN recBack).h₁ (keyInstanceOfOutOfDomainSample (recOfM DF M ρT), s) (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧ ∀ i : Fin six.length, numSix i < 3 →
      PIN (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (keyInstanceOfOutOfDomainSample (recOfM DF M ρT), s) (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧
      hasSmp (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (keyInstanceOfOutOfDomainSample (recOfM DF M ρT), s) = true ∧
      NoColl (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 (keyInstanceOfOutOfDomainSample (recOfM DF M ρT), s) (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') := by
  obtain ⟨hn, -, -, -, hst, -⟩ := seven_at hZ hP hm hX hp hw hD
  exact member_pinw_name X N P "" "" "" (hn "" "" "").1 (hn "" "" "").2.1 (hn "" "" "").2.2 hst b y₀ m₀ r₀ ρ hsend M ρT h0

/-- **The same, the verifier's state a letter.** -/
theorem member_pinw_scope_rec {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (hm : Key.madeAt Z Zp.lay cfg = .ok m) (hX : Key.sourceOf m = .ok X) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hw : (Key.descriptionFromSource X N P).wantedOk = true) (hD : (Key.descriptionFromSource X N P).data "key file" = .ok writtenKFull)
    (I : Fin six.length → Prop) (hI : ∀ i, I i → numSix i < 3)
    (y₀ : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str) (a : Xi × FirstState)
    (hrec : ∀ i, I i → ∃ o ρ y, (KeyRows1.plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 a.2.d.st o ρ y)
    (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρT : DF.Z.D) (ha : a.1 = keyInstanceOfOutOfDomainSample (recOfM DF M ρT)) (h0 : y₀.1 = stored DF M) :
    ∃ (W : Wit MsgN Unit Fill.Tab) (y' : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str),
      W.cells = DF.ix.view (upM DF M) ∧ y'.1 = stored DF M ∧
      PINW (baseAt X decN recBack).h₁ a (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧ ∀ i : Fin six.length, I i →
      PIN (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧
      hasSmp (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a = true ∧
      NoColl (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') := by
  obtain ⟨hn, -⟩ := seven_at hZ hP hm hX hp hw hD
  exact member_pinw_name_rec X N P I hI "" "" "" (hn "" "" "").1 (hn "" "" "").2.1 (hn "" "" "").2.2 y₀ a hrec M ρT ha h0

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.member_pinw_scope
#print axioms Johnson.RunOne.KeyLetters.member_pinw_scope_rec
