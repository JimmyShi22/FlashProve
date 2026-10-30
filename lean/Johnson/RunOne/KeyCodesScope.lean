-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyCodesScope.lean: THEOREMS. **IN SCOPE THE CARRIED CODES ARE THE WRITTEN VALUE's, keyFull.codes, AT EVERY RECORD THAT ANY OF Key.descriptionFromSource's THREE CHAINS REACHES; ON CHAINS 2 | 3 WITHOUT planOk AND WITHOUT A STEP OF CHAIN 3**

OBJECT. X.chains.made.sized.key.codes · X.Y.k.oneTime.codes at X := what sourceOf gives of the maker's record in scope. USER. The rows of chain 2 at F_K's letters. LETTERS. Zp · Z · cfg · m · X · N · P · D · k · a.
  chains_codes_in_scope    InScope Zp → ReadOf Zp.pol Z → madeAt Z Zp.lay cfg = .ok m → sourceOf m = .ok X → X.chains.made.sized.key.codes = keyFull.codes: key_in_scope (Johnson/RunOne/Law/KeyInScope.lean) and KeyPayD's pubsOf_ok: two rewrites; NO planOk
  codes_in_scope₂ | ₃      so Hist₂ | Hist₃ … k a → a.2.st.codes = keyFull.codes
  codes_in_scope₁          with planOk (five_in_scope, its fifth equation): Hist₁ … k a → (stAt a).codes = keyFull.codes
What is not claimed. Anything at a free X. Nothing on soundness.

-/
import Johnson.RunOne.KeyCodesLater
import Johnson.RunOne.KeyPayD
import Johnson.RunOne.Law.KeyInScope

set_option autoImplicit false

namespace Johnson.RunOne.KeyCodes

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open VerifiableInference.Desc.Third (S₃)
open LPFD (Hist₁ Hist₂ Hist₃)
open Lk6.AtPlan (keyFull)

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **In scope the sized key's codes, as the source holds them, are the written value's.** -/
theorem chains_codes_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) : X.chains.made.sized.key.codes = keyFull.codes := by
  rw [(Johnson.RunOne.KeyPay.pubsOf_ok hX).1, Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm]

theorem codes_in_scope₂ {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (D : OnBytes.Maker.WholeD) (k : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D k a) : (st₂ (show _root_.Desc.K14.St from a.2)).codes = keyFull.codes :=
  (codes_at_reached₂ D k a h).trans (chains_codes_in_scope hZ hP hm hX)

theorem codes_in_scope₃ {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (D : OnBytes.Maker.WholeD) (k : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) : (st₃ (show S₃ from a.2)).codes = keyFull.codes :=
  (codes_at_reached₃ D k a h).trans (chains_codes_in_scope hZ hP hm hX)

theorem codes_in_scope₁ {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (descriptionFromSource X N P).planOk = true) (D : OnBytes.Maker.WholeD) (k : ℕ)
    (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D k a) : (stAt a).codes = keyFull.codes :=
  (codes_at_reached₁ D k a h).trans (Johnson.RunOne.Law.KeyInScope.five_in_scope hZ hP hm hX hp).2.2.2.2

end Johnson.RunOne.KeyCodes
