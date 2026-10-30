-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GoodCollidesB.lean: where the verifier program has said yes to a key file, if
three tests on the plain data pass: either the six parts of the typing return at the fixed reading
of that file, or the file shows a collision of the format's hash: two entries out of its own lists
as read give two different strings of bytes with one answer, at one number, label, index and start.

Statements and proofs. OnBytes/Maker/Page/RecordBytes.lean has the law at the record of a reading,
and the way from the record to `KeyCollidesB` (OnBytes/Maker/Page/CollidesBytes.lean), whose reading
is fixed by the equation of the program's reader. Here the record is that of the program's check
(OnBytes/TieK/), the reader's equation comes from the check's yes, and the three chains' one setting
from the way in which the program reads their parameter bytes.

Main names:
  `chains_returns_or_collidesInB`: at the flat record of the check of a key's three chains:
    `typeReturns .. = true ∨ CollidesInB Fmt.formatHash ..`.
  `good_returns_or_collidesInB`: the same at a good reading of a key file (`KeyGood`).
  `port_returns_or_collidesB`: at the files F to which the program has said yes (`K.PortYesAt`):
    `typeReturns .. = true ∨ KeyCollidesB Fmt.formatHash p.chains.key table F.key j`.
The three tests: `okAt`, `oneShapeB`, `saltsFit`, all on the plain data of the rounds.
Under "there is" in the last law: j, fixed by the equation of `Key.readTable` at F's key file; then
the letters of `KeyCollidesB`.
Limits: the tests are not shown here. The number of bytes of a salt is the one-time chain's; the
start of the stored tables' leaves in the second arm is the shared chain's digest of the
configuration, which `SameSetting` makes equal to the one-time chain's. No file beside this one
calls `good_returns_or_collidesInB`. cfg, the typing's letter, is free. Nothing on how hard such a
file is to make. Nothing on opening-form binding, no two openings of a commitment, correctness of
extraction, what a root fixes or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.Page.RecordBytes
import OnBytes.Maker.Page.GoodCollides
import OnBytes.Maker.Page.GoodFields
import OnBytes.TieK.PortChains

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- **At the flat record of the check of a key's three chains.** -/
theorem chains_returns_or_collidesInB (C : CK) (a : ℕ) (cfg : ByteArray) (k : Params.KeyChains)
    (table : Params.TableName) {file : ByteArray} {j : ℕ} {R₁ : Rounds} {dry : FirstEnd}
    {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd}
    {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS : k.oneTime.describe table R₁ = some S₁)
    (s₂ : SameSetting k.oneTime.given k.shared.given)
    (s₃ : SameSetting k.oneTime.given k.second.given) (R : Rounds × Rounds × Rounds)
    (hR : dryKey k r.key = some R) (hok : okAt a (some R) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit k.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) = true) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) k.oneTime.given.plan.salt cfg r = true ∨
      CollidesInB Fmt.formatHash (Three.Whole.of R.1 R.2.1 R.2.2) r k.shared.given.cfg := by
  have hS' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS
  unfold dryKey at hR
  rw [T.first_dry] at hR
  have hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := key_own k.oneTime T.first_dry
  exact returns_or_collidesInB Fmt.formatHash C a k.oneTime.given.plan.salt cfg k.shared.given.cfg T
    (readAt_H T) hS' (fun e => by cases e) o₁ b₁ R₃ hd hok (okAt_parts hok).fits
    (okAt_parts hok).stored rfl s₂.salt.symm s₃.salt.symm s₂.cfg rfl (s₃.cfg.symm.trans s₂.cfg) hB
    (oneSaltB_of_saltsFit hsalts)

/-- **At a good reading of a key file.** key₀: a fixed key at which the three lists R were made. -/
theorem good_returns_or_collidesInB (u : KeyPub) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R)
    (d : Params.TableName × ChainsData) (hg : KeyGood u d) (C : CK) (a : ℕ) (cfg : ByteArray)
    (hok : okAt a (some R) = true) (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit p.chains.key.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true) :
    typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.key.oneTime.given.plan.salt cfg
        d.2.r = true ∨
      CollidesInB Fmt.formatHash (Three.Whole.of R.1 R.2.1 R.2.2) d.2.r p.chains.key.shared.given.cfg := by
  obtain ⟨file, j, real, real2, -, -, hS, T⟩ := good_chains u p hp d hg
  obtain ⟨-, s₂, s₃⟩ := setting_keyGood hg hp
  exact chains_returns_or_collidesInB C a cfg p.chains.key d.1 T.toRead hS s₂ s₃ R
    (good_dry3 u p hp key₀ h0 hf R hR d hg) hok hB hsalts

/-- **At the files to which the program has said yes.** d: the fixed reading of F's key file. -/
theorem port_returns_or_collidesB (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (d : ChainsData)
    (hd : readKeyChains F.pol F.lay F.KL F.key = some (table, d)) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (C : CK) (a : ℕ)
    (cfg : ByteArray) (hok : okAt a (some R) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hsalts : saltsFit p.chains.key.oneTime.given.plan.salt (Three.Whole.of R.1 R.2.1 R.2.2) =
      true) :
    ∃ j, Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg F.key =
        .ok (table, j) ∧
      (typeReturns C a (Three.Whole.of R.1 R.2.1 R.2.2) p.chains.key.oneTime.given.plan.salt cfg
          d.r = true ∨
        KeyCollidesB Fmt.formatHash p.chains.key table F.key j) := by
  have ho := port_key_chains F id table further h
  have hg : KeyGood ⟨F.pol, F.lay, F.KL⟩ (table, d) := ⟨F, rfl, rfl, rfl, ho, hd⟩
  obtain ⟨p', j, d', real, real2, hp', ht, hd', hS, T, -, -⟩ := readKeyChains_of F table ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  obtain ⟨-, s₂, s₃⟩ := setting_keyGood hg hp
  have hR' : dryKey p.chains.key d.r.key = some R :=
    good_dry3 ⟨F.pol, F.lay, F.KL⟩ p hp key₀ h0 hf R hR (table, d) hg
  have hk : Key.check p.chains.key F.key = .ok table := by
    obtain ⟨_, q, _, -, -, -, -, -, -, -, -, -, -, hq, -, -, hk, -⟩ := h
    obtain rfl : p = q := Except.ok.inj (hp.symm.trans hq)
    exact hk
  obtain ⟨j₀, r₀, ht₀, h₀, -⟩ := key_check_reads _ _ _ hk
  obtain rfl : j = j₀ := by
    have := ht.symm.trans ht₀
    injection this with e
    exact (Prod.mk.inj e).2
  refine ⟨j, ht, ?_⟩
  rcases chains_returns_or_collidesInB C a cfg p.chains.key table T.toRead hS s₂ s₃ R hR' hok hB
    hsalts with hr | hc
  · exact Or.inl hr
  · have Tr := T.toRead
    have hR2 := hR'
    unfold dryKey at hR2
    rw [Tr.first_dry] at hR2
    have hd3 : Three.dry3 (Key.tailPublic p.chains.key table) d.r.key (d.rounds1, d.dry) =
        some R := hR2
    obtain ⟨R₃, rfl⟩ := dry3_shape hd3 Tr.shared_dry
    exact Or.inr (keyCollidesB_of_record p.chains.key table F.key j r₀ h₀ Tr hS hd3 hc)

end OnBytes.Maker.Page
