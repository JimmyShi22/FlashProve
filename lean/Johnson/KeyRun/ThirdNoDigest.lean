-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/KeyRun/ThirdNoDigest.lean: `third` (Johnson/KeyRun/Third.lean), a check of a key file's
third chain, does not read the digest of the public parameter files.

The plan's key chains hold that digest, an answer of the format's hash, in two fields of each chain
(`Given.cfg`, `Given.bytes`). `OnBytes.Tie.keyAtCfg k c'` (OnBytes/Tie/ChainsAtCfg.lean) is k with
other bytes c' in the digest's place. Here: `third` and its two parts are the same functions at
both. Statements with proofs.
Main names: `pubOf_atCfg`, `claim₁_atCfg`, `dec₃_atCfg`, `thirdPublic_atCfg`, `third_atCfg`.
Limits: it speaks of these two fields alone. It says nothing of the views, whose drawn values are
answers of the hash, nor of how the plan's other fields are made. It says nothing of the verifier
program's check of that chain, whose hash chain starts from bytes that hold the digest. Nothing on
soundness.


-/
import Johnson.KeyRun.Third
import OnBytes.Tie.ChainsAtCfg

set_option autoImplicit false

namespace Johnson.KeyRun.Third

open OnBytes OnBytes.Params

/-- The public values that `dec₃` reads do not hold the digest. -/
theorem pubOf_atCfg (k : KeyChains) (c' : ByteArray) :
    pubOf (OnBytes.Tie.keyAtCfg k c') = pubOf k := rfl

/-- Nor does the claim that is made of the first view depend on it. -/
theorem claim₁_atCfg (k : KeyChains) (c' : ByteArray) (v₁ : Fmt.View) :
    FirstClaim.claim₁ (OnBytes.Tie.keyAtCfg k c').oneTime v₁ 0 =
      FirstClaim.claim₁ k.oneTime v₁ 0 := rfl

/-- **`dec₃` does not read the digest of the public parameter files.** -/
theorem dec₃_atCfg (k : KeyChains) (c' : ByteArray) (v₁ v₂ v₃ : Fmt.View) :
    dec₃ (OnBytes.Tie.keyAtCfg k c') v₁ v₂ v₃ = dec₃ k v₁ v₂ v₃ := by
  unfold dec₃
  rw [claim₁_atCfg, pubOf_atCfg]

/-- Nor do the tests on the plan. -/
theorem thirdPublic_atCfg (k : KeyChains) (c' : ByteArray) :
    thirdPublic (OnBytes.Tie.keyAtCfg k c') = thirdPublic k := rfl

/-- **`third` does not read the digest of the public parameter files.** -/
theorem third_atCfg (k : KeyChains) (c' : ByteArray) (v₁ v₂ v₃ : Fmt.View) :
    third (OnBytes.Tie.keyAtCfg k c') v₁ v₂ v₃ = third k v₁ v₂ v₃ := by
  unfold third thirdPublicOk
  rw [thirdPublic_atCfg, dec₃_atCfg]

end Johnson.KeyRun.Third

#print axioms Johnson.KeyRun.Third.dec₃_atCfg
#print axioms Johnson.KeyRun.Third.third_atCfg
