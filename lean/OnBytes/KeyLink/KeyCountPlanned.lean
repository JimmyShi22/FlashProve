-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/KeyLink/KeyCountPlanned.lean: at the planner's plain steps, ONE number bounds the questions
of the key file's reading through the oracle at every public digest and every file.

`preT_asks_one` (KeyCountOne.lean) asks that the parameters at all digests are wiped to one value.
OnBytes/Tie/ChainsAtCfg.lean has that what the planner's plain steps return at a digest c they
return at every c', with the chains put at c' (`plannedAt_at`). The key's chains put at c'
(`keyAtCfg`) are `KeyChains.atCfg` (OnBytes/Maker/AtCfg/Lay.lean), to the letter; and they are wiped
to what the chains are wiped to.

Main names:
  `keyAtCfg_eq`, `keyAtCfg_wipe`, and the proof's chains' like `proofAtCfg_eq`, `proofAtCfg_wipe`:
    by `rfl`.
  `ksPlanned_wipe`: if the plain steps return p at a digest c₀, whatever they return at a digest c
    is wiped to what p's key chains are wiped to.
  `preT_asks_planned`: then at every d and every file `preT` at `ksPlanned` asks at most
    `keyCount p.chains.key t₀` strings; t₀ any table.

Premises: the plain steps return p at c₀; c₀ has 32 bytes (in `ksPlanned_wipe` c too); EACH OF THE
SEVEN STRINGS OF PARAMETER BYTES IN p HAS FEWER THAN 2 ^ 64 BYTES (`plannedAt_at`'s own condition; a
yes of the test `shortB` gives it: `short_of_test`, OnBytes/Tie/PlanAtDigest.lean; the verifier
program does not run that test; by ChainsAtCfg.lean's head each of three files' yeses gives it for
one of the seven, two of them at a value of `planned` alone, so not at what `plannedAt` returns at
another digest).

Which hash. The planner's plain steps are `plannedAt` (OnBytes/Tie/ChainsAtCfg.lean). The format's
second hash function, a fixed function, is called in them, at every c alike: the head of
OnBytes/Tie/PlanAtDigest.lean says where.

Limits: the number is not evaluated. Nothing on which strings are asked. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.KeyLink.KeyCountOne
import OnBytes.KeyLink.KeyPreOwn

set_option autoImplicit false

namespace OnBytes.KeyLink

open OnBytes.Tie OnBytes.Model.Verify
open OnBytes.Params (KeyChains ProofChains TableName)
open OnBytes.Proof (TailRead)
open _root_.Iop (Dig)
open _root_.Run (digToBytes size_digToBytes)

/-- The key's chains put at a digest are `KeyChains.atCfg`. -/
theorem keyAtCfg_eq (k : KeyChains) (c : ByteArray) : keyAtCfg k c = k.atCfg c := rfl

/-- They are wiped to what the chains are wiped to. -/
theorem keyAtCfg_wipe (k : KeyChains) (c : ByteArray) : (keyAtCfg k c).wipe = k.wipe := rfl

/-- The proof's chains put at a digest are `ProofChains.atCfg`. -/
theorem proofAtCfg_eq (c : ProofChains) (d : ByteArray) : proofAtCfg c d = c.atCfg d := rfl

/-- They are wiped to what the chains are wiped to. -/
theorem proofAtCfg_wipe (c : ProofChains) (d : ByteArray) : (proofAtCfg c d).wipe = c.wipe := rfl

/-- **Whatever the plain steps return at a digest is wiped to one value.** -/
theorem ksPlanned_wipe {pol KL lay c₀ c : ByteArray} {p : Planned} {k : KeyChains}
    (hp : plannedAt pol KL (some lay) c₀ = .ok p) (h₀ : c₀.size = 32)
    (hb : ∀ n : ChainName, (p.chains.bytes n).size < 2 ^ 64) (hc : c.size = 32)
    (hk : ksPlanned pol KL lay c = some k) : k.wipe = p.chains.key.wipe := by
  have e := plannedAt_at h₀ hc hb hp
  unfold ksPlanned at hk
  rw [e] at hk
  cases hk
  rfl

/-- **One number at every digest and every file, at the planner's plain steps.** -/
theorem preT_asks_planned {D Out : Type} (Pt : List Bool → Prop) [DecidablePred Pt]
    (tab : D → KeyChains → List Bool → Dig 256) (cfgOf : D → Dig 256)
    (asm : KeyChains → ByteArray → TableName → TailRead → Option Out) {pol KL lay c₀ : ByteArray}
    {p : Planned} (hp : plannedAt pol KL (some lay) c₀ = .ok p) (h₀ : c₀.size = 32)
    (hb : ∀ n : ChainName, (p.chains.bytes n).size < 2 ^ 64) (t₀ : TableName) (d : D)
    (keyFile : ByteArray) :
    (preT Pt tab cfgOf (ksPlanned pol KL lay) asm d keyFile).QueryBound
      (keyCount p.chains.key t₀) :=
  preT_asks_one Pt tab cfgOf (ksPlanned pol KL lay) asm p.chains.key t₀
    (fun d' _ hk => ksPlanned_wipe hp h₀ hb (size_digToBytes (cfgOf d')) hk) d keyFile

end OnBytes.KeyLink
