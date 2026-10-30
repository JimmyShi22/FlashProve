-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/CfgOfRead.lean: the digest that is read back with a key file's one-time chain
is the digest at which the planner spelled the chain's parameter bytes: from ONE bound on a string's
length. General: no value is treated. Calls, with small steps in between.

Why. The clause "digest" of a key file's test on the file asks that the digest as read is not 32
zero bytes. hcfg_of_made (RowAtMade.lean) has it through OnBytes.TieK.G.chains_same
(OnBytes/TieK/G/SameChainsG.lean), which takes three bounds: on the key's one-time chain's string,
on the copy's file's chain's, and on the PROOF file's first chain's. So there a clause on the key
file hangs on a bound on the proof file. For its first conjunct chains_same itself calls
Given.read_cfg (OnBytes/Params/ReadBackLaws.lean) with the first bound alone. Here that road is
walked by itself.

Main names.
  cfg_of_read: k.oneTime.given.cfg = cfg, from configure's return, the digest's 32 bytes, the bound
  on made.keyOneTime, and the reader's return on the three strings that were made.
  digest_of_read: so the clause in its own words, where cfg is not 32 zero bytes.
Limits. That configure or the reader returns is a premise. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB9.ItemsAtMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open OnBytes OnBytes.Params

theorem cfg_of_read {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure l x cfg bits = .ok made) (h32 : cfg.size = 32)
    (hb₁ : made.keyOneTime.size < 2 ^ 64) {k : KeyChains}
    (hread : KeyChains.read made.keyOneTime made.keyShared made.keySecond = some k) :
    k.oneTime.given.cfg = cfg := by
  obtain ⟨P1, P2, P3, F, S2, S3, -, -, e1, -⟩ := configure_bytes hc
  obtain ⟨r1, -, -⟩ := KeyChains.read_three hread
  have g1 := OneTime.read_given r1
  rw [e1] at g1
  exact Given.read_cfg (by rw [← e1]; exact hb₁) h32 g1

/-- **The clause "digest".** -/
theorem digest_of_read {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure l x cfg bits = .ok made) (h32 : cfg.size = 32)
    (hne : (cfg != Fmt.zero32) = true) (hb₁ : made.keyOneTime.size < 2 ^ 64) {k : KeyChains}
    (hread : KeyChains.read made.keyOneTime made.keyShared made.keySecond = some k) :
    (k.oneTime.given.cfg != Fmt.zero32) = true := by
  rw [cfg_of_read hc h32 hb₁ hread]
  exact hne

end Johnson.KB4

#print axioms Johnson.KB4.cfg_of_read
#print axioms Johnson.KB4.digest_of_read
