-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/CondLit.lean: the records of Johnson/Desc/K1/Law/CondRow.lean at every sending
of the seven plans, at both examples, 119 and 46; Lean's kernel evaluates the test at each: it says
yes; so the promise of Johnson/Desc/K1/Law/CondRow.lean holds at each.

Nothing is written anew: a record takes its messages from Johnson/G/SendsLit.lean (what the verifier
is told at each sending) and its codes and its sampled messages with their radii from
Johnson/G/PackLit.lean, by its number.
  litRows: the two lists side by side
  litFull, litSmall: the 119 and the 46 records, in the order key 0, 1, 2, entry 0, proof 0, 1, 2
  litFull_length, litSmall_length: litRows zips the two lists, so these give the shorter list's
      length alone; that both lists have 119 and 46 entries is the theorem lengths in
      Johnson/G/SendsAll.lean
  litFull_ok, litSmall_ok: the test says yes at each: one evaluation in Lean's kernel for each
      example (decide +kernel)
  k01_full, k01_small: K01At at the two lists
  cond_at_full: so at every place whose codes and messages are those of one of the 119 records the
      kind's one Boolean holds at that record's radii

What is not claimed. The theorems speak of written numbers. That these are the planner's at the two
examples' public files is held by the tests of Johnson/G/SendsLitGuard.lean and
Johnson/G/PackLit.lean, by evaluation, not by a theorem; the limits of Johnson/G/Sends.lean (which
of the verifier's functions give a sending's list is a reading of its text) and of
Johnson/G/PackList.lean (the map from a message to its radius) stand. "Every sending" is every entry
"SEND seed" of a plan. What Johnson/Desc/K1/Law/CondRow.lean does not claim. Nothing on soundness,
on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.CondRow
import Johnson.G.SendsLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes Johnson.G

/-- The two lists side by side. -/
def litRows (S : List SendLit) (Pk : List (Codes × List (OracleShape × Nat))) : List SendRow :=
  (S.zip Pk).map fun x => ⟨x.2.1, x.1.2.2.2, x.2.2⟩

def litFull : List SendRow := litRows sendsFullLit packFullLit
def litSmall : List SendRow := litRows sendsSmallLit packSmallLit

theorem litFull_length : litFull.length = 119 := by decide +kernel
theorem litSmall_length : litSmall.length = 46 := by decide +kernel

/-- The test says yes at each of the 119. By evaluation in Lean's kernel. -/
theorem litFull_ok : (litFull.all fun r => r.ok) = true := by decide +kernel

/-- The test says yes at each of the 46. By evaluation in Lean's kernel. -/
theorem litSmall_ok : (litSmall.all fun r => r.ok) = true := by decide +kernel

/-- **The kind's condition at all 119 written sendings of the full-size example.** -/
theorem k01_full : K01At litFull := k01At _ litFull_ok

/-- **And at all 46 of the small example.** -/
theorem k01_small : K01At litSmall := k01At _ litSmall_ok

/-- In the letters of the kind's laws. -/
theorem cond_at_full (r : SendRow) (hr : r ∈ litFull) (P : Par) (hc : P.codes = r.cs)
    (hs : P.sent = r.sent.toArray) : condPort P (radFrom P r.l) = true :=
  (((k01_full r hr).2).1 P ⟨hc, hs⟩).1

end VerifiableInference.Desc.K1
