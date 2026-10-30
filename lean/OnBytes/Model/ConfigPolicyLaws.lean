-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/ConfigPolicyLaws.lean: what three functions of OnBytes/Model/Config.lean return at a
policy with 2^8 ≤ theta < C, at the exponent sh = 8.

The three functions sort and describe an acceptance policy from its numbers alone. The program does
not import this file.
* `least_eight`: the least cost of a token, as `policyEmpty` and `aboveClip` compute it, is 256.
* `policyEmpty_zero`: `policyEmpty` returns 0: it finds none of the four kinds of policy under
  which, by its docstring, a result would mean nothing.
* `policyKind_clippedGap`: at sT = 4, `policyKind` returns "clipped-gap".
* `aboveClip_eq`: at 2^8 < theta, the value of `aboveClip` as one formula.

What this file does not claim. By the docstring of `policyEmpty`, a policy at which it returns 0
can still let every token through. Nothing is said on sh other than 8, on `policyKind` at sT other
than 4, on a model, or on what a verifier's acceptance shows.


-/
import OnBytes.Model.Config

set_option autoImplicit false

namespace OnBytes.Model

/-- The least cost of a token at sh = 8, as `policyEmpty` and `aboveClip` compute it. -/
theorem least_eight : (if 8 < 63 then 2 ^ 8 else 2 ^ 64 - 1 : Nat) = 256 := by decide

/-- At sh = 8, under the hypotheses 2^8 ≤ theta and theta < C, `policyEmpty` returns 0, whatever n
and cap are. -/
theorem policyEmpty_zero {n C theta cap : Nat} (h1 : 256 ≤ theta) (h2 : theta < C) :
    policyEmpty n C theta cap 8 = 0 := by
  have hne : (theta == C) = false := beq_eq_false_iff_ne.2 (Nat.ne_of_lt h2)
  unfold policyEmpty
  simp only [least_eight, hne, Bool.false_and]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rfl

/-- At sh = 8 and sT = 4, under the hypothesis theta < C, the policy's kind is "clipped-gap". -/
theorem policyKind_clippedGap {C theta cap s : Nat} (h : theta < C) :
    policyKind C theta cap s 8 4 = "clipped-gap" := by
  have hne : (C == theta) = false := beq_eq_false_iff_ne.2 (Nat.ne_of_gt h)
  unfold policyKind exactMatch
  simp [hne]

/-- At sh = 8, under the hypotheses 2^8 < theta and theta < C, `aboveClip` returns the least of
n (theta - 2^8) / (C - 2^8) rounded down, cap and n. What that number bounds is told in the
docstring of `aboveClip`; no theorem of this file is about it. -/
theorem aboveClip_eq {n C theta cap : Nat} (h1 : 256 < theta) (h2 : theta < C) :
    aboveClip n C theta cap 8 = min (n * (theta - 256) / (C - 256)) (min cap n) := by
  unfold aboveClip
  simp only [least_eight]
  rw [if_neg (by omega), if_pos h1]

end OnBytes.Model
