-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5LedgerGuards.lean

Two guards for the premise of Lane5.lean at the head with the cost ledger (Lane5Ledger.lean).

Main theorems:
* "premiseL_met": the premise is not empty: at every lawful table and every policy within its bounds
  some index and some request with r = 1,023 and e = 1,024 have matrices that meet it (all weights
  and tokens 0; "Policy.TrueGuards.some_true"). It shows that, and no more.
* "no_premiseL": the premise is not true of everything, and the policy is read: under a policy with
  θ < 2^8 ≤ C no request that has a counted position has matrices that meet it, at any index
  ("Policy.TrueGuards.none_true": every cost is at least 2^8).

Not claimed: all that Lane5.lean and Lane5Ledger.lean do not claim.

-/
import Policy.Rel.TrueGuards
import Johnson.Road.Lane5Ledger

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

/-- **The premise at the ledger's head is not empty.** -/
theorem premiseL_met {s : Cm.Scales} {pol : AcceptancePolicy} (hs : s.Lawful) (hpol : Policy.PolCond pol) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (A : ℕ → Mx),
      x.r = 1023 ∧ x.e = 1024 ∧ Premise Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x A :=
  ⟨_, _, _, rfl, rfl, (premiseL_of_under hs hpol (Policy.TrueGuards.some_true hs pol)).2⟩

/-- **Under a policy that no counted position can meet, no matrices meet the premise.** -/
theorem no_premiseL {s : Cm.Scales} {pol : AcceptancePolicy} (hs : s.Lawful) (hpol : Policy.PolCond pol)
    (h1 : pol.theta < 256) (h2 : 256 ≤ pol.C) (i : Cm.Idx) (x : Instance ppref)
    (hre : x.r < x.e) (hN : 0 < x.NB) (A : ℕ → Mx) :
    ¬ Premise Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x A :=
  fun P => Policy.TrueGuards.none_true s pol h1 h2 i x hN (under_of_premise hs hpol hre P)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.premiseL_met
#print axioms OnBytes.Road.L5.no_premiseL
