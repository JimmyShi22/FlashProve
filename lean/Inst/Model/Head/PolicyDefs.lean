-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/PolicyDefs.lean: the integer relations of the acceptance policy in the head segment:
the six hidden numbers of a position, the digits of a margin, and (B1) to (B4), (HE), (Z), over ℤ.

Definitions only, stated once, for the file that derives the policy from them
(Inst/Model/Head/PolicySound.lean) and the file that builds them from the policy
(Inst/Model/Head/PolicyHonest.lean).

All this is at sh = 8, F = 24, BIG = 2^37 (the factor of b in `marg`), the step table (`EX`,
Inst/Model/Tables.lean) and the public term Pub = 0.
  `rhoR`, `rhoC`   the masks: covered r ≤ t < e; counted r ≤ t < min(e, T − 1)
  `HRel`           nonneg, (B1) with the digits' ranges, (HE), (Z), (B2), (B3), (B4)
  `Fit`            the size bounds that both directions assume (Inst/Model/Head/PolicyHonest.lean;
                   on the side of soundness Policy/Rel/LedgerHeadNoWrap.lean): a bound on the
                   logits at the T positions and V tokens; C, θ < 2^40; cap < 2^16; 2 V ≤ 2^24
  `Hid.Bytes`      the ranges that the ledger's bytes give: c, u, k < 2^40 (five bytes), b < 2^8, z
                   < 2^16, zs < 2^24
(HE) is required only at pairs (v, t) with v < V, t covered: what the cells hold elsewhere is not a
matter of these relations.
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.ProgramR
import Inst.Model.Tables

set_option autoImplicit false

namespace Inst.Model.Head.Policy

open Inst.Model

/-- the six hidden numbers of a position -/
structure Hid where
  c : ℕ → ℤ
  b : ℕ → ℤ
  u : ℕ → ℤ
  k : ℕ → ℤ
  z : ℕ → ℤ
  zs : ℕ → ℤ

/-- the three digits of a margin and the looked-up value, at the pair (v, t) -/
structure Dig where
  K0 : ℕ → ℕ → ℤ
  K1 : ℕ → ℕ → ℤ
  K2 : ℕ → ℕ → ℤ
  ex : ℕ → ℕ → ℤ

section
variable {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P) (h : Hid) (d : Dig)

/-- ρ_t = [r ≤ t < e] -/
def rhoR (t : ℕ) : ℤ := if x.r ≤ t ∧ t < x.e then 1 else 0
/-- ρC_t = [r ≤ t < min(e, T − 1)] -/
def rhoC (t : ℕ) : ℤ := if t ∈ x.cnt then 1 else 0

/-- the margin at position t and token v -/
def marg (t v : ℕ) : ℤ :=
  lg t (x.w t) + rhoC x t * (h.c t + 2 ^ 37 * h.b t) - lg t v - if v < x.w t then 1 else 0

/-- The relations. `nonneg`: at a counted position the six hidden numbers are not negative. (B1), at
a covered position, for v < V: the margin is K2 + 2^8 K1 + 2^23 K0, each digit in its range. (HE),
at the same pairs: ex = EX[K1]. (Z) and (B4), at a counted position: zs + Σ_{v<V} ex = 2^24; c + k =
C. (B2) and (B3), sums over the counted positions: Σ (c + C b + u) = θ NB; Σ (b + z) = cap, or 0 if
NB = 0. c is the declared cost, b the overflow count (Inst/Model/Head/PolicyHonest.lean). -/
structure HRel : Prop where
  nonneg : ∀ t ∈ x.cnt, 0 ≤ h.c t ∧ 0 ≤ h.b t ∧ 0 ≤ h.u t ∧ 0 ≤ h.k t ∧ 0 ≤ h.z t ∧ 0 ≤ h.zs t
  B1 : ∀ t, x.r ≤ t → t < x.e →
    ∀ v < P.V,
      marg lg x h t v = d.K2 v t + 2 ^ 8 * d.K1 v t + 2 ^ 23 * d.K0 v t ∧
      (0 ≤ d.K0 v t ∧ d.K0 v t < 2 ^ 16) ∧
      (0 ≤ d.K1 v t ∧ d.K1 v t < 2 ^ 16) ∧
      (0 ≤ d.K2 v t ∧ d.K2 v t < 2 ^ 8)
  HE : ∀ t, x.r ≤ t → t < x.e → ∀ v < P.V, d.ex v t = EX (d.K1 v t).toNat
  Z : ∀ t ∈ x.cnt, h.zs t + ∑ v ∈ Finset.range P.V, d.ex v t = 2 ^ 24
  B2 : ∑ t ∈ x.cnt, (h.c t + pol.C * h.b t + h.u t) = pol.theta * x.NB
  B3 : ∑ t ∈ x.cnt, (h.b t + h.z t) = if 0 < x.NB then (pol.cap : ℤ) else 0
  B4 : ∀ t ∈ x.cnt, h.c t + h.k t = pol.C

/-- the ranges that the ledger's bytes give -/
def Hid.Bytes (t : ℕ) : Prop :=
  h.c t < 2 ^ 40 ∧ h.b t < 2 ^ 8 ∧ h.u t < 2 ^ 40 ∧ h.k t < 2 ^ 40 ∧
  h.z t < 2 ^ 16 ∧ h.zs t < 2 ^ 24

end

/-- The size bounds that both directions assume beyond the policy: Inst/Model/Head/PolicyHonest.lean
(`honest_rel`) to build the relations, Policy/Rel/LedgerHeadNoWrap.lean (`HRel_of_HCong`) to get
them from congruences modulo p. 68,715,282,431 is the greatest L with (2 L + 1) + 2^23 ≤ 2^37. -/
structure Fit (P : Params) (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) : Prop where
  lg : ∀ t < P.T, ∀ v < P.V, |lg t v| ≤ 68715282431
  C : pol.C < 2 ^ 40
  theta : pol.theta < 2 ^ 40
  cap : pol.cap < 2 ^ 16
  V : 2 * P.V ≤ 2 ^ 24

end Inst.Model.Head.Policy
