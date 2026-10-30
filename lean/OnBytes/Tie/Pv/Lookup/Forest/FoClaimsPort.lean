-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoClaimsPort.lean.
The join of the byte-level verifier is the last value of the lookup's list of claims.

OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean lists the claims of a sub-proof's lookup as values that
must be 0, from the record of
end values (Fo.endsOf). This file ties the last of them to the byte-level verifier's own form, as
an equation of values: so it sees the sign.

States:
  join_claim: if the fields theta, alpha, e, zy of the record that the byte-level routine returns
    (Forest.Heard) read as the fields of the record of end values, and the form cEnd has in a world
    W the value of the record's form at the reading ν of the places, then in W the value of the form
    that Forest.join returns (joinForm, OnBytes/Tie/Pv/Lookup/Forest/FoJoinRun.lean) is claimJoin,
    at the values of the caller's forms in W.
Premises: FoNums.ok of the record's shape; the caller hands in as many forms as there are calls;
the five equations between the two records. That a run of Forest.pad leaves them is not shown here.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoClaims
import OnBytes.Tie.Pv.Lookup.Forest.FoEndsE
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinRun

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes OnBytes.Model Cb.Fo

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

theorem join_claim (g : Forest.Heard) (KF : Array Aff) (H : FoNums.ok g.shape = true)
    (hs : KF.size = g.shape.NC) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K)
    (hθ : ρ.val g.theta = (endsOf g.shape lm jLK rs).theta)
    (hα : ρ.val g.alpha = (endsOf g.shape lm jLK rs).alpha)
    (he : ∀ c < g.shape.NC, ρ.val (g.e.getD c zeroE) = (endsOf g.shape lm jLK rs).e.getD c 0)
    (hzy : rdL ρ g.zy = (endsOf g.shape lm jLK rs).zy)
    (hcE : g.cEnd.value ρ W =
      AffK.val ((endsOf g.shape lm jLK rs).cEndF, (endsOf g.shape lm jLK rs).cEndC) ν) :
    (joinForm g KF).value ρ W =
      claimJoin g.shape lm jLK rs ν fun c => (KF.getD c (Aff.ofConst zeroE)).value ρ W := by
  have hN : g.shape.NC ≤ 2 ^ 64 := by
    obtain ⟨_, _, _, _, _, _, f2, _⟩ := ok_parts H
    exact le_trans f2 (by norm_num)
  rw [join_val ρ W g KF hs hN
    (fun c => AffK.ofConst ((KF.getD c (Aff.ofConst zeroE)).value ρ W))
    ((endsOf g.shape lm jLK rs).cEndF, (endsOf g.shape lm jLK rs).cEndC) ν
    (fun c _ => (AffK.val_ofConst _ _).symm) hcE]
  unfold claimJoin
  rw [val_joinK, val_joinK, hθ, hα, hzy]
  congr 2
  exact sum_congr rfl fun c hc => by
    rw [he c (mem_range.mp hc), ends_e g.shape H lm jLK rs c (mem_range.mp hc)]

end
end Fo
