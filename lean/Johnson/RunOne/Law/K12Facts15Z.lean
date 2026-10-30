-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15Z.lean: THE SETTING OF ALL SIZES IS THE WRITTEN SETTING, IN SCOPE, AT ANY DIGEST. Two statements with their proofs, after the make of another file (Johnson/RunOne/Law/KeyInScope.lean: key_at_chains: the sized key at any digest) and of set_at_scope (Johnson/Goal/PlanValues/KeyPlansAtScope.lean: at the files' own digest).
OBJECT. m.p.chains.made.sized.set, m made by Key.madeAt at any digest. USER. Johnson/RunOne/Law/K12Facts15LS.lean: the bits of work of the ranges' test's place come of this setting.
Limits. One size. Nothing on soundness.

-/
import Johnson.RunOne.Law.KeyInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Facts15
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (recordSet)
open Lk6.AtPlan
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc.Key (madeAt)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.SourceIs (madeAt_parts)

theorem set_at_chains {v : VerifierAndGoals.FreeLines} {layout : Option ByteArray} {Z : Public} {cfg : ByteArray}
    {c : Chains} (hX : ReadOf (VerifierAndGoals.policyFile v) Z) (hc : chainsOf Z layout cfg = .ok c) :
    c.made.sized.set = recordSet := by
  obtain ⟨links, shapes, _, hm, -, -⟩ := chainsOf_parts hc
  obtain ⟨y, hy, _⟩ := hX
  rw [scan_frame (polLayout_scan hy)] at hm
  exact (Params.sized_link (Params.configure_plans hm).1).1

/-- **The setting of all sizes is the written setting, in scope, at any digest.** -/
theorem set_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m) :
    m.p.chains.made.sized.set = recordSet := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hP
  exact set_at_chains hP (madeAt_parts hm).2.1

end Johnson.RunOne.Law.K12Facts15

#print axioms Johnson.RunOne.Law.K12Facts15.set_at_chains
#print axioms Johnson.RunOne.Law.K12Facts15.set_in_scope
