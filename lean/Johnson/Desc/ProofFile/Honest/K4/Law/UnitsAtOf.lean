-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/UnitsAtOf.lean: CONDITIONAL.

What is here. The public hypothesis `UnitsAt` of TripTiesOf.lean (the units of one panel's weight
claims) at every panel that the honest side lays, at any values in the place of the shown ones and
at claims made at any challenges and any token point: from the layout of the weights. It is the law
`panel_units` of Johnson/Road/K4/C/UnitsOfClaim.lean one level lower: that law speaks of the batched
sumcheck's data, at the second token sumcheck's end point; this one of the honest side's shared
data, so that the point can be a token's corner. The proof is that law's, step by step, over its own
lemmas.

  `unitsAt_of`   **the units, at every panel**

Limits. On public functions alone. HYPOTHESES: the functions that make the shared data and lay the
panels return; the verifier's function for the claims returns at the honest side's environment with
challenges and a point laid in; the layout of the weights is what the verifier's `wsLayOf` returns
for a model with routed experts; its widths d and fe are the layer sub-proof's; three public
inequalities between the two shapes (dq, f, and fe against f). No statement here ties the weights'
layout to the layer sub-proof's. No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TripTiesOf
import Johnson.Desc.ProofFile.Honest.K4.Law.TokSig
import Johnson.Road.K4.C.UnitsOfClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E)
open OnBytes.Model (WsClaim WsShape wsLayOf)
open OnBytes.Model.Layer (SBlk ClaimEnv)
open OnBytes.Road (claims_of_panels placed_f2 claimsT_routed_at claimsA_at claimsT_QK_at triStep_wy
  kindA_groups)
open OnBytes.Road.K4.C (sidesEnv sides_claims mem_of_forall₂ claimUnit_routed claimUnit_two
  claimUnit_last triStep_nums panelA_ny panelT_QK_ny kkSize_acc)
open OnBytes.Desc.First.K4.Honest

/-- **THE UNITS OF THE WEIGHT CLAIMS, AT EVERY PANEL THAT THE HONEST SIDE LAYS.** CONDITIONAL: on
every hypothesis named. -/
theorem unitsAt_of {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides}
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) {sh : Array E} {bl : Array SBlk}
    {places : ℕ} (hpan : S.panels sh = some (bl, places)) {rs rt : Array E} {cl : List WsClaim}
    (hcl : ({ S.ce with rs := rs, rt := rt } : ClaimEnv).weightClaims S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay) (hd : s.d = S.v.y.h.d)
    (hfe : s.fe = S.v.y.h.fe) (hdq : s.dq ≤ S.v.y.dq) (hf : s.f ≤ S.v.y.h.f)
    (hfef : s.fe ≤ S.v.y.h.f) : ∀ b ∈ bl.toList, UnitsAt Q.P.wsLay cl b := by
  obtain ⟨pans, hp, ebl⟩ := panels_open hpan
  obtain ⟨_, _, _, cv, cw⟩ := sides_claims hS
  have hv : (sidesEnv S sh).v = ({ S.ce with rs := rs, rt := rt } : ClaimEnv).v := cv.symm
  have hl' : wsLayOf s true lk = .ok ({ S.ce with rs := rs, rt := rt } : ClaimEnv).wsLay := by
    show wsLayOf s true lk = .ok S.ce.wsLay
    rw [cw]
    exact hl
  have G := (claims_of_panels _ _ hv S.TS hp hcl).2
  intro b hb v0 h0
  obtain ⟨b₀, hb₀, o, rfl⟩ := mem_of_forall₂ (placed_f2 pans.bl) b (by rw [← ebl]; exact hb)
  refine ⟨fun ht => ?_, fun ht i hi => ?_⟩
  · obtain ⟨q, -, g, -, lm, st, st', l, h3, hname, hlm, -, hstep, hbl, hclT, hlen, hat⟩ :=
      (G b₀ hb₀ v0 h0).2 ht
    obtain ⟨-, hatr⟩ := claimsT_routed_at _ g.name (hv ▸ h3) hname hclT
    have hlm' : lm < l.length := by omega
    have e2 : l[lm]? = some l[lm] := List.getElem?_eq_getElem hlm'
    obtain ⟨u, hu, hE, hwk, hkk, _⟩ :=
      claimUnit_routed hl' hname ((hatr lm hlm').symm.trans e2)
    obtain ⟨hwy, _⟩ := triStep_wy hstep hbl
    obtain ⟨hny, _⟩ := triStep_nums hstep hbl
    refine ⟨l[lm], u, hat.trans e2, by rw [← cw]; exact hu, hE, ?_, ?_⟩
    · show OnBytes.Road.wkOf u.g = b₀.wy
      rw [hwk, hwy, hd, hfe]
      rfl
    · show OnBytes.Road.K4.C.extR u "kk" ≤ b₀.ny
      rw [hkk, hny, hd, hfe]
      exact Nat.le_refl _
  · rcases (G b₀ hb₀ v0 h0).1 ht with ⟨q, -, g, -, st, l, hacc, -, hbl, hclA, hlen, hat⟩ |
      ⟨q, -, g, -, st, st', l, hname, -, hpt, hbl, hclT, hlen, hat⟩
    · have hi' : i < l.length := by
        rw [hlen]
        exact hi
      have e2 : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
      obtain ⟨k1, k2⟩ := kindA_groups g.name
        (({ S.ce with rs := rs, rt := rt } : ClaimEnv).v.isMoe
          (if g.name == "LR" then 2 * i + 1 else i))
        (({ S.ce with rs := rs, rt := rt } : ClaimEnv).v.isMoe
          (if g.name == "LR" then 2 * i + 1 else i)) hacc
      obtain ⟨u, hu, hE, hkk⟩ :=
        claimUnit_two hl' ((claimsA_at _ g.name hclA hacc i hi').symm.trans e2) k1 k2
      refine ⟨l[i], u, (hat i hi).trans e2, by rw [← cw]; exact hu, hE, ?_⟩
      show OnBytes.Road.K4.C.extR u "kk" ≤ b₀.ny
      rw [hkk, panelA_ny _ _ _ _ st hacc hbl]
      exact kkSize_acc _ _ hacc hd hdq hf hfef
    · have hi' : i < l.length := by
        rw [hlen]
        exact hi
      have e2 : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
      rw [hname] at hclT
      obtain ⟨-, AH, lfc, -, hatq⟩ := claimsT_QK_at _ hclT
      obtain ⟨u, hu, hE, hkk⟩ := claimUnit_last hl' ((hatq i hi').symm.trans e2)
      refine ⟨l[i], u, (hat i hi).trans e2, by rw [← cw]; exact hu, hE, ?_⟩
      show OnBytes.Road.K4.C.extR u "kk" ≤ b₀.ny
      rw [hkk, panelT_QK_ny _ _ _ _ st st' hname hpt hbl, hd]
      exact Nat.le_refl _

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.unitsAt_of
