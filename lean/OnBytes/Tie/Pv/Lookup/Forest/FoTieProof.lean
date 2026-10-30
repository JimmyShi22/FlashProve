-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTieProof.lean.
The tie at the sub-proofs' lookup (Fo.HCtie): its proof.

Main names:
  `tieRows_of`, `tiePlanes_of`, `tieJoin_of`: the three equations of values, behind HeardIs.
    `tiePlanes_of` and `tieJoin_of` have a second premise: FoNums.ok g.shape = true.
  `tieIff_of`: the «if and only if», from these three and Fo.hcClaims' clause.
  `hcTie_of`: HCout2V → HCtie. `hcTie`: HCtie.
The proof puts together: Fo.hcOut2V (what a run of Forest.pad that returns hands on);
Cb.Fo.PlaneClaims.rows_claim, planes_claim and Fo.join_claim (the byte-level forms' values);
Cb.Fo.PlaneClaims.planesK_congr, countK_congr (they read the planes' columns alone);
Fo.meet_view (the typed transcript of the rounds taken off the view); Fo.hcOut1E (the state put
out); Fo.hcClaims (what the typed verifier puts out holds if and only if all values of claimsOf are
0); Cb.Fo.shape_ok and Cb.Fo.holeCgl (the shape is lawful; knowledge soundness at a lawful shape).
Limits: those of the statement's file, OnBytes/Tie/Pv/Lookup/Forest/FoTieC.lean. Among them:
YNonZero is a premise on the view, before all that HCtie says of the typed verifier: the byte-level
routine does not test it; where it fails, nothing is said of the typed verifier. CallerOk is the
caller's to show. A caller that makes its claims on the planes or its claim on the keys by hand is
not served by TiePlanes, TieJoin and TieIff. Where the claims stand in the sub-proof's own
numbering, and that the caller adds them all, is not said here. Nothing is said of a run that does
not return. That the errors of Cb.Fo.forB are small is not said here.
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieC
import OnBytes.Tie.Pv.Lookup.Forest.FoPadAll

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Cb.Fo.Pin
open Cb.Fo.PlaneClaims OnBytes OnBytes.Model OnBytes.PscRun

theorem tieRows_of {g : Forest.Heard} {F' : Fork} {lm jLK : ℕ} {rs : Rounds Cb.Gl.E}
    (hI : HeardIs gl g F' (endsOf g.shape lm jLK rs)) : TieRows g F' lm jLK rs :=
  fun H hH ν entry => rows_claim gl g lm jLK rs F' hI H hH ν entry

theorem tiePlanes_of {g : Forest.Heard} {F' : Fork} {lm jLK : ℕ} {rs : Rounds Cb.Gl.E}
    (hI : HeardIs gl g F' (endsOf g.shape lm jLK rs)) (hok : FoNums.ok g.shape = true) :
    TiePlanes g F' lm jLK rs :=
  fun bit pin F1 G c1 c2 planes hb hp hl hS hr =>
    planes_claim gl g lm jLK rs bit pin hb hp F' F1 G c1 c2 planes hr hI hl hok hS

theorem tieJoin_of {g : Forest.Heard} {F' : Fork} {lm jLK : ℕ} {rs : Rounds Cb.Gl.E}
    (hI : HeardIs gl g F' (endsOf g.shape lm jLK rs)) (hok : FoNums.ok g.shape = true) :
    TieJoin g F' lm jLK rs := by
  intro KF hs H hH ν entry
  have hcE : g.cEnd.value gl (wOf H ν entry) =
      AffK.val ((endsOf g.shape lm jLK rs).cEndF, (endsOf g.shape lm jLK rs).cEndC) ν := by
    rw [(hI.cEnd H hH).2 (fun j => ν (.mask j)) entry,
      evalL_muOf (onMasks_keyTop g.shape lm jLK rs) ν]
    show _ = evalL ν (scale (-1) (endsOf g.shape lm jLK rs).cEndInc) + _
    rw [evalL_scale]
    ring
  exact join_claim gl (wOf H ν entry) g KF hok hs lm jLK rs ν hI.theta hI.alpha
    (fun k _ => by rw [rdL_getD, show rdL gl g.e = _ from hI.e]) hI.zy hcE

section
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- From the three equations of values and the clause of Fo.hcClaims at x. -/
theorem tieIff_of {g : Forest.Heard} {F' : Fork} {lm jLK : ℕ} {rs : Rounds Cb.Gl.E}
    {L : Lay Cb.Gl.E St₀ J₀} {mk : ℕ → J₀} {pl : ℕ → ℕ → J₀} {st : St₀}
    {x : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)} (hR : TieRows g F' lm jLK rs)
    (hPl : TiePlanes g F' lm jLK rs) (hJ : TieJoin g F' lm jLK rs)
    (hcl : ∀ (KF : ℕ → AffK (Option J₀) Cb.Gl.E) (μ₀ : J₀ → Cb.Gl.E),
      KFokAt g.shape (forK Cb.Gl.E L st) (fun k => (endsOf g.shape lm jLK rs).zk.getD k []) KF
        (zext μ₀) →
      ((forA Cb.Gl.E g.shape L).lk.out id id x (zext μ₀) ↔
        ∀ y ∈ claimsOf g.shape lm jLK rs (nuOf mk pl μ₀)
          (colsK g.shape lm (endsOf g.shape lm jLK rs).zb0 (nuOf mk pl μ₀))
          (colsK g.shape lm (endsOf g.shape lm jLK rs).zb1 (nuOf mk pl μ₀))
          (pinColK lm (nuOf mk pl μ₀)) (fun k => AffK.val (KF k) (zext μ₀)), y = 0)) :
    TieIff g F' lm jLK rs L mk pl st x := by
  intro bit pin KF F1 G H c1 c2 planes μ₀ entry hl1 hS1 hpc hGH hC
  obtain ⟨_, hFG, _, _, hp3⟩ := hPl bit pin F1 G c1 c2 planes hC.quietB hC.quietP hl1 hS1 hpc
  have hF'H : Later F' H := (hl1.trans hFG).trans hGH
  -- the caller's key forms as constants: the byte-level forms' own values
  have h3 := hcl (fun k => AffK.ofConst ((KF.getD k (Aff.ofConst zeroE)).value gl
    (wOf H (nuOf mk pl μ₀) entry))) μ₀ fun k hk => by
      rw [AffK.val_ofConst]
      exact hC.kf k hk
  simp only [AffK.val_ofConst] at h3
  rw [h3]
  have hE : (portForms g planes KF).map (fun f => f.value gl (wOf H (nuOf mk pl μ₀) entry)) =
      claimsOf g.shape lm jLK rs (nuOf mk pl μ₀)
        (colsK g.shape lm (endsOf g.shape lm jLK rs).zb0 (nuOf mk pl μ₀))
        (colsK g.shape lm (endsOf g.shape lm jLK rs).zb1 (nuOf mk pl μ₀))
        (pinColK lm (nuOf mk pl μ₀))
        (fun k => (KF.getD k (Aff.ofConst zeroE)).value gl (wOf H (nuOf mk pl μ₀) entry)) := by
    unfold portForms claimsOf
    rw [List.map_append, List.map_append, hR H hF'H (nuOf mk pl μ₀) entry,
      hp3 H hGH (nuOf mk pl μ₀) entry, List.map_singleton,
      hJ KF hC.nKF H hF'H (nuOf mk pl μ₀) entry, List.append_assoc]
    unfold claimLeaves claimBits
    rw [planesK_congr g.shape lm _ _ _ hC.col0, planesK_congr g.shape lm _ _ _ hC.col1,
      countK_congr g.shape lm _ _ hC.pinC]
    rfl
  rw [← hE]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

end

theorem hcTie_of (h2 : HCout2V) : HCtie := by
  intro calls pub lid lm F F' c c' g St₀ J₀ _ _ L mk pl hr hF hc h5 hlm hmk hbc
  obtain ⟨hSh, hL, rv, ht, hs, hI⟩ := h2 Cb.Gl.E gl calls pub lid lm F F' c c' g hr hF hc
  have H : FoNums.ok g.shape = true := by
    obtain ⟨h0, hs0, hp0, he⟩ := hSh
    rw [he]
    exact shape_ok hs0 hp0
  refine ⟨hSh, hL, rv, ht, hI, tieRows_of hI, tiePlanes_of hI H, tieJoin_of hI H,
    fun hz Ex a => ⟨meet_view gl g.shape L Ex rv (by have := ok_v H; omega) hs hz,
      fun Kc M Wp R0 msg₀ => holeCgl St₀ J₀ g.shape L Ex Kc M Wp R0 msg₀ H, fun τ hτ => ?_⟩⟩
  obtain ⟨x, hx, hcl⟩ :=
    hcClaims Cb.Gl.E St₀ J₀ g.shape L lm F.next mk pl H h5 hlm hmk hbc Ex a τ
  obtain ⟨x', hx', hst, _⟩ := hcOut1E Cb.Gl.E St₀ J₀ g.shape L lm F.next mk pl H hmk hbc Ex a τ
  have hxx : x' = x := congrArg Prod.fst (Option.some.inj (hx'.symm.trans hx))
  rw [hxx, hτ] at hst
  rw [hτ] at hcl
  exact ⟨x, hx, hst, tieIff_of (tieRows_of hI) (tiePlanes_of hI H) (tieJoin_of hI H) hcl⟩

/-- The tie at the sub-proofs' lookup. -/
theorem hcTie : HCtie := hcTie_of hcOut2V

end Fo
