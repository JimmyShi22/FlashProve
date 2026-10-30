-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3LawClaims.lean: the kind «lookup» (K3): the law that ties the proved block's
out-statement to a written list of claims: stated and proved, at the kind's block and at the kind
with riders.

The proved block of a sub-proof's lookup decides nothing: it puts out a statement at every
transcript. So the kind's law is not «its yes gives the block's yes»: it is on what is claimed.

Main names:
  `viewRounds ds τ`: a written transcript's rounds as plain data at the challenge field.
  `K3OutIsClaims` (a Prop), `k3OutIsClaims` (its proof): at the block of the kind kLookupCN, at
    every written transcript whose rounds meet the block's spec: the block puts out a statement x,
    and at all entries μ₀ and all key forms of the host that are worth the key vectors'
    extensions at the calls' points, x's out-claim holds if and only if every member of the
    library's list `claimsOf`, made of the public numbers and that transcript's rounds alone, is 0.
  `K3OutIsClaimsR`, `k3OutIsClaimsR`: the same at the kind with riders, kLookupCRN.

Limits. k3OutIsClaims names no hearing, no record of what was heard and no routine of the verifier
program: `claimsOf` is a definition of the library's, not the text that runs. Its premises are at
letters: the test on the public numbers; 5 ≤ lm ≤ kT + 5; two laws on the layout; the written
rounds meet the spec and hold no answers; the host's key forms. None is shown at a value here.
That every member is in fact claimed, once, at its number, is the link's law, not this one. It
stands on Johnson/Top/H/LookupCOutD.lean and OnBytes/Tie/Pv/Lookup/Forest/FoOutD.lean.
No soundness is claimed. Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupCOutD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-- A written transcript's rounds as plain data: for each round the scalars sent and the challenges
drawn, read at the challenge field. -/
abbrev viewRounds (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)) : Rounds Cb.Gl.E :=
  (rvT (ckP .two) ds τ).map (rdRV Reading.gl)

/-- **What the block puts out says what the list of claims says**, at the kind's own block. -/
def K3OutIsClaims : Prop :=
  ∀ (L : List LookupCCaller) (c : LookupCCaller), FoNums.ok c.h = true →
  ∀ (lm jLK : ℕ), 5 ≤ lm → lm ≤ c.h.kT + 5 →
  ∀ (mk : ℕ → c.J₀) (pl : ℕ → ℕ → c.J₀),
    (∀ s, c.L.mkS s = mk (jLK + s)) →
    (∀ t k j, k < c.h.NC →
      c.L.bc t k j = pl (FoNums.cellRC c.h lm (t, k, j)).1 (FoNums.cellRC c.h lm (t, k, j)).2) →
  ∀ (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF c.h)), (∀ d ∈ ds, NoAns d.items) →
  ∀ (a : (c.St₀ × c.Sg.Smp) × (c.Ex.prod c.Sg.ext).Str) (τ : Tr (uLT (ckP .two) ds)),
    ∃ x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀),
      ((kLookupCN L).toKind.block c).R.red.out a
          ((mapsT ds _ (specF c.h) (rkFor c.h c.L c.Ex).R hM.length_eq).view τ) =
        some ((x, a.1.2), a.2) ∧
      ∀ (KF : ℕ → AffK (Option c.J₀) Cb.Gl.E) (μ₀ : c.J₀ → Cb.Gl.E),
        KFokAt c.h (forK Cb.Gl.E c.L a.1.1)
          (fun k => (endsOf c.h lm jLK (viewRounds ds τ)).zk.getD k []) KF (zext μ₀) →
        ((forA Cb.Gl.E c.h c.L).lk.out id id x (zext μ₀) ↔
          ∀ y ∈ claimsOf c.h lm jLK (viewRounds ds τ) (fun p => zext μ₀ (placeOf mk pl p))
            (colsK c.h lm (endsOf c.h lm jLK (viewRounds ds τ)).zb0
              fun p => zext μ₀ (placeOf mk pl p))
            (colsK c.h lm (endsOf c.h lm jLK (viewRounds ds τ)).zb1
              fun p => zext μ₀ (placeOf mk pl p))
            (pinColK lm fun p => zext μ₀ (placeOf mk pl p))
            (fun k => AffK.val (KF k) (zext μ₀)), y = 0)

theorem k3OutIsClaims : K3OutIsClaims := by
  intro L c H lm jLK h5 hlm mk pl hmk hbc ds hM hA a τ
  refine ⟨_, lookKind_view L c H lm jLK mk pl hmk hbc ds hM hA a τ, fun KF μ₀ hKF => ?_⟩
  refine out_iff_claims c.h H c.L lm jLK h5 hlm mk pl (viewRounds ds τ) a.1.1 _ ?_ KF μ₀ hKF
  rw [← lookOutD_ofEnds]
  exact lookOutD_outAt Cb.Gl.E c.St₀ c.J₀ c.h lm jLK (placeOf mk pl) (viewRounds ds τ) a.1.1 H

/-- **The same at the kind with riders.** -/
def K3OutIsClaimsR : Prop :=
  ∀ (L : List LookupCRCaller) (r : LookupCRCaller), FoNums.ok r.c.h = true →
  ∀ (lm jLK : ℕ), 5 ≤ lm → lm ≤ r.c.h.kT + 5 →
  ∀ (mk : ℕ → r.c.J₀) (pl : ℕ → ℕ → r.c.J₀),
    (∀ s, r.c.L.mkS s = mk (jLK + s)) →
    (∀ t k j, k < r.c.h.NC →
      r.c.L.bc t k j =
        pl (FoNums.cellRC r.c.h lm (t, k, j)).1 (FoNums.cellRC r.c.h lm (t, k, j)).2) →
  ∀ (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF r.c.h)),
    (∀ d ∈ ds, NoAns d.items) →
  ∀ (a : (r.c.St₀ × r.c.Sg.Smp) × (r.c.Ex.prod r.c.Sg.ext).Str) (τ : Tr (uLT (ckP .two) ds)),
    ∃ x : TX (r.c.St₀ × Cb.Gl.E) Cb.Gl.E (Option r.c.J₀),
      ((kLookupCRN L).toKind.block r).R.red.out a
          ((mapsT ds _ (specF r.c.h) (rkFor r.c.h r.c.L r.c.Ex).R hM.length_eq).view τ) =
        some ((x, a.1.2), a.2) ∧
      ∀ (KF : ℕ → AffK (Option r.c.J₀) Cb.Gl.E) (μ₀ : r.c.J₀ → Cb.Gl.E),
        KFokAt r.c.h (forK Cb.Gl.E r.c.L a.1.1)
          (fun k => (endsOf r.c.h lm jLK (viewRounds ds τ)).zk.getD k []) KF (zext μ₀) →
        ((forA Cb.Gl.E r.c.h r.c.L).lk.out id id x (zext μ₀) ↔
          ∀ y ∈ claimsOf r.c.h lm jLK (viewRounds ds τ) (fun p => zext μ₀ (placeOf mk pl p))
            (colsK r.c.h lm (endsOf r.c.h lm jLK (viewRounds ds τ)).zb0
              fun p => zext μ₀ (placeOf mk pl p))
            (colsK r.c.h lm (endsOf r.c.h lm jLK (viewRounds ds τ)).zb1
              fun p => zext μ₀ (placeOf mk pl p))
            (pinColK lm fun p => zext μ₀ (placeOf mk pl p))
            (fun k => AffK.val (KF k) (zext μ₀)), y = 0)

theorem k3OutIsClaimsR : K3OutIsClaimsR := by
  intro L r H lm jLK h5 hlm mk pl hmk hbc ds hM hA a τ
  refine ⟨_, lookKindR_view L r H lm jLK mk pl hmk hbc ds hM hA a τ, fun KF μ₀ hKF => ?_⟩
  refine out_iff_claims r.c.h H r.c.L lm jLK h5 hlm mk pl (viewRounds ds τ) a.1.1 _ ?_ KF μ₀ hKF
  rw [← lookOutD_ofEnds]
  exact lookOutD_outAt Cb.Gl.E r.c.St₀ r.c.J₀ r.c.h lm jLK (placeOf mk pl) (viewRounds ds τ)
    a.1.1 H

#print axioms k3OutIsClaims
#print axioms k3OutIsClaimsR

end VerifiableInference.OnPublicFiles
