-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookLayer.lean.
The layers' sub-proof: its lookup's claims inside the one equation, stretch by stretch.

The layers' sub-proof adds the lookup's claims in two places: `Forest.objects` at the head of its
list of claims, and `Layer.claimsPlanes` further down. It adds no claim on the keys: the join's
place is the start form of its batched sumcheck (FoStartClaim).

Main names:
  `layer_objects`: `objects_grows` (FoLookGrows) at the layers' record, and no more: over a run of
    `Forest.objects Hd.fo` the total grows by the rows of the record of end values, each as its form
    less its target, under the powers of theta from the number of claims before the run on.
  `layer_planes`: over a run of `Layer.claimsPlanes v fo`: if the world meets the law of the reads
    at the three tables of the planes' matrix, the total grows by `Fo.claimLeaves`, `Fo.claimBits`
    and the counts' sum at the columns' sums. The three tables' first entries are what `Env.tabAt`
    gives at the names b-bits-0, b-bits-1, b-pin.
  Among the arguments of these values stand the shape, lm, the lookup's first slot, the rounds heard
  by the lookup's routine and the reading ν of the places: no state of the sub-proof, and not the
  state's theta. The record's own field theta is another element: one of the lookup's own rounds.

Under: the run returns, from a state F that has one coefficient for each slot and whose arrays have
their sizes; the lookup's record holds the flat function's end values (`HeardIs`) in a state F0; for
`layer_planes`, F is a later state than F0 and the shape is lawful (`FoNums.ok`). The world is
`Fork.worldOf` of any state later than F0 (`layer_objects`) or than the run's end state
(`layer_planes`), with ν's values at the mask's places as the mask row, and with any entries.

Limit: identities at the one element theta of the state. Whether the reading ν, or the world's
entries of virtual rows of which the law of the reads speaks, hang on theta is not said here.
Some entries meet the law of the reads if the three tables lie one behind the other
(`readsLaw_some`, FoReads); that the layers' three tables do is not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun Cb.Fo

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The lookup's claims on mask entries, at the head of the layers' list of claims. -/
theorem layer_objects (Hd : Layer.Heard) (lm jLK : ℕ) (rsK : Rounds K) (F0 F G : Fork) (c c' : Ctx)
    (hO : Forest.objects Hd.fo F c = .ok (((), G), c'))
    (hI : HeardIs ρ Hd.fo F0 (endsOf Hd.fo.shape lm jLK rsK)) (hs : F.LS.size = F.ns)
    (hF : Sized F) :
    Later F G ∧ Sized G ∧ G.LS.size = G.ns ∧
      ∀ H, Later F0 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
        GrowsBy ρ F G (H.worldOf ρ (fun j => ν (.mask j)) entry)
          ((endsOf Hd.fo.shape lm jLK rsK).rows.map (rowRes ν)) :=
  objects_grows ρ Hd.fo lm jLK rsK F0 F G c c' hO hI hs hF

/-- **The lookup's three claims on the planes, in the layers' list of claims.** -/
theorem layer_planes (v : Layer.Env) (fo : Heard) (jLK : ℕ) (rsK : Rounds K) (F0 F G : Fork)
    (c c' : Ctx) (h : Layer.claimsPlanes v fo F c = .ok (((), G), c'))
    (hI : HeardIs ρ fo F0 (endsOf fo.shape v.y.h.lmb jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok fo.shape = true) (hs : F.LS.size = F.ns) (hF : Sized F) :
    ∃ tB0 tB1 tP, v.tabAt "b-bits-0" = some tB0 ∧ v.tabAt "b-bits-1" = some tB1 ∧
      v.tabAt "b-pin" = some tP ∧ Later F G ∧ Sized G ∧ G.LS.size = G.ns ∧
      ∀ H, Later G H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K),
        ReadsLaw fo.shape v.y.h.lmb (endsOf fo.shape v.y.h.lmb jLK rsK).zb0
          (endsOf fo.shape v.y.h.lmb jLK rsK).zb1 ν entry v.iU3 v.K3 tB0 tB1 tP →
        GrowsBy ρ F G (H.worldOf ρ (fun j => ν (.mask j)) entry)
          [claimLeaves fo.shape v.y.h.lmb jLK rsK ν
              (colsK fo.shape v.y.h.lmb (endsOf fo.shape v.y.h.lmb jLK rsK).zb0 ν),
            claimBits fo.shape v.y.h.lmb jLK rsK ν
              (colsK fo.shape v.y.h.lmb (endsOf fo.shape v.y.h.lmb jLK rsK).zb1 ν),
            Pin.countK fo.shape v.y.h.lmb (Pin.pinColK v.y.h.lmb ν)] := by
  rw [claimsPlanes_eq] at h
  obtain ⟨tB0, F1, c1, h1, k1⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨a1, e1, r1⟩ := (get_ok _ F c _).1 h1
  simp only [Prod.mk.injEq] at r1
  obtain ⟨⟨t1, f1⟩, g1⟩ := r1
  rw [f1, g1] at k1
  obtain ⟨tB1, F2, c2, h2, k2⟩ := (bind_ok _ _ F c _).1 k1
  obtain ⟨a2, e2, r2⟩ := (get_ok _ F c _).1 h2
  simp only [Prod.mk.injEq] at r2
  obtain ⟨⟨t2, f2⟩, g2⟩ := r2
  rw [f2, g2] at k2
  obtain ⟨tP, F3, c3, h3, k3⟩ := (bind_ok _ _ F c _).1 k2
  obtain ⟨a3, e3, r3⟩ := (get_ok _ F c _).1 h3
  simp only [Prod.mk.injEq] at r3
  obtain ⟨⟨t3, f3⟩, g3⟩ := r3
  rw [f3, g3] at k3
  exact ⟨tB0, tB1, tP, by rw [t1]; exact e1, by rw [t2]; exact e2, by rw [t3]; exact e3,
    planeLins_reads ρ fo v.y.h.lmb jLK rsK _ _ F0 F G c c' (readsAt_layer v tB0 tB1 tP F c) k3 hI
      h0 hok hs hF⟩

end
end Fo
