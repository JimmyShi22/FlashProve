-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPlaneHeard.lean.
The three claims that read the planes of the counts, behind a run of the lookup's routine.

`planeClaims_at` (OnBytes/Tie/Pv/Lookup/Forest/FoPlaneAt.lean) takes what the record g holds as
hypotheses, one by one. Here they are read off `HeardIs` (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean):
the record g, with the state F, holds the flat function's end values
at
the rounds rs.

Main names:
  `planeClaims_heard`: a run of `Forest.planeClaims` from F that returns makes three forms; in every
    later state, at all entries μ that read the place that is no cell as 0, if the caller's forms
    for the columns below NC * 2 ^ (kT + 5 - lm) are worth the columns' sums, they are worth rowRes
    μ (rowEnd ..),
    - rowRes μ (rowBitE ..) and rowRes μ (rowNum ..), at the forest's numbers and the flat trace.

Under: `HeardIs`; the shape is lawful (`FoNums.ok`); the caller's routines are quiet; the state's
arrays have their sizes.

Limits: that a run of the lookup's routine leaves a record with `HeardIs` is not stated here. That
  the
caller's forms are worth the columns' sums is the caller's to state. Not claimed: anything on
soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneAt
import OnBytes.Tie.Pv.Lookup.Port.FoHeard

set_option autoImplicit false

namespace Cb.Fo.PlaneClaims
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

theorem planeClaims_heard (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F G : Fork) (c c' : Ctx) (rows : Array Aff)
    (h : planeClaims g lm bit pin F c = .ok ((rows, G), c'))
    (hI : HeardIs ρ g F (endsOf g.shape lm jLK rsK)) (hok : FoNums.ok g.shape = true)
    (hF : Sized F) :
    c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∃ r0 r1 r2, rows = #[r0, r1, r2] ∧
        ∀ H, Later G H → ∀ (μ : Pl → K) (entry : ℕ → ℕ → ℕ → K), μ .zero = 0 →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (bit 0 col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            colsK g.shape lm (endsOf g.shape lm jLK rsK).zb0 μ col) →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (bit 1 col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            colsK g.shape lm (endsOf g.shape lm jLK rsK).zb1 μ col) →
          (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
            (got (pin col) F c).value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
            Pin.pinColK lm μ col) →
          r0.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              rowRes μ (rowEnd (forN g.shape lm jLK rsK) (forTrace g.shape lm jLK rsK)) ∧
          r1.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              -rowRes μ (rowBitE (forN g.shape lm jLK rsK) (forTrace g.shape lm jLK rsK)) ∧
          r2.value ρ (H.worldOf ρ (fun j => μ (.mask j)) entry) =
              rowRes μ (rowNum (forN g.shape lm jLK rsK)) := by
  obtain ⟨mu, zd, rs, hRan, _, hdg⟩ := hI.lvRan
  have hdg' : dgOf zd = dgE (numsF g.shape lm jLK (thetaOf g.shape rsK)) := by
    have e1 : dgOf zd = (zd.map fun p => p.2).map (· - 1) := by
      unfold dgOf
      rw [List.map_map]
      rfl
    rw [e1, hdg, List.map_map]
    have e2 : ((fun x : ℕ => x - 1) ∘ fun x => x + 1) = id := funext fun x => by simp
    rw [e2, List.map_id]
    rfl
  exact planeClaims_at ρ g lm jLK (thetaOf g.shape rsK) (forTrace g.shape lm jLK rsK) bit pin hb hp
    F F F G c c' rows h hok (Later.refl F) (Later.refl F) hF hRan hdg' hI.lvStart hI.lvTg hI.lvEps
    hI.lvFin hI.lvXs hI.leavesA hI.zb0 hI.zb1 hI.sBitAt

end
end Cb.Fo.PlaneClaims
