-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3OnOutStep.lean: the kind "lookup" (K3): THE PROMISE BEHIND A LOOKUP (the
Bool k3OnOut, Johnson/Desc/First/Look/K3Borders.lean) RIDES OVER ANY STEP OF THE VERIFIER's STATE
THAT LEAVES WHAT IT READS: free of any kind of sub-protocol. One theorem. NO SOUNDNESS IS CLAIMED.

Why. The public item lookOut stays open behind a lookup up to the front of the segment's batching:
every sub-protocol between has to keep it. k3OnOut_other_rides (K3DigitsOtherRides.lean) says so of
the digits' own .ok alone.

Main name.
  k3OnOut_step: from s to s', where both hold a ledger (F, G) · what the lookup's verifier has heard
    at the place's seat is one (hh) · next does not fall (hnext) · the later ledger has its sizes
    (hsz) · a stretch of free slots that ends at or below F.next stays free (hfree): k3OnOut p s =
    true → k3OnOut p s' = true.
WHAT k3OnOut READS OF THE STATE: heardAt p.digits s · s.fork?, and of that ledger three things
alone: p.first + elems h ≤ next · sizedB · freeB at the leaves' window, which by the Bool's own
conjuncts ends at or below p.first + elems h.
OBJECT. The Bool Desc.K3.k3OnOut.
Used by KeepAtMerge.lean (Johnson/Top/H0/MergeLaw/).
LETTERS. p, s, s', F, G.
IS IT EMPTY? At s' := s all premises hold.


Compiled with the whole library.
Limits. hfree is the substance: that a step fills no slot below next that was free is its own
files' to show.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OnOutOfLeft
import Johnson.Top.H.K3SeatFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.K3 (sizedB freeB heardAt k3OnIn k3OnOut)

/-- **The promise behind rides over a step that leaves what it reads.** -/
theorem k3OnOut_step (p : Desc.First.Look.P) (s s' : Desc.First.S) (F G : Fork)
    (hF : s.fork? = some F) (hG : s'.fork? = some G)
    (hh : heardAt p.digits s' = heardAt p.digits s) (hnext : F.next ≤ G.next)
    (hsz : sizedB G = true)
    (hfree : ∀ first n, first + n ≤ F.next → freeB F first n = true → freeB G first n = true)
    (hO : k3OnOut p s = true) : k3OnOut p s' = true := by
  unfold k3OnOut at hO ⊢
  rw [hG, hh]
  rw [hF] at hO
  cases hs : p.shape with
  | none =>
    rw [hs] at hO
    cases hO
  | some h₀ =>
    cases hg : heardAt p.digits s with
    | none =>
      rw [hs, hg] at hO
      cases hO
    | some g =>
      rw [hs, hg] at hO
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hO ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨c16, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩ := hO
      refine ⟨⟨⟨⟨⟨⟨⟨c16, ?_⟩, hsz⟩, ?_⟩, c10⟩, c11⟩, c12⟩, c13⟩
      · omega
      · exact hfree _ _ (by omega) c9

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3OnOut_step
