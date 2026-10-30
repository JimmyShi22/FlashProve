-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PlanesTrue.lean: the three true reads of the planes' tables at the layers
(K4ReadsTrue, Johnson/Top/H/K4PlanesWorth.lean) from the lookup's law of the reads (Fo.ReadsLaw,
OnBytes/Tie/Pv/Lookup/Port/FoReads.lean), where K4's text planesParts has returned.

K4ReadsTrue speaks of the forms that the text's readers return, with a default where a reader
refuses. Where planesParts has returned, no reader has refused at the columns spoken of
(planesParts_readers, Johnson/Road/K4/PlanesReaders.lean), and a reader that returns, returns the
form of one entry of the reads (U3at_some). The law says what that entry is.

Main names:
  `k4Col_value`: a reader that has returned is worth, in any world, entry t + x of the reads.
  `k4ReadsTrue_of_law`: K4ReadsTrue in the world of any ledger, from the law at the same entries.
  `k4ReadsTrue_pub`: at a public record Pub34: from ReadsTrue in that world (readsLaw_pub,
    Johnson/Road/K4/ReadsLawPub.lean).
  `k4ReadsTrue_entryOf`: at the record, with the entries entryOf
    (Johnson/Road/K4/EntryTrue.lean): ReadsTrue is no premise any more.
Limits. Premises: planesParts has returned; in the last two: that the planes' matrix has its rows in
one run of 2 ^ lmb (h1) and at least the planes' columns (h2), and that the planes' cells under nu
are the entries of the planes' matrix in M (h4). In the last the entries are true BY MAKE: nothing
ties them to what a prover has committed. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.PlanesReaders
import Johnson.Road.K4.ReadsLawPub
import Johnson.Road.K4.EntryTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model _root_.Fo Cb.Fo
open OnBytes.Model.Layer (Env matIx)
open OnBytes.Desc.First.K4 (planesParts)
open VerifiableInference.OnPublicFiles (k4Bit k4Pin k4Col K4ReadsTrue)

variable {K : Type} [Field K]

/-- A reader that has returned is worth entry t + x of the reads. -/
theorem k4Col_value (ρ : Reading K) (W : World K) (v : Env) (t x : ℕ)
    (h : (k4Col v t x).isSome = true) :
    ((k4Col v t x).getD {}).value ρ W = u3Val W.entry v.iU3 v.K3 (t + x) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
  rw [hb, Option.getD_some]
  unfold k4Col at hb
  split at hb
  · rw [U3at_some v t x b hb, u3Form_value]
  · cases hb

theorem k4Bit_zero (v : Env) (a b x : ℕ) : k4Bit v a b 0 x = k4Col v a x := rfl

theorem k4Bit_one (v : Env) (a b x : ℕ) : k4Bit v a b 1 x = k4Col v b x := rfl

theorem k4Pin_eq (v : Env) (t x : ℕ) : k4Pin v t x = k4Col v t x := rfl

/-- **The three true reads from the law of the reads.** -/
theorem k4ReadsTrue_of_law (ρ : Reading K) {v : Env} {fo : Forest.Heard} {pp : Aff × List Aff}
    (hpp : planesParts v fo = some pp) (H : Fork) (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K)
    (Lw : ∀ tB0 tB1 tP, v.tabAt "b-bits-0" = some tB0 → v.tabAt "b-bits-1" = some tB1 →
      v.tabAt "b-pin" = some tP →
      ReadsLaw fo.shape v.y.h.lmb (rdL ρ fo.zb0) (rdL ρ fo.zb1) ν entry v.iU3 v.K3 tB0 tB1 tP) :
    K4ReadsTrue ρ v fo H ν entry := by
  intro tB0 tB1 tP t0 t1 tp
  obtain ⟨a0, a1, ap, e0, e1, ep, hr⟩ := planesParts_readers hpp
  obtain rfl : a0 = tB0 := Option.some.inj (e0.symm.trans t0)
  obtain rfl : a1 = tB1 := Option.some.inj (e1.symm.trans t1)
  obtain rfl : ap = tP := Option.some.inj (ep.symm.trans tp)
  have L := Lw _ _ _ t0 t1 tp
  refine ⟨fun col hc => ?_, fun col hc => ?_, fun col hc => ?_⟩
  · have r := (hr col hc).1
    rw [k4Bit_zero] at r ⊢
    rw [k4Col_value ρ _ v a0 col r]
    exact L.bits0 col hc
  · have r := (hr col hc).2.1
    rw [k4Bit_one] at r ⊢
    rw [k4Col_value ρ _ v a1 col r]
    exact L.bits1 col hc
  · have r := (hr col hc).2.2
    rw [k4Pin_eq] at r ⊢
    rw [k4Col_value ρ _ v ap col r]
    exact L.count col hc

/-- **At a public record, from ReadsTrue.** -/
theorem k4ReadsTrue_pub (X : Rows.Pub34 K) (M : Mats K) (H : Fork) (ν : Pl → K)
    (entry : ℕ → ℕ → ℕ → K)
    (hRd : X.ReadsTrue (H.worldOf X.ρ (fun j => ν (.mask j)) entry) M)
    (h1 : (X.tl.mats.getD (matIx X.p.v.y).iB {}).m / 2 ^ X.p.v.y.h.lmb = 1)
    (h2 : planeCols X.H.fo.shape X.p.v.y.h.lmb ≤ (X.tl.mats.getD (matIx X.p.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ X.p.v.y.h.lmb, ∀ c < planeCols X.H.fo.shape X.p.v.y.h.lmb,
      M (matIx X.p.v.y).iB r c = ν (.cell r c))
    {pp : Aff × List Aff} (hpp : planesParts X.p.v X.H.fo = some pp) :
    K4ReadsTrue X.ρ X.p.v X.H.fo H ν entry :=
  k4ReadsTrue_of_law X.ρ hpp H ν entry fun _ _ _ t0 t1 tp =>
    readsLaw_pub X _ M hRd ν h1 h2 h4 t0 t1 tp

/-- **At a public record, with the true entries.** -/
theorem k4ReadsTrue_entryOf (X : Rows.Pub34 K) (M : Mats K) (H : Fork) (ν : Pl → K)
    (h1 : (X.tl.mats.getD (matIx X.p.v.y).iB {}).m / 2 ^ X.p.v.y.h.lmb = 1)
    (h2 : planeCols X.H.fo.shape X.p.v.y.h.lmb ≤ (X.tl.mats.getD (matIx X.p.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ X.p.v.y.h.lmb, ∀ c < planeCols X.H.fo.shape X.p.v.y.h.lmb,
      M (matIx X.p.v.y).iB r c = ν (.cell r c))
    {pp : Aff × List Aff} (hpp : planesParts X.p.v X.H.fo = some pp) :
    K4ReadsTrue X.ρ X.p.v X.H.fo H ν (entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 M) :=
  k4ReadsTrue_pub X M H ν _ (reads_true_pub X M rfl) h1 h2 h4 hpp

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4ReadsTrue_of_law
#print axioms OnBytes.Road.K4.k4ReadsTrue_pub
#print axioms OnBytes.Road.K4.k4ReadsTrue_entryOf
