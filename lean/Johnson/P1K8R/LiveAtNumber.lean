-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LiveAtNumber.lean: `live_below_head` AND `live_at_head`
(Johnson/P1K8R/LiveBehindAll.lean) WITH THE SITE GONE FROM THEIR PREMISES: AT THE SEGMENT's NUMBER,
THE TWO MARKS' FACE READ OFF THE PUBLIC PART's OWN BUILT SEGMENT. Lemmas; NONE OF THE LIBRARY's
GOALS. Nothing on completeness, soundness or hiding. No new argument: three calls each.

  **`live_below_no`**   under the description's head, at l < 24, X the public part's built segment
      at l: a yes of the step of the lookup on the digits with both marks silent at K3.faceOf
      X.tl.f9, from a reached state: the state behind is reached in front of the batching, and its
      data pass `planesLive` and `digitsLive`
  **`live_at_head_no`**   the like at the head's segment, behind the merge's step
By: site_made_at (Johnson/AtFull/Shape/SitesAtHead.lean): under the head a site is made at each of
the fifty addresses · `hp_of_head` (Johnson/P1K8R/LiveBehindAll.lean).
Limits. The description's head h is a hypothesis; the full size alone. That the steps accept, that
the tests say yes and "reached" hold together at any run is not shown. Nothing on any measure.
-/
import Johnson.P1K8R.LiveBehindAll
import Johnson.AtFull.Shape.SitesAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Maker
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (okRoundsE)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open ProofFile.Honest.K3 (goodK3 goodK3Out Site lookSites)
open Johnson.AtFull.Shape (site_made_at)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **Below the head's segment, at the segment's number: no site among the premises.** -/
theorem live_below_no (l : ℕ) (hl : l < 24) {X : LinkH} (hX : Zp.p.built.links[l]? = some X)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[borderOf l true]? = some blk) {sj sj' : TS}
    {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn} (hlen : rs.length = blk.rounds.length)
    (hstep : blk.step 0 sj rs c = .ok (sj', c.length))
    (hok : okRoundsE rs = true)
    (hm1 : goodK3 (K3.faceOf X.tl.f9) (rs.map (·.drawn)) = true)
    (hm2 : goodK3Out (K3.faceOf X.tl.f9) (rs.map (·.drawn)) = true) {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf l true) (z, sj)) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + 9) (z, sj') ∧
      ∃ tl, sj'.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true := by
  obtain ⟨s, hs, rfl, hd⟩ := site_made_at h l (by omega) true
  have e := hp_of_head h s hs (by omega) hd X hX
  rw [e] at hm1 hm2
  exact live_below_head h s hs hl hd hblk hlen hstep hok hm1 hm2 hr

/-- **At the head's segment: no site among the premises.** -/
theorem live_at_head_no {X : LinkH} (hX : Zp.p.built.links[24]? = some X)
    {blk b11 : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf 24 true]? = some blk) (h11 : cF.blocksInOrder[346]? = some b11)
    {sj sj' sj'' : TS} {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn}
    (hlen : rs.length = blk.rounds.length) (hstep : blk.step 0 sj rs c = .ok (sj', c.length))
    (hy : StepYes 0 b11 sj' sj'')
    (hok : okRoundsE rs = true)
    (hm1 : goodK3 (K3.faceOf X.tl.f9) (rs.map (·.drawn)) = true)
    (hm2 : goodK3Out (K3.faceOf X.tl.f9) (rs.map (·.drawn)) = true) {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf 24 true) (z, sj)) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, sj'') ∧
      ∃ tl, sj''.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true := by
  obtain ⟨s, hs, hl, hd⟩ := site_made_at h 24 (by omega) true
  have e := hp_of_head h s hs (by omega) hd X (by rw [hl]; exact hX)
  rw [e] at hm1 hm2
  rw [← hl] at hblk hr
  exact live_at_head h s hs hl hd hblk h11 hlen hstep hy hok hm1 hm2 hr

end P1K8

#print axioms P1K8.live_below_no
#print axioms P1K8.live_at_head_no
