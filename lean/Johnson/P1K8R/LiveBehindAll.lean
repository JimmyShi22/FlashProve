-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LiveBehindAll.lean: `live_behind_pub` (Johnson/P1K8R/LiveBehindPub.lean) AND
`live_behind_head` (Johnson/P1K8R/LiveBehindHead.lean) WITH THEIR CLOSED PREMISE ON THE PUBLIC PART
STRUCK: UNDER THE DESCRIPTION's HEAD THE BUILT SEGMENT's f9 IS THE SITE's SHAPE. Lemmas; NONE OF THE
LIBRARY's GOALS. Nothing on completeness, soundness or hiding. No new argument: calls.

  **`hp_of_head`**   under the head, at a site on the digits of a segment below 25: the public
      part's built segment's f9 is the site's shape
  **`live_below_head`**   `live_behind_pub` without that premise
  **`live_at_head`**   `live_behind_head` without that premise
By: site_f9_head (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsShapeHead.lean) · built_tl_head
(DigitsF9Reach.lean) · K9Asks.built_tl (Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean) ·
P1K8T.built_at (Johnson/P1K8R/Tied.lean).
Limits. The description's head h is a hypothesis; the full size alone. That there is a site on the
digits is a premise. That the steps accept, that the tests say yes and "reached" hold together at
any run is not shown. Nothing on any measure.
-/
import Johnson.P1K8R.LiveBehindHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsF9Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Maker
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (okRoundsE)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open ProofFile.Honest.K3 (goodK3 goodK3Out Site lookSites)
open ProofFile.Honest.K3.Law.AtThr (site_f9_head built_tl_head)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **Under the head the built segment's f9 is the site's shape.** -/
theorem hp_of_head (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 25)
    (hd : s.digits = true) :
    ∀ X, Zp.p.built.links[s.link]? = some X → X.tl.f9 = s.shape := by
  intro X hX
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Xl, e3⟩ := P1K8T.built_at h.scope h.reads O (by omega : s.link ≤ 24)
  obtain ⟨X', x1, x2⟩ := K9Asks.built_tl O.blank e3
  obtain rfl : X' = X := Option.some.inj (x1.symm.trans hX)
  obtain ⟨tlP, t1, t2⟩ := site_f9_head h s hs hd
  obtain rfl : tlP = Xl.tl := Option.some.inj (t1.symm.trans (built_tl_head h s.link hl O e3))
  rw [← x2, t2]

/-- **Below the head's segment, with no premise on data.** -/
theorem live_below_head (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 24)
    (hd : s.digits = true) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf s.link true]? = some blk) {sj sj' : TS}
    {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn} (hlen : rs.length = blk.rounds.length)
    (hstep : blk.step 0 sj rs c = .ok (sj', c.length))
    (hok : okRoundsE rs = true)
    (hm1 : goodK3 (K3.faceOf s.shape) (rs.map (·.drawn)) = true)
    (hm2 : goodK3Out (K3.faceOf s.shape) (rs.map (·.drawn)) = true) {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf s.link true) (z, sj)) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * s.link + 9) (z, sj') ∧
      ∃ tl, sj'.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true :=
  live_behind_pub h s hs hl hd hblk hlen hstep (hp_of_head h s hs (by omega) hd) hok hm1 hm2 hr

/-- **At the head's segment, with no premise on data.** -/
theorem live_at_head (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link = 24)
    (hd : s.digits = true) {blk b11 : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf s.link true]? = some blk) (h11 : cF.blocksInOrder[346]? = some b11)
    {sj sj' sj'' : TS} {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn}
    (hlen : rs.length = blk.rounds.length) (hstep : blk.step 0 sj rs c = .ok (sj', c.length))
    (hy : StepYes 0 b11 sj' sj'')
    (hok : okRoundsE rs = true)
    (hm1 : goodK3 (K3.faceOf s.shape) (rs.map (·.drawn)) = true)
    (hm2 : goodK3Out (K3.faceOf s.shape) (rs.map (·.drawn)) = true) {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf s.link true) (z, sj)) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, sj'') ∧
      ∃ tl, sj''.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true :=
  live_behind_head h s hs hl hd hblk h11 hlen hstep hy (hp_of_head h s hs (by omega) hd) hok hm1
    hm2 hr

end P1K8

#print axioms P1K8.hp_of_head
#print axioms P1K8.live_below_head
#print axioms P1K8.live_at_head
