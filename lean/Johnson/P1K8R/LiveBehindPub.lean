-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LiveBehindPub.lean: `live_behind_lookup` (Johnson/P1K8R/LiveBehindLookup.lean) WITH
ITS PREMISE ON THE STATE's FIELD f9 STRUCK: IN ITS PLACE ONE CLOSED SENTENCE ON THE PUBLIC PART. One
lemma; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding. No new argument.

  **`live_behind_pub`**   at a segment below the head's: where the public part's built segment's f9
      is the site's shape: from a state reached in front of the member at the lookup on the digits
      and an accepting step of it, with the library's test on the rounds and both tests' yes
      (`goodK3`, `goodK3Out`): the state behind is reached in front of the batching and passes
      `planesLive` and `digitsLive`
By: `live_behind_lookup`, `border_next` · `f9_at_batch` (Johnson/P1K8R/F9AtBatch.lean) ·
P1K8T.built_at (Johnson/P1K8R/Tied.lean) · K9Asks.built_tl
(Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean).
Limits. Those of LiveBehindLookup.lean, less the one on f9. The closed sentence is shown of no
public part here.
-/
import Johnson.P1K8R.LiveBehindLookup
import Johnson.P1K8R.F9AtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Maker
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (okRoundsE)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.K3 (goodK3 goodK3Out Site lookSites)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **Both tests behind the step, from a closed sentence on the public part.** -/
theorem live_behind_pub (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 24)
    (hd : s.digits = true) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf s.link true]? = some blk) {sj sj' : TS}
    {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn} (hlen : rs.length = blk.rounds.length)
    (hstep : blk.step 0 sj rs c = .ok (sj', c.length))
    (hp : ∀ X, Zp.p.built.links[s.link]? = some X → X.tl.f9 = s.shape)
    (hok : okRoundsE rs = true)
    (hm1 : goodK3 (K3.faceOf s.shape) (rs.map (·.drawn)) = true)
    (hm2 : goodK3Out (K3.faceOf s.shape) (rs.map (·.drawn)) = true) {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf s.link true) (z, sj)) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * s.link + 9) (z, sj') ∧
      ∃ tl, sj'.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Xl, e3⟩ := P1K8T.built_at h.scope h.reads O (by omega : s.link ≤ 24)
  obtain ⟨X, hX, -⟩ := K9Asks.built_tl O.blank e3
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * s.link + (if s.link = 24 then 11 else 9))
      (z, sj') := by
    rw [if_neg (by omega : ¬ s.link = 24), ← border_next hl]
    exact Reach.succ hr hblk ⟨rs, c, hlen, hstep⟩
  exact live_behind_lookup h s hs hl hd hblk hlen hstep
    (fun tl ht => (f9_at_batch h.scope h.reads O (by omega) hr' hX ht).trans (hp X hX))
    hok hm1 hm2 hr

end P1K8

#print axioms P1K8.live_behind_pub
