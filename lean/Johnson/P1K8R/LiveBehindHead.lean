-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LiveBehindHead.lean: THE SMALLNESS TEST AT THE HEAD's SEGMENT: THE FELLOW OF
`live_behind_pub` (Johnson/P1K8R/LiveBehindPub.lean) WHERE ONE MEMBER MORE STANDS BETWEEN THE LOOKUP
ON THE DIGITS AND THE BATCHING. One lemma; NONE OF THE LIBRARY's GOALS. Nothing on completeness,
soundness or hiding. No new argument: calls.

  **`live_behind_head`**   at the head's segment: where the public part's built segment's f9 is the
      site's shape: from a state reached in front of the member at the lookup on the digits (number
      345), an accepting step of it and an accepting step of the member behind it (number 346), with
      the library's test on the lookup's rounds and both tests' yes (`goodK3`, `goodK3Out`) at these
      rounds' draws: the state behind the two is reached in front of the batching (number 347) and
      passes `planesLive` and `digitsLive`
By: P1K8S.merge_leaves (Johnson/P1K8R/WideAtSeat.lean): the member at 346 leaves the smallness
test's record whole · Sound.step_ok_iff (Johnson/Desc/Sound/RunIsDecide.lean) · `f9_at_batch`
(Johnson/P1K8R/F9AtBatch.lean) · digits_heard_f9 · `planes_of_silence` · `digits_at_batch` ·
`eps_of_good`, `planes_of_goodK3` (Johnson/P1K8R/LiveBehindLookup.lean).
Limits. The closed sentence on f9 is shown of no public part here. The description's head h is a
hypothesis; the full size alone. That there is a site on the digits is a premise. That the two steps
accept, that the tests say yes and "reached" hold together at any run is not shown. Nothing on any
measure.
-/
import Johnson.P1K8R.LiveBehindPub
import Johnson.P1K8R.WideAtSeat

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
open ProofFile.Honest.K3.Law.AtThr (digits_heard_f9 ok_of_okRoundsE)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **Both tests in front of the head's batching.** -/
theorem live_behind_head (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link = 24)
    (hd : s.digits = true) {blk b11 : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf s.link true]? = some blk) (h11 : cF.blocksInOrder[346]? = some b11)
    {sj sj' sj'' : TS} {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn}
    (hlen : rs.length = blk.rounds.length) (hstep : blk.step 0 sj rs c = .ok (sj', c.length))
    (hy : StepYes 0 b11 sj' sj'')
    (hp : ∀ X, Zp.p.built.links[s.link]? = some X → X.tl.f9 = s.shape)
    (hok : okRoundsE rs = true)
    (hm1 : goodK3 (K3.faceOf s.shape) (rs.map (·.drawn)) = true)
    (hm2 : goodK3Out (K3.faceOf s.shape) (rs.map (·.drawn)) = true) {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf s.link true) (z, sj)) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, sj'') ∧
      ∃ tl, sj''.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e345 : borderOf s.link true + 1 = 346 := by
    rw [hl]
    rfl
  have r346 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sj') := by
    rw [← e345]
    exact Reach.succ hr hblk ⟨rs, c, hlen, hstep⟩
  have r347 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, sj'') := Reach.succ r346 h11 hy
  obtain ⟨bm, hbm, hLv⟩ := P1K8S.merge_leaves h.scope h.reads O
  obtain rfl : bm = b11 := Option.some.inj (hbm.symm.trans h11)
  obtain ⟨R, c', -, e⟩ := hy
  have etl : sj''.tl? = sj'.tl? :=
    hLv _ _ _ _ ((Sound.step_ok_iff 0 bm sj' sj'' R c' c'.length).1 e).2.2.2
  obtain ⟨Xl, e3⟩ := P1K8T.built_at h.scope h.reads O (by omega : s.link ≤ 24)
  obtain ⟨X, hX, -⟩ := K9Asks.built_tl O.blank e3
  have r347' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * s.link + (if s.link = 24 then 11 else 9))
      (z, sj'') := by
    rw [if_pos hl, hl]
    exact r347
  have hf : ∀ tl, sj'.tl? = some tl → tl.f9 = s.shape := fun tl ht =>
    (f9_at_batch h.scope h.reads O (by omega) r347' hX (etl.trans ht)).trans (hp X hX)
  obtain ⟨tl, g, t1, t2, W, c1, l1, l2⟩ :=
    digits_heard_f9 h s hs (by omega) hd blk hblk 0 sj sj' c.length rs c hstep hf
  have e9 := hf tl t1
  have p : planesLive tl = true :=
    planes_of_silence tl g (rs.map (·.drawn)) t2 W (by rw [e9]; exact hm2) l1 (by
      rw [l2 (ok_of_okRoundsE rs hok), e9]
      exact eps_of_good (planes_of_goodK3 hm1))
  obtain ⟨tl', t1', H⟩ := digits_at_batch h.scope h.reads O (by omega : s.link < 25) r347'
  obtain rfl : tl = tl' := Option.some.inj ((etl.trans t1).symm.trans t1')
  exact ⟨r347, tl, etl.trans t1, p,
    H g (rs.map (·.drawn)) t2 W (by rw [e9]; exact hm2) c1⟩

end P1K8

#print axioms P1K8.live_behind_head
