-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LiveBehindLookup.lean: THE SMALLNESS TEST: BEHIND AN ACCEPTING STEP OF THE
DESCRIPTION's OWN MEMBER AT THE LOOKUP ON THE DIGITS, WHERE TWO TESTS ON THAT STEP's OWN CHALLENGES
SAY YES (`goodRun … .planes`, `goodK3Out`, Johnson/Desc/ProofFile/Honest/K3/GoodDraws.lean), THE
STATE's DATA PASS `planesLive` (Johnson/Desc/K8/Honest/PlanesFew.lean) AND `digitsLive`
(DigitsFew.lean). Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  `leaves_stage`   the leaves' stage is one of a lookup's stages
  `eps_of_good`   where the test for the planes' run says yes, the first element that the leaves'
      first round sampled does not read 0
  **`planes_behind_lookup`**   under the premises of `digits_heard_f9`
      (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsHeardLink.lean), the library's test on the
      rounds and the two tests' yes: `planesLive`
  `planes_of_goodK3`, `border_next`   the test for all of the lookup's slots holds the one for the
      planes' run; below the head's segment the lookup on the digits stands right in front of the
      batching
  **`digits_behind_lookup`**   at a segment below the head's: under the premises of
      `digits_heard_f9`, `goodK3Out`'s yes, and where the state behind the step is reached at the
      batching's number 14 l + 9: `digitsLive`
  **`live_behind_lookup`**   at a segment below the head's: from a state reached in front of the
      lookup's member and an accepting step of it, with both tests' yes (`goodK3`, `goodK3Out`): the
      state behind is reached in front of the batching and passes both
By: digits_heard_f9 · ok_of_okRoundsE (OkOfRounds.lean) · Good.eps_ne
(Johnson/Desc/ProofFile/Honest/K3/Good/Gives.lean) · `planes_of_silence`
(Johnson/P1K8R/PlanesOfSilence.lean) · `digits_at_batch` (Johnson/P1K8R/KeyFitOf.lean).
Limits. That the state's field f9 is the site's shape is a premise. The head's segment, where
another member stands between the lookup and the batching, is served by `planes_behind_lookup`
alone. That a step accepts, that the tests say yes and "reached" hold together at any run is not
shown. Nothing on any measure.
-/
import Johnson.P1K8R.KeyFitOf
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsHeardLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OkOfRounds
import Johnson.Desc.ProofFile.Honest.K3.Good.Gives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Maker
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (okRoundsE)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.K3 (goodK3 goodK3Out goodRun lookHeardAt OpenSame LFace stages spotsAt one
  firstRound Site lookSites)
open ProofFile.Honest.K3.Law.AtThr (digits_heard_f9 ok_of_okRoundsE)
open P5J (AtMgA TS)

/-- The leaves' stage is one of a lookup's stages. -/
theorem leaves_stage (f : LFace) : ProofFile.Honest.K3.Stage.leaves ∈ stages f := by
  unfold stages
  exact List.mem_append_right _ List.mem_cons_self

/-- Where the test for the planes' run says yes, the leaves' first sampled element does not read
0. -/
theorem eps_of_good {f : LFace} {rs : List Fmt.RoundView}
    (h : goodRun f .planes (rs.map (·.drawn)) = true) :
    Reading.gl.val (one rs (firstRound f .leaves)) ≠ 0 :=
  ProofFile.Honest.K3.Good.eps_ne h (leaves_stage f)
    (show (⟨.leaves, 0, 0, false⟩ : ProofFile.Honest.K3.Spot) ∈
      [(⟨.leaves, 0, 0, false⟩ : ProofFile.Honest.K3.Spot)] ++ _ from
      List.mem_append_left _ List.mem_cons_self) rfl

/-- The test for all of the lookup's slots holds the one for the planes' run. -/
theorem planes_of_goodK3 {f : LFace} {ds : List Fmt.Drawn} (h : goodK3 f ds = true) :
    goodRun f .planes ds = true := by
  unfold goodK3 at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

/-- Below the head's segment the lookup on the digits stands right in front of the batching. -/
theorem border_next {l : ℕ} (hl : l < 24) : borderOf l true + 1 = 14 * l + 9 := by
  show 14 * l + ((if true = true then 6 else 1) + (if l = 24 then 1 else 0)) + 2 + 1 =
    14 * l + 9
  rw [if_pos rfl, if_neg (by omega : ¬ l = 24)]

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **`planesLive` behind the step.** -/
theorem planes_behind_lookup (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 25)
    (hd : s.digits = true) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf s.link true]? = some blk) {ft : Nat} {sj sj' : TS} {n : Nat}
    {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn} (hstep : blk.step ft sj rs c = .ok (sj', n))
    (hf : ∀ tl, sj'.tl? = some tl → tl.f9 = s.shape) (hok : okRoundsE rs = true)
    (hm1 : goodRun (K3.faceOf s.shape) .planes (rs.map (·.drawn)) = true)
    (hm2 : goodK3Out (K3.faceOf s.shape) (rs.map (·.drawn)) = true) :
    ∃ tl, sj'.tl? = some tl ∧ planesLive tl = true := by
  obtain ⟨tl, g, t1, t2, W, -, l1, l2⟩ :=
    digits_heard_f9 h s hs hl hd blk hblk ft sj sj' n rs c hstep hf
  have e := hf tl t1
  refine ⟨tl, t1, planes_of_silence tl g (rs.map (·.drawn)) t2 W (by rw [e]; exact hm2) l1 ?_⟩
  rw [l2 (ok_of_okRoundsE rs hok), e]
  exact eps_of_good hm1

/-- **`digitsLive` behind the step, where its end is reached at the batching's number.** -/
theorem digits_behind_lookup (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 24)
    (hd : s.digits = true) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf s.link true]? = some blk) {ft : Nat} {sj sj' : TS} {n : Nat}
    {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn} (hstep : blk.step ft sj rs c = .ok (sj', n))
    (hf : ∀ tl, sj'.tl? = some tl → tl.f9 = s.shape)
    (hm2 : goodK3Out (K3.faceOf s.shape) (rs.map (·.drawn)) = true) {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * s.link + 9) (z, sj')) :
    ∃ tl, sj'.tl? = some tl ∧ digitsLive tl = true := by
  have hl' : s.link < 25 := by omega
  obtain ⟨tl, g, t1, t2, W, c1, -, -⟩ :=
    digits_heard_f9 h s hs hl' hd blk hblk ft sj sj' n rs c hstep hf
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * s.link + (if s.link = 24 then 11 else 9))
      (z, sj') := by
    rw [if_neg (by omega : ¬ s.link = 24)]
    exact hr
  obtain ⟨tl', t1', H⟩ := digits_at_batch h.scope h.reads O hl' hr'
  obtain rfl : tl = tl' := Option.some.inj (t1.symm.trans t1')
  exact ⟨tl, t1, H g (rs.map (·.drawn)) t2 W (by rw [hf tl t1]; exact hm2) c1⟩

/-- **Both, at the 24 segments where the lookup on the digits stands right in front of the
batching: from a state reached in front of the lookup's member and an accepting step of it.** -/
theorem live_behind_lookup (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 24)
    (hd : s.digits = true) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf s.link true]? = some blk) {sj sj' : TS}
    {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn} (hlen : rs.length = blk.rounds.length)
    (hstep : blk.step 0 sj rs c = .ok (sj', c.length))
    (hf : ∀ tl, sj'.tl? = some tl → tl.f9 = s.shape) (hok : okRoundsE rs = true)
    (hm1 : goodK3 (K3.faceOf s.shape) (rs.map (·.drawn)) = true)
    (hm2 : goodK3Out (K3.faceOf s.shape) (rs.map (·.drawn)) = true) {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf s.link true) (z, sj)) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * s.link + 9) (z, sj') ∧
      ∃ tl, sj'.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true := by
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * s.link + 9) (z, sj') := by
    rw [← border_next hl]
    exact Reach.succ hr hblk ⟨rs, c, hlen, hstep⟩
  obtain ⟨tl, t1, p⟩ := planes_behind_lookup h s hs (by omega) hd hblk hstep hf hok
    (planes_of_goodK3 hm1) hm2
  obtain ⟨tl', t1', q⟩ := digits_behind_lookup h s hs hl hd hblk hstep hf hm2 hr'
  obtain rfl : tl = tl' := Option.some.inj (t1.symm.trans t1')
  exact ⟨hr', tl, t1, p, q⟩

end

end P1K8

#print axioms P1K8.leaves_stage
#print axioms P1K8.eps_of_good
#print axioms P1K8.planes_of_goodK3
#print axioms P1K8.border_next
#print axioms P1K8.planes_behind_lookup
#print axioms P1K8.digits_behind_lookup
#print axioms P1K8.live_behind_lookup
