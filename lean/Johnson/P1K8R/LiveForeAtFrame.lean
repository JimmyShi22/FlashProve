-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LiveForeAtFrame.lean: THE SMALLNESS TEST's SECOND FALL IN THE HONEST SIDE's FRAME:
`LiveFore` (Johnson/P1K8R/BehindLast.lean: on what the lookup on the digits has heard: weights that
are not 0) HOLDS AT THE STATES THAT THE FRAME's FIELD hP' HANDS, WHERE THE LOOKUP's MARKS AND THE
FIT's MARKS HAVE BEEN SILENT AND THE FIELD HEARD (`HeardAtZ`, BehindHeard.lean) IS MET. UNDER THE
DESCRIPTION's HEAD. Lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness,
soundness or hiding.

  `call_lt_of_planned`   `PiecePlanned` (Johnson/P1K8R/WantAtBatch.lean), `joinPairs`
      (Johnson/Desc/K8/Honest/DigitsLiveOf.lean)
  **`liveFore_behind`**   at the state: `piece_of_silence` (Johnson/P1K8R/PieceOfSilence.lean);
      digits_heard_f9 (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsHeardLink.lean);
      site_made_at (Johnson/AtFull/Shape/SitesAtHead.lean); `hp_of_head` (LiveBehindAll.lean),
      `f9_at_batch` (F9AtBatch.lean), `public_at_batch` (PublicAtBatch.lean), `keyFit_of_B`
      (KeyFitOf.lean), `want_at_batch`
  **`liveFore_below_handed`**, **`liveFore_head_handed`**   `step_handed`, `two_handed`
      (Johnson/P1K8R/LooksAtFrame.lean); at the head's P1K8S.merge_leaves
Limits. `HeardAtZ s'` IS A PREMISE: `piece_of_silence` takes the calls' weights' second computation
off it. The description's head h is a hypothesis; the full size alone. That the walk returns, that
its start obeys the frame's law, that the marks named are among those asked and that they have been
silent are premises. It is not laid into a member of `FirstAsks` here. Nothing says that any state
is reached. It stands over the files of the kind "lookup" on the honest side.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LooksAtFrame
import Johnson.P1K8R.PieceOfSilence
import Johnson.P1K8R.BehindHeard

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
open ProofFile.Honest (Lay ChainProgress Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3 (goodK3 goodK3Out Site lookSites)
open ProofFile.Honest.K3.Good (markK3 markOut)
open ProofFile.Honest.K3.Law.AtThr (digits_heard_f9)
open Johnson.AtFull.Shape (site_made_at)
open P5J (AtMgA TS)

/-- A planned piece's call is one of the two. -/
theorem call_lt_of_planned {tl : HTailF2} {w : HTailF2.Want} (h : PiecePlanned tl w) :
    w.call < 2 := by
  have hm := h.mem
  unfold joinPairs at hm
  obtain ⟨q, hq, hx⟩ := List.mem_flatMap.1 hm
  obtain ⟨p, -, e⟩ := List.mem_map.1 hx
  have e1 : q = w.call := congrArg Prod.fst e
  rw [← e1]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  omega

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **BEHIND AN ACCEPTING STEP OF THE LOOKUP ON THE DIGITS WITH ITS SECOND TEST's YES: `LiveFore`**,
at a state t in front of the batching that holds the data which the step left (etl), is reached
there (hr) and meets the field heard (hH). l < 25. -/
theorem liveFore_behind (l : ℕ) (hl : l < 25) {X : LinkH} (hX : Zp.p.built.links[l]? = some X)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[borderOf l true]? = some blk) {ft n : ℕ}
    {sj sj' t : TS} {rs : List Fmt.RoundView} {c : List Desc.OpenedColumn}
    (hstep : blk.step ft sj rs c = .ok (sj', n))
    (hm2 : goodK3Out (K3.faceOf X.tl.f9) (rs.map (·.drawn)) = true) (etl : t.tl? = sj'.tl?)
    {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + (if l = 24 then 11 else 9)) (z, t))
    (hH : HeardAtZ t) : LiveFore t := by
  obtain ⟨s, hs, rfl, hd⟩ := site_made_at h l hl true
  have e := hp_of_head h s hs hl hd X hX
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Xl, e3⟩ := P1K8T.built_at h.scope h.reads O (by omega : s.link ≤ 24)
  have hf : ∀ tl, sj'.tl? = some tl → tl.f9 = s.shape := fun tl ht =>
    (f9_at_batch h.scope h.reads O hl hr hX (etl.trans ht)).trans e
  obtain ⟨tl, g, t1, t2, hOpen, -, -, -⟩ :=
    digits_heard_f9 h s hs hl hd blk hblk ft sj sj' n rs c hstep hf
  obtain ⟨tl₂, u1, -, -, u4⟩ := public_at_batch h.scope h.reads O hl hr
  obtain rfl : tl₂ = tl := Option.some.inj (u1.symm.trans (etl.trans t1))
  intro tl' F' ht hF g₀ nbW Wn hg hw
  obtain rfl : tl₂ = tl' := Option.some.inj (u1.symm.trans ht)
  obtain rfl : g = g₀ := Option.some.inj (t2.symm.trans hg)
  exact piece_of_silence tl₂ g (rs.map (·.drawn)) Wn hOpen
    (by rw [hf tl₂ t1, ← e]; exact hm2) (keyFit_of_B tl₂ u4)
    (fun w hw' => call_lt_of_planned
      (want_at_batch h.scope h.reads O h.laid.planOk hl e3 hr ht nbW Wn hw w hw'))
    (fun w hw' => (hH tl₂ ht g nbW Wn hg hw w hw').2)

section
variable {W Y : Type}

/-- **BELOW THE HEAD's SEGMENT: `LiveFore` AT THE STATES THAT THE FRAME's FIELD hP' HANDS, FROM THE
SILENCE OF THE LOOKUP's MARKS AND THE FIELD HEARD.** The premises of `looks_below_handed`
(Johnson/P1K8R/LooksAtFrame.lean), and `HeardAtZ s'`. -/
theorem liveFore_below_handed {l : ℕ} (hl : l < 24) {X : LinkH}
    (hX : Zp.p.built.links[l]? = some X) (ms : List Mark) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf l true]? = some blk)
    (h3 : markK3 blk.place (K3.faceOf X.tl.f9) ∈ ms)
    (ho : markOut blk.place (K3.faceOf X.tl.f9) ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * l + 9) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') (hH : HeardAtZ s') : LiveFore s' := by
  have hA' : A.length = borderOf l true + 1 := by
    rw [hA]
    exact (border_next hl).symm
  obtain ⟨sj, R, c, g2, g3, -, -, k2, hr⟩ := step_handed cF.blocksInOrder (ProofFile.startS Zp) zp hblk ms
    (K3.faceOf X.tl.f9) h3 ho hall hfit hA' hpos L hft hm ha hn hq hz hv
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + (if l = 24 then 11 else 9)) (zp, s') := by
    rw [if_neg (by omega : ¬ l = 24), ← border_next hl]
    exact Reach.succ hr hblk ⟨R, c, g2, g3⟩
  exact liveFore_behind h l (by omega) hX hblk g3 k2 rfl hr' hH

/-- **The like at the head's segment**, where the merge b₁ stands between: its step leaves the data.
-/
theorem liveFore_head_handed {X : LinkH} (hX : Zp.p.built.links[24]? = some X) (ms : List Mark)
    {blk b₁ : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[borderOf 24 true]? = some blk)
    (h11 : cF.blocksInOrder[346]? = some b₁)
    (h3 : markK3 blk.place (K3.faceOf X.tl.f9) ∈ ms)
    (ho : markOut blk.place (K3.faceOf X.tl.f9) ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 347) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') (hH : HeardAtZ s') : LiveFore s' := by
  have hA' : A.length = borderOf 24 true + 2 := hA
  have h11' : cF.blocksInOrder[borderOf 24 true + 1]? = some b₁ := h11
  obtain ⟨sj, sk, R, c, g2, g3, -, -, k2, g6, hr⟩ := two_handed cF.blocksInOrder (ProofFile.startS Zp) zp hblk
    h11' ms (K3.faceOf X.tl.f9) h3 ho hall hfit hA' hpos L hft hm ha hn hq hz hv
  have r346 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (zp, sk) :=
    Reach.succ hr hblk ⟨R, c, g2, g3⟩
  have r347 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * 24 + (if 24 = 24 then 11 else 9)) (zp, s') :=
    Reach.succ r346 h11 g6
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨bm, hbm, hLv⟩ := P1K8S.merge_leaves h.scope h.reads O
  obtain rfl : bm = b₁ := Option.some.inj (hbm.symm.trans h11)
  obtain ⟨R', c', -, e⟩ := g6
  have etl : s'.tl? = sk.tl? :=
    hLv _ _ _ _ ((Sound.step_ok_iff 0 bm sk s' R' c' c'.length).1 e).2.2.2
  exact liveFore_behind h 24 (by omega) hX hblk g3 k2 etl r347 hH

end

end

end P1K8

#print axioms P1K8.call_lt_of_planned
#print axioms P1K8.liveFore_behind
#print axioms P1K8.liveFore_below_handed
#print axioms P1K8.liveFore_head_handed
