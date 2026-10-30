-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ZxAtFrame.lean: THE HONEST SIDE's FRAME: AT THE STATES THAT ITS FIELD hP' HANDS IN
FRONT OF EACH OF THE 25 BATCHINGS: THE POINT zx OF WHAT THE LOOKUP ON THE SEGMENT's CALLS HAS HEARD:
NO COORDINATE IS 0 OR 1, AND ITS SIZE: FROM THE SILENCE OF THAT LOOKUP's SECOND MARK. UNDER THE
DESCRIPTION's HEAD. Lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness,
soundness or hiding.
Why. The tables of reads on which `readsLive` (Johnson/Desc/K8/Honest/LinkedFew.lean) hangs are, at
most matrices of every sort of segment, made of cuts of this point.

  `border_calls`, `out_of_silent`   by evaluation; mark_silent
      (Johnson/Desc/ProofFile/Honest/Law/CoverFit.lean)
  **`calls_handed`**   `mid_handed` (Johnson/P1K8R/MidStepAtWalk.lean) at the calls' lookup's
      number; site_at_all_fifty (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/SiteAllFifty.lean),
      calls_heard_link, calls_heard_site (CallsHeardLink.lean), sites_shape_ok
      (Johnson/Desc/ProofFile/Honest/K3/Law/SitesOk.lean); `look_zx_fine`, `look_zx_size`
      (Johnson/P1K8R/ZxOfSilence.lean)
  **`zx_handed`**   `calls_handed`; `keeps_five`, `keeps_six`, `look_rides`
      (Johnson/P1K8R/KeepsBetween.lean)
Kin. The frame's authors' made_member (Johnson/Desc/ProofFile/Honest/Thread/MemberLaw.lean): an
earlier member's own step on its own slice of what was heard, and the fold behind it, AT THE THREAD;
its head tells the road that `calls_handed` and `zx_handed` walk at the walk. `border_calls`: the
authors of the layers' own kind have the name and the sentence at l = 2 g
(ProofFile.Honest.K4.border_calls, Johnson/Desc/ProofFile/Honest/K4/Law/LookMemberHead.lean).
`out_of_silent` IS THE SECOND ARM OF `good_of_quiet`'s PROOF (Johnson/P1K8R/LooksAtFrame.lean) AS A
LEMMA, from "no mark at the place speaks" where that has the marks' silence along a list: a second
text among this file's authors' own.
Limits. The head h is a hypothesis; the full size alone. That the walk returns, that its start obeys
the frame's law, that the lists named are among the marks asked and that these have been silent are
premises. IT SAYS NOTHING OF `readsLive` ITSELF: which table is which cut of zx, and that the tables
in front of the batching are made of what this lookup heard, are other files' matter. It is not laid
into a member of `FirstAsks` here. It stands over the files of the kind "lookup" on the honest side.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.MidStepAtWalk
import Johnson.P1K8R.ZxOfSilence
import Johnson.P1K8R.KeepsBetween
import Johnson.Desc.ProofFile.Honest.K3.Good.MarksList
import Johnson.Desc.ProofFile.Honest.K3.Law.SitesOk
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAllFifty
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CallsHeardLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Lay ChainProgress Mid Step walk Mark markOf marksQuiet mark_silent drawsFit)
open ProofFile.Honest.K3 (goodK3Out LFace Site lookSites)
open ProofFile.Honest.K3.Good (markOut k3Marks)
open ProofFile.Honest.K3.Law (sites_shape_ok)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty calls_heard_link calls_heard_site)
open P5J (AtMgA TS)

/-- The number of the lookup on a segment's calls in the flat list. -/
theorem border_calls (l : ℕ) : borderOf l false = 14 * l + 3 + (if l = 24 then 1 else 0) := by
  show 14 * l + ((if false = true then 6 else 1) + (if l = 24 then 1 else 0)) + 2 = _
  rw [if_neg (by decide)]
  omega

/-- Where no mark asked at the place a speaks, and the lookup's second mark at a is among those
asked: the lookup's second test says yes. -/
theorem out_of_silent {ms : List Mark} {a : Place} {f : LFace} (ho : markOut a f ∈ ms)
    {fr own : List Fmt.Drawn} (hs : markOf ms a fr own = none) : goodK3Out f own = true := by
  have hso : (markOf ms (markOut a f).place fr own).isSome = false := by
    show (markOf ms a fr own).isSome = false
    rw [hs]
    rfl
  have h' : (if goodK3Out f own = true
      then none else some "K3: a sample at which another kind's weight may die") = none :=
    mark_silent ho hso
  by_cases hb : goodK3Out f own = true
  · exact hb
  · rw [if_neg hb] at h'
    cases h'

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W Y : Type}
include h

/-- **AT ALL 25 SEGMENTS, AT WHAT THE FRAME's FIELD hP' HANDS IN FRONT OF THE BATCHING: THE OWN STEP
OF THE LOOKUP ON THE SEGMENT's CALLS**, to a state sk that is reached behind it: what that lookup
has heard stands at sk, no coordinate of its point zx is 0 or 1, that point has dT coordinates; and
the fold over the members between takes sk to the state s' that the field hands. Where the list of
the lookups' marks (`k3Marks`, Johnson/Desc/ProofFile/Honest/K3/Good/MarksList.lean) and the fit's
marks at A's members are among the marks asked and these have been silent. -/
theorem calls_handed (G₀ : ProofFile.Ground) {l : ℕ} (hl : l < 25) (ms : List Mark)
    (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * l + (if l = 24 then 11 else 9)) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = false ∧
      ∃ (blk : Block TS ProofFile.Cl) (sj sk : TS) (R : List Fmt.RoundView) (c : List Desc.OpenedColumn)
        (r₂ r₃ : List Fmt.RoundView) (c₂ c₃ : List Desc.OpenedColumn) (g : Forest.Heard),
        cF.blocksInOrder[borderOf l false]? = some blk ∧ blk.step 0 sj R c = .ok (sk, c.length) ∧
        Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf l false + 1) (zp, sk) ∧
        sk.lookHeard? = some g ∧ (∀ w ∈ g.zx.toList, Fine w) ∧ g.zx.size = s.shape.dT ∧
        foldBlocks 0 ((cF.blocksInOrder.take A.length).drop (borderOf l false + 1)) sk r₂ c₂ =
          .ok (s', r₃, c₃) := by
  obtain ⟨s, hs, rfl, hd, hp, -⟩ := site_at_all_fifty h l hl false
  obtain ⟨-, -, -, -, blk, hblk, hpl, -⟩ := calls_heard_link h s.link hl
  obtain ⟨hface, hok⟩ := sites_shape_ok Zp s hs
  have hlt : borderOf s.link false < A.length := by
    rw [hA, border_calls s.link]
    split <;> omega
  obtain ⟨sj, sk, R, c, r₂, r₃, c₂, c₃, -, g3, -, hsil, -, hr1, hfold⟩ :=
    mid_handed cF.blocksInOrder (ProofFile.startS Zp) zp hblk ms hall hfit hlt hpos L hft hm ha hn hq hz hv
  obtain ⟨-, g, -, -, -, hg, ho, -, -, -⟩ :=
    calls_heard_site h s hs hl hd blk hblk 0 sj sk c.length R c g3
  have hmo : markOut blk.place (K3.faceOf s.shape) ∈ ms := by
    rw [hpl, ← hp, ← hface]
    exact hsub _ (List.mem_flatMap.2 ⟨s, hs, List.mem_cons_of_mem _ List.mem_cons_self⟩)
  have hgo := out_of_silent hmo hsil
  exact ⟨s, hs, rfl, hd, blk, sj, sk, R, c, r₂, r₃, c₂, c₃, g, hblk, g3, hr1, hg,
    look_zx_fine s.shape g _ ho hgo hok, look_zx_size s.shape g _ ho hok, hfold⟩

/-- **SO, AT THE STATE THAT THE FIELD HANDS: WHAT THE LOOKUP ON THE SEGMENT's CALLS HAS HEARD STANDS
THERE, NO COORDINATE OF ITS POINT zx IS 0 OR 1, AND THAT POINT HAS dT COORDINATES.** The members
between keep it. -/
theorem zx_handed (G₀ : ProofFile.Ground) {l : ℕ} (hl : l < 25) (ms : List Mark)
    (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * l + (if l = 24 then 11 else 9)) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = false ∧ ∃ g, s'.lookHeard? = some g ∧
      (∀ w ∈ g.zx.toList, Fine w) ∧ g.zx.size = s.shape.dT := by
  obtain ⟨s, hs, e1, hd, -, -, sk, -, -, r₂, r₃, c₂, c₃, g, -, -, -, hg, hfine, hsz, hfold⟩ :=
    calls_handed h G₀ hl ms hsub hall hfit hA hpos L hft hm ha hn hq hz hv
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hk : OnPublicFiles.KeepsLook sk s' := by
    by_cases h24 : l = 24
    · rw [hA, if_pos h24, border_calls l, if_pos h24, h24] at hfold
      exact look_rides cF.blocksInOrder 341 6 (keeps_six h.scope h.reads O h.laid.planOk) hfold
    · rw [hA, if_neg h24, border_calls l, if_neg h24] at hfold
      exact look_rides cF.blocksInOrder (14 * l + 4) 5
        (keeps_five h.scope h.reads O h.laid.planOk (by omega)) hfold
  exact ⟨s, hs, e1, hd, g, hk g hg, hfine, hsz⟩

end

end P1K8

#print axioms P1K8.border_calls
#print axioms P1K8.out_of_silent
#print axioms P1K8.calls_handed
#print axioms P1K8.zx_handed
