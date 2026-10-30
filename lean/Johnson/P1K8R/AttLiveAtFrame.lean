-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/AttLiveAtFrame.lean: THE HONEST SIDE's FRAME, AT THE TWELVE ATTENTION SEGMENTS:
`readsLive` (Johnson/Desc/K8/Honest/LinkedFew.lean) AT THE STATES THAT ITS FIELD hP' HANDS IN FRONT
OF THE BATCHING: FROM THE SILENCE OF THE LOOKUPS' SECOND MARK AT THE LOOKUP ON THE SEGMENT's CALLS
AND OF THE SEGMENT's OWN KIND's MARK ON ITS READ ROUNDS; AND ONE SENTENCE ON PUBLIC NUMBERS, WHICH
STAYS A PREMISE. UNDER THE DESCRIPTION's HEAD. Lemmas; NONE OF THE LIBRARY's GOALS. A joining.
Nothing on completeness, soundness or hiding.

  `look_zk_all`, `rawFine_of_silence`   static: `look_zk_fine`, `look_point`
      (Johnson/P1K8R/PieceOfSilence.lean); `look_zx_fine`, `look_zx_size`, `order_of_ok`
      (ZxOfSilence.lean)
  `fold_head`, `fold_window_end`   general, on the fold: foldBlocks_cons
      (Johnson/Desc/K15/FoldInv.lean); the lines by which `own_behind_calls`
      (Johnson/P1K8R/OwnBetween.lean) splits its first member off, as a lemma
  `fit_at_silent`   mark_silent (Johnson/Desc/ProofFile/Honest/Law/CoverFit.lean)
  **`attLive_handed`**   `pair_handed` (Johnson/P1K8R/TwoStepsAtWalk.lean) at 14 l + 3 and 14 l +
      4; at the first as `calls_handed` (ZxAtFrame.lean): its lines a third time; `att_g_behind`,
      `sizes_at_att` (AttBehindCalls.lean); **liveAll_at_batch**, mats_at_head
      (Johnson/Desc/K5/Honest/Law/ReadsLiveAll.lean); mkReads_silent
      (Johnson/Desc/ProofFile/Honest/K5/Law/MarkReads.lean), reads_len_of_fit (MarksFit.lean),
      rounds_at_head (MarksOwn.lean), k5Marks_head (MarksListLaw.lean), public_at_head
      (Johnson/Desc/K5/Honest/Law/PublicAtHead.lean); K5Law.ofPlan_size
      (Johnson/Desc/First/Att/ArmAttPublic.lean); `tiesLaid_at_batch`
      (Johnson/P1K8R/TiesAtBatch.lean); `readsLive_of` (Johnson/Desc/K8/Honest/ReadsLiveOf.lean);
      `liveTable_of_V` (Johnson/P1K8R/LiveTablesOfMark.lean)
Kin. `liveTables_of_mark` (Johnson/P1K8R/LiveTablesOfMark.lean): two of the NAs + 4 matrices, at
five decisions handed as premises. The segment's own kind's authors' mkReads_liveV_own
(MarksOwn.lean): the same two, from the mark's silence and the fit at the member's own rounds. The
frame's authors' fit_of_silent, fit_of_quiet (CoverFit.lean): the fit along a whole list;
`fit_at_silent` is at one member. fold_member (Johnson/Desc/ProofFile/Honest/Thread/MemberLaw.lean):
a member's own step off a fold, at any number; `fold_head` is at the first of a window, at the
decision.
Limits. **hdT IS A PREMISE HERE: A SENTENCE ON PUBLIC NUMBERS ALONE (no state, no run, no
challenge): `depth_at_att` (Johnson/P1K8R/DepthAtAtt.lean) has it under the head.** The head h is a
hypothesis; the full size alone. That the walk returns, that its start obeys the frame's law, that
the lists named are among the marks asked, that these have been silent and that the state handed is
reached are premises. Sufficient, not necessary. It is not laid into a member of `FirstAsks` here.
It stands over files of the kinds "lookup" and "attention's own rounds" on the honest side.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.TwoStepsAtWalk
import Johnson.P1K8R.ZxAtFrame
import Johnson.P1K8R.AttBehindCalls
import Johnson.P1K8R.PieceOfSilence
import Johnson.P1K8R.LiveTablesOfMark
import Johnson.Desc.K5.Honest.Law.ReadsLiveAll
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksOwn
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksListLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Maker
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (Reach StepYes step_less stepYes_decide)
open ProofFile.Honest (Lay ChainProgress Mid Step walk Mark markOf marksQuiet mark_silent drawsFit)
open ProofFile.Honest.K3 (goodK3Out lookHeardAt OpenSame lookSites)
open ProofFile.Honest.K3.Good (markOut k3Marks)
open ProofFile.Honest.K3.Law (sites_shape_ok)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty calls_heard_link calls_heard_site)
open ProofFile.Honest.K5 (k5Marks k5Marks_head mkReads mkReads_silent reads_len_of_fit rounds_at_head
  parAt)
open H2K5.Honest (readRounds Reads LiveV RawFine liveAll_at_batch mats_at_head public_at_head)
open P5J (AtMgA TS)

/-- The key point of EVERY call of what the lookup has heard, where its second test says yes: no
coordinate reads 0 or 1. `look_zk_fine` (Johnson/P1K8R/PieceOfSilence.lean) below the number of
calls; beyond it the array is empty. More than `RawFine` asks, which reads one call. -/
theorem look_zk_all (h : Forest.Shape) (g : Forest.Heard) (own : List Fmt.Drawn)
    (ho : OpenSame g (lookHeardAt h 0 own)) (hs : goodK3Out (K3.faceOf h) own = true)
    (hok : FoNums.ok h = true) : ∀ q, ∀ w ∈ (g.zk.getD q #[]).toList, Fine w := by
  obtain ⟨hl, hord⟩ := order_of_ok h hok
  intro q w hw
  by_cases hq : q < h.NC
  · exact look_zk_fine h g own ho hs hl hord q hq w hw
  · obtain ⟨p₀, -, -, -, hk⟩ := look_point h g own ho hs hl hord
    have hsz : g.zk.size = h.NC := by
      rw [hk, Array.size_map, Array.size_range]
    have e : g.zk.getD q #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    rw [e] at hw
    exact absurd hw (by simp)

/-- **What the files on `readsLive` at an attention segment ask of the raw points that the lookup on
the calls left (`RawFine`, Johnson/Desc/K5/Honest/Law/ReadsLiveAll.lean), from that lookup's second
test's yes**; hlm: a sentence on public numbers. -/
theorem rawFine_of_silence (h : Forest.Shape) (g : Forest.Heard) (own : List Fmt.Drawn)
    (ho : OpenSame g (lookHeardAt h 0 own)) (hs : goodK3Out (K3.faceOf h) own = true)
    (hok : FoNums.ok h = true) (geo : Att.P.Geo) (hlm : geo.lmS ≤ h.dT) : RawFine geo g :=
  ⟨look_zx_fine h g own ho hs hok, by rw [look_zx_size h g own ho hok]; exact hlm,
    fun u _ => look_zk_all h g own ho hs hok u.call⟩

section
variable {T Cl : Type}

/-- The first member of a window of a list, off the verifier's fold over the window: its decision's
yes, and the fold over the rest. -/
theorem fold_head {flat : List (Block T Cl)} {n N : ℕ} {b : Block T Cl}
    (hb : flat[n]? = some b) (hN : n < N) {s : T} {r : List Fmt.RoundView} {c : List Desc.OpenedColumn}
    {out : T × List Fmt.RoundView × List Desc.OpenedColumn}
    (hf : foldBlocks 0 ((flat.take N).drop n) s r c = .ok out) :
    ∃ (s₁ : T) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (r' : List Fmt.RoundView)
      (c' : List Desc.OpenedColumn), b.decide s rs gs = .ok s₁ ∧
      foldBlocks 0 ((flat.take N).drop (n + 1)) s₁ r' c' = .ok out := by
  have hb' : (flat.take N)[n]? = some b := by
    rw [List.getElem?_take, if_pos hN]
    exact hb
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 hb'
  rw [List.drop_eq_getElem_cons hi, e] at hf
  obtain ⟨s₁, k, hlen, st, hrest⟩ := foldBlocks_cons 0 b _ s r c _ hf
  obtain ⟨rs, gs, hd⟩ := stepYes_decide (⟨_, _, hlen, step_less st⟩ : StepYes 0 b s s₁)
  exact ⟨s₁, rs, gs, _, _, hd, hrest⟩

/-- The fold over an empty window stays. -/
theorem fold_window_end {flat : List (Block T Cl)} {N : ℕ} {s t : T} {r r' : List Fmt.RoundView}
    {c c' : List Desc.OpenedColumn}
    (hf : foldBlocks 0 ((flat.take N).drop N) s r c = .ok (t, r', c')) : t = s := by
  have e : (flat.take N).drop N = [] :=
    List.drop_eq_nil_of_le (by rw [List.length_take]; omega)
  rw [e] at hf
  unfold foldBlocks at hf
  injection hf with hf
  exact (Prod.mk.inj hf).1.symm

end

/-- Where no mark asked at a member's place speaks and the fit's mark at that member is among those
asked: its rounds can draw these challenges. -/
theorem fit_at_silent {T Cl : Type} {ms : List Mark} (d : Block T Cl)
    (hfit : (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    {fr own : List Fmt.Drawn} (hs : markOf ms d.place fr own = none) :
    drawsFit d.rounds own = true := by
  have h' : (if drawsFit d.rounds own then none else some "its rounds cannot draw these") =
      (none : Option String) :=
    mark_silent hfit (by
      show (markOf ms d.place fr own).isSome = false
      rw [hs]
      rfl)
  by_cases hb : drawsFit d.rounds own = true
  · exact hb
  · rw [if_neg hb] at h'
    cases h'

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  {W Y : Type}
include h

/-- **AT THE TWELVE ATTENTION SEGMENTS: `readsLive` AT THE STATES THAT THE FRAME's FIELD hP' HANDS
IN FRONT OF THE BATCHING.** Where the lookups' marks (`k3Marks`), the marks of the segment's own
kind (`k5Marks`) and the fit's marks at A's members are among the marks asked and these have been
silent; hr: the state handed is reached (the field hands that too); **hdT: A SENTENCE ON PUBLIC
NUMBERS, A PREMISE HERE**: the shape of the lookup on the segment's calls has trees of depth lmS at
least. -/
theorem attLive_handed (G₀ : ProofFile.Ground) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hdT : ∀ s ∈ lookSites Zp, s.link = 2 * g + 1 → s.digits = false →
      (Att.P.parCOf a).geo.lmS ≤ s.shape.dT)
    (ms : List Mark) (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    (hsubA : ∀ mk ∈ k5Marks Zp Bs.G₀, mk ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * (2 * g + 1) + 9) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a₀ z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a₀ = .ok z) (hv : z.ver = some s')
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 9) (zp, s')) :
    ∃ tl, s'.tl? = some tl ∧ readsLive tl = true := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  have n24 : ¬ 2 * g + 1 = 24 := by omega
  -- the members
  obtain ⟨s, hs, el, hd, hp, -⟩ := site_at_all_fifty h (2 * g + 1) (by omega) false
  obtain ⟨-, -, -, -, blk₁, hb₁, hpl, -⟩ := calls_heard_link h (2 * g + 1) (by omega)
  obtain ⟨hface, hok⟩ := sites_shape_ok Zp s hs
  have hb : borderOf (2 * g + 1) false = 14 * (2 * g + 1) + 3 := by
    rw [border_calls, if_neg n24]
  have K := keeps_five h.scope h.reads O h.laid.planOk (l := 2 * g + 1) (by omega)
  obtain ⟨b4, f4, -⟩ := K 0 (by omega)
  obtain ⟨b5, f5, -⟩ := K 1 (by omega)
  obtain ⟨b6, f6, -⟩ := K 2 (by omega)
  obtain ⟨b7, f7, -⟩ := K 3 (by omega)
  obtain ⟨b8, f8, -⟩ := K 4 (by omega)
  have hb₁' : cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₁ := by
    rw [← hb]
    exact hb₁
  obtain ⟨sj, sk, sl, R₁, R₂, d₁, d₂, r₂, r₃, c₂, c₃, f₁, f₂, -, g3, -, hs1, -, k3, -, hs2, -, -,
    -, hfold⟩ := pair_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 14 * (2 * g + 1) + 3) hb₁' f4 ms
      hall hfit (by omega) hpos L hft hm ha hn hq hz hv
  rw [hA] at hfold
  -- what the lookup on the calls has heard
  have hb₁s : cF.blocksInOrder[borderOf s.link false]? = some blk₁ := by
    rw [el]
    exact hb₁
  obtain ⟨-, gH, -, -, -, hgH, ho, -, -, -⟩ :=
    calls_heard_site h s hs (by omega) hd blk₁ hb₁s 0 sj sk d₁.length R₁ d₁ g3
  have hmo : markOut blk₁.place (K3.faceOf s.shape) ∈ ms := by
    rw [hpl, ← hp, ← hface]
    exact hsub _ (List.mem_flatMap.2 ⟨s, hs, List.mem_cons_of_mem _ List.mem_cons_self⟩)
  have hraw : RawFine (Att.P.parCOf a).geo gH :=
    rawFine_of_silence s.shape gH _ ho (out_of_silent hmo hs1) hok _ (hdT s hs el hd)
  have hL : ∀ att G, sk.here = .att att → att.g = some G → RawFine (Att.P.parCOf a).geo G := by
    intro att G e1 e2
    rw [att_g_behind h.scope h.reads O h.laid.planOk (l := 2 * g + 1) (by omega) hb₁' g3 hgH
      att G e1 e2]
    exact hraw
  -- the segment's own kind's step, and the four behind
  have d4 := ((Sound.step_ok_iff 0 b4 sk sl R₂ d₂ d₂.length).1 k3).2.2.2
  obtain ⟨s6, rs5, gs5, r5, c5, d5, h5⟩ :=
    fold_head (n := 14 * (2 * g + 1) + 5) f5 (by omega) hfold
  obtain ⟨s7, rs6, gs6, r6, c6, d6, h6⟩ :=
    fold_head (n := 14 * (2 * g + 1) + 6) f6 (by omega) h5
  obtain ⟨s8, rs7, gs7, r7, c7, d7, h7⟩ :=
    fold_head (n := 14 * (2 * g + 1) + 7) f7 (by omega) h6
  obtain ⟨s9, rs8, gs8, r8, c8, d8, h8⟩ :=
    fold_head (n := 14 * (2 * g + 1) + 8) f8 (by omega) h7
  obtain rfl : s' = s9 := fold_window_end h8
  -- that kind's mark
  have hmem : b4 ∈ A := by
    have e : A[14 * (2 * g + 1) + 4]? = some b4 := by
      have k := f4
      rw [hall, List.getElem?_append_left (by omega)] at k
      exact k
    exact List.mem_of_getElem? e
  have hf := fit_at_silent b4 (hfit b4 hmem) hs2
  have Pu := public_at_head h hg ea
  have hlen : ∀ n ∈ readRounds a.own (Att.P.parCOf a).geo, n < (R₂.map (·.drawn)).length :=
    reads_len_of_fit (parAt Zp g a) a.S Pu.sized Pu.planned (by
      rw [← rounds_at_head h hg ea f4]
      exact hf)
  have hp4 : b4.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
    obtain ⟨Lk, b', bq, aq, e1, e2, _, e4, _⟩ := IM.k5_of h.scope h.reads O g hg
    have k := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (by omega : 2 * g + 1 ≤ 24) 2] at k
    obtain rfl : b' = b4 := Option.some.inj (k.symm.trans f4)
    exact IM.alone_place e4
  have hsay : (mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo).test f₂ (R₂.map (·.drawn)) = none :=
    mark_silent (hsubA _ (k5Marks_head h hB hg ea).1) (by
      show (markOf ms ⟨1, some (2 * g + 1), 3, .K5⟩ f₂ (R₂.map (·.drawn))).isSome = false
      rw [← hp4, hs2]
      rfl)
  have hk := mkReads_silent (2 * g + 1) #[] hlen hsay
  have hc : Reads ⟨#[], R₂.map (·.drawn)⟩ (R₂.map noDigest) := by
    intro i r hr
    rw [List.getElem?_map] at hr
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
    show ((R₂.map (·.drawn))[i]?).map (·.elems) = some (noDigest r').drawn.elems
    rw [List.getElem?_map, hr']
    rfl
  obtain ⟨tl, ht, hlive⟩ := liveAll_at_batch h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 _ hc hk hL
  -- the list of matrices, their number, the ties
  obtain ⟨q, tl', eq, ht', eNM, emats⟩ := sizes_at_att h.scope h.reads O hg hr
  obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
  rw [O.W] at eq
  obtain rfl : a = q := Option.some.inj (ea.symm.trans eq)
  obtain ⟨A0, pf, hA0, e0⟩ := H2K5.Door.planIs_all h g a ea
  have hNM : tl.NM = (Att.P.parCOf a).geo.NAs + 4 := by
    rw [eNM, K5Law.ofPlan_size ⟨_, _, _, A0, pf, hA0, e0⟩]
    exact mats_at_head h ea
  obtain ⟨tl'', ht'', hties⟩ := tiesLaid_at_batch h.scope h.reads O (l := 2 * g + 1) (by omega)
    (z := zp) (s := s') (by
      rw [if_neg n24]
      exact hr)
  obtain rfl : tl = tl'' := Option.some.inj (ht.symm.trans ht'')
  refine ⟨tl, ht, readsLive_of tl hties fun mu hmu => ?_⟩
  obtain ⟨n, Fn, hF, hV⟩ := hlive mu (by omega)
  exact ⟨Fn, liveTable_of_V emats hF hV⟩

end

end P1K8

#print axioms P1K8.look_zk_all
#print axioms P1K8.rawFine_of_silence
#print axioms P1K8.fold_head
#print axioms P1K8.fold_window_end
#print axioms P1K8.fit_at_silent
#print axioms P1K8.attLive_handed
