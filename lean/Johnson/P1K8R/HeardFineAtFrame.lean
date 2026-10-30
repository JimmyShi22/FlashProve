-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/HeardFineAtFrame.lean: THE HONEST SIDE's FRAME, AT THE HEAD's SEGMENT: AT WHAT ITS
FIELD hP' HANDS IN FRONT OF THE BATCHING: WHAT THE HEAD HAS HEARD BEHIND ITS OWN ROUNDS' OWN STEP
HAS FOUR POINTS NO COORDINATE OF WHICH IS 0 OR 1, AND THREE OF THEM THEIR SIZES: FROM THE SILENCE OF
THE LOOKUPS' SECOND MARK AT THE LOOKUP ON THE CALLS AND OF THAT SUB-PROTOCOL's OWN SECOND MARK.
UNDER THE DESCRIPTION's HEAD. Lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on
completeness, soundness or hiding.

  `mem_extract_mono`   on arrays
  **`heardFine_handed`**   `pair_handed` (Johnson/P1K8R/TwoStepsAtWalk.lean) at 340 and 341; at
      340 as `calls_handed` (ZxAtFrame.lean): its lines a second time; at 341: heardOf_at_accept
      (Johnson/Desc/ProofFile/Honest/K6/HeardAtYes.lean), k6_points_at_accept, headSumR_size
      (HeardPoints.lean), P4.k6_member_at_mg (Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean),
      P4.wellLaid_341 (Johnson/P4R/FreeAt341N.lean); `linked_fine`, `drawsOk_of_rounds`
      (Johnson/P1K8R/LinkedOfSilence.lean); `keeps_six` (KeepsBetween.lean); `zlSize_at_block`,
      `lsFits_in_scope` (ZlSizeAtStep.lean)
Kin. The sealed Core's clauses hX2, hsTV, hsTH (Johnson/Desc/Reads/LiesBehind.lean): Zl's text and
two of the three sizes, as premises' forms behind steps' yeses. That kind's authors'
tables_at_accept (Johnson/Desc/ProofFile/Honest/K6/HeardAtYes.lean). `mem_extract_mono`: "a member
of a cut is a member of the whole" stands four times: the sealed Fo.Tp.mem_extract
(Johnson/Top/H/Keep/CEndPoint.lean), called here; mem_extract
(Johnson/Desc/K8/Honest/DigitsLiveOf.lean) and another of this file's authors'; mem_of_extract
(Johnson/Desc/K5/Honest/Law/ReadsLiveAll.lean); none is from cut to cut. That sl is reached at 342
is handed for whoever needs it: Johnson/P1K8R/AsksHeadLive.lean drops it.
Limits. The head h is a hypothesis; the full size alone. That the walk returns, that its start obeys
the frame's law, that the lists named are among the marks asked and that these have been silent are
premises. IT SAYS NOTHING OF `readsLive` ITSELF. It is not laid into a member of `FirstAsks` here.
It stands over files of the kinds "lookup" and "the output head's own rounds" on the honest side.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.TwoStepsAtWalk
import Johnson.P1K8R.ZxAtFrame
import Johnson.P1K8R.LinkedOfSilence
import Johnson.P1K8R.ZlSizeAtStep
import Johnson.Desc.ProofFile.Honest.K6.K6Marks
import Johnson.Desc.ProofFile.Honest.K6.HeardPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Kinds (Head.parOf Head.Law.readsOf Head.Law.workOf)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Lay ChainProgress Mid Step walk Mark markOf marksQuiet mark_silent drawsFit)
open ProofFile.Honest.K3 (lookSites)
open ProofFile.Honest.K3.Good (markOut k3Marks)
open ProofFile.Honest.K3.Law (sites_shape_ok)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty calls_heard_link calls_heard_site)
open ProofFile.Honest.K6 (part4Marks headParAt headPlace linkedK6TSays headLs headLt headLPd
  headSumR_size heardOf_at_accept k6_points_at_accept)
open P5J (AtMgA TS)

/-- A cut of an array from further on lies in the cut from earlier on, up to the same end. -/
theorem mem_extract_mono {α : Type} {a : Array α} {i i' n : ℕ} {x : α} (hi : i' ≤ i)
    (h : x ∈ (a.extract i n).toList) : x ∈ (a.extract i' n).toList := by
  rw [Array.toList_extract] at h ⊢
  have h' : x ∈ (a.toList.drop i).take (n - i) := h
  show x ∈ (a.toList.drop i').take (n - i')
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h'
  rw [List.getElem?_take] at hj
  by_cases hlt : j < n - i
  · rw [if_pos hlt, List.getElem?_drop] at hj
    refine List.mem_iff_getElem?.2 ⟨(i - i') + j, ?_⟩
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop,
      show i' + (i - i' + j) = i + j by omega]
    exact hj
  · rw [if_neg hlt] at hj
    exact nomatch hj

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  {W Y : Type}
include h

/-- **AT THE HEAD's SEGMENT, AT WHAT THE FRAME's FIELD hP' HANDS IN FRONT OF THE BATCHING: THE STATE
sl BEHIND THE OUTPUT HEAD's OWN ROUNDS' OWN STEP**, reached at 342: what the head has heard there,
x, has: no coordinate of Zl, of the last la of wpl.r, of tH.r, of tV.r reads 0 or 1; and Zl, tH.r,
tV.r have their sizes; and the fold over the five members between takes sl to the state s' that the
field hands. Where the lookups' marks (`k3Marks`), that sub-protocol's marks (`part4Marks`, at a
ground whose public structure is the head's) and the fit's marks at A's members are among the marks
asked and these have been silent. The seven clauses stand unfolded, in the form of a premise that
another author's files on `readsLive` at the head's segment ask under the name HeardFine. -/
theorem heardFine_handed (G₀ G₁ : ProofFile.Ground) (hG : G₁.W = P5J.At.X Zp) (ms : List Mark)
    (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms) (hsubK : ∀ mk ∈ part4Marks Zp G₁, mk ∈ ms)
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
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ (sl : TS) (o : HeadOwn) (x : Head.Heard) (r₂ r₃ : List Fmt.RoundView) (c₂ c₃ : List Desc.OpenedColumn),
      Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 342 (zp, sl) ∧ sl.here = .head o ∧ o.x = some x ∧
      ((∀ w ∈ x.Zl.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) ∧
        (∀ ZV, Own.tailOf x.wpl.r (P5J.At.X Zp).hS.la = some ZV →
          ∀ w ∈ ZV.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) ∧
        (∀ w ∈ x.tH.r.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) ∧
        (∀ w ∈ x.tV.r.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) ∧
        x.Zl.size = (P5J.At.X Zp).hS.ls + (P5J.At.X Zp).hS.lt ∧
        x.tH.r.size = (P5J.At.X Zp).hS.lt ∧ x.tV.r.size = (P5J.At.X Zp).hS.lt) ∧
      foldBlocks 0 ((cF.blocksInOrder.take 347).drop 342) sl r₂ c₂ = .ok (s', r₃, c₃) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  -- the two members
  obtain ⟨s, hs, e24, hd, hp, -⟩ := site_at_all_fifty h 24 (by omega) false
  obtain ⟨-, -, -, -, blk₁, hb₁, hpl, -⟩ := calls_heard_link h 24 (by omega)
  obtain ⟨hface, hok⟩ := sites_shape_ok Zp s hs
  have hb340 : borderOf 24 false = 340 := rfl
  obtain ⟨blk₂, hb₂, M⟩ := P4.k6_member_at_mg h.toAtMg
  rw [hb340] at hb₁
  obtain ⟨sj, sk, sl, R₁, R₂, d₁, d₂, r₂, r₃, c₂, c₃, f₁, f₂, -, g3, -, hs1, -, k3, k4, hs2, -,
    hr1, hr2, hfold⟩ := pair_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 340) hb₁ hb₂ ms hall hfit
      (by omega) hpos L hft hm ha hn hq hz hv
  rw [hA] at hfold
  -- what the lookup on the calls has heard
  have hb₁' : cF.blocksInOrder[borderOf s.link false]? = some blk₁ := by
    rw [e24, hb340]
    exact hb₁
  obtain ⟨-, g, -, -, -, hg, ho, -, -, -⟩ :=
    calls_heard_site h s hs (by omega) hd blk₁ hb₁' 0 sj sk d₁.length R₁ d₁ g3
  have hmo : markOut blk₁.place (K3.faceOf s.shape) ∈ ms := by
    rw [hpl, ← hp, ← hface]
    exact hsub _ (List.mem_flatMap.2 ⟨s, hs, List.mem_cons_of_mem _ List.mem_cons_self⟩)
  have hfine := look_zx_fine s.shape g _ ho (out_of_silent hmo hs1) hok
  -- the head's own rounds' step
  have hW := P4.wellLaid_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) hr1
    (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
  obtain ⟨o, x, g1, y, e1, e2, e3, -, -, -, eZl, -⟩ := heardOf_at_accept M k3 hW
  obtain ⟨o', x', e1', e2', ew, eV, eH⟩ := k6_points_at_accept M k3 hW
  have eo := e1'.symm.trans e1
  injection eo with eo
  subst eo
  obtain rfl : x' = x := Option.some.inj (e2'.symm.trans e2)
  have hd2 := ((Sound.step_ok_iff 0 blk₂ sk sl R₂ d₂ d₂.length).1 k3).2.2.2
  -- what the lookup heard is what the head's hearing took
  obtain ⟨b6, hb6, hk6⟩ := keeps_six h.scope h.reads O h.laid.planOk 0 (by omega)
  obtain rfl : blk₂ = b6 := Option.some.inj (hb₂.symm.trans hb6)
  have hl := hk6 sk _ _ sl hd2 g hg
  have hg1 : g1 = g := by
    unfold S.lookHeard? at hl
    rw [e1] at hl
    by_cases hop : o'.opened = true
    · have hl' : (if o'.opened = true then o'.lookHeard else none) = some g := hl
      rw [if_pos hop] at hl'
      exact Option.some.inj (e3.symm.trans hl')
    · have hl' : (if o'.opened = true then o'.lookHeard else none) = some g := hl
      rw [if_neg hop] at hl'
      exact nomatch hl'
  subst hg1
  -- that sub-protocol's second mark
  have hpar : headParAt G₁ = Head.parOf (P5J.At.X Zp).hS (Head.Law.workOf (P5J.At.X Zp)) := by
    show Head.parOf G₁.W.hS (Head.Law.workOf G₁.W) = _
    rw [hG]
  have hp2 : blk₂.place = headPlace 24 4 := by
    obtain ⟨_, _, _, _, hla⟩ := M
    exact IM.alone_place hla
  have hsay : linkedK6TSays (headParAt G₁) (R₂.map (·.drawn)) = none :=
    mark_silent (hsubK _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by
      show (markOf ms (headPlace 24 4) f₂ (R₂.map (·.drawn))).isSome = false
      rw [← hp2, hs2]
      rfl)
  rw [hpar] at hsay
  obtain ⟨q2, q7, q5⟩ := linked_fine _ _ (drawsOk_of_rounds R₂ k4) hsay
  -- Zl's size
  obtain ⟨o'', x'', z1, z2, z3⟩ := zlSize_at_block _ _ _ _ sk sl _ _ (M.decide_down hd2).1
    (lsFits_in_scope Z _ _ (P5J.At.X Zp) h.scope h.reads h.pubOne)
  have eo2 := z1.symm.trans e1
  injection eo2 with eo2
  subst eo2
  obtain rfl : x'' = x' := Option.some.inj (z2.symm.trans e2)
  refine ⟨sl, _, _, r₂, r₃, c₂, c₃, hr2, e1, e2, ⟨?_, ?_, ?_, ?_, z3, ?_, ?_⟩, hfold⟩
  · intro w hw
    rw [eZl] at hw
    have hw' : w ∈ (g1.zx.extract (g1.zx.size - ((P5J.At.X Zp).hS.ls + (P5J.At.X Zp).hS.lt))
      g1.zx.size).toList := hw
    exact hfine w (Fo.Tp.mem_extract hw')
  · intro ZV hZV w hw
    have eZ : ZV = x''.wpl.r.extract (x''.wpl.r.size - (P5J.At.X Zp).hS.la) x''.wpl.r.size := by
      unfold Own.tailOf Own.cutTail at hZV
      by_cases hc : (P5J.At.X Zp).hS.la > x''.wpl.r.size
      · rw [if_pos hc] at hZV
        exact absurd hZV (by simp)
      · rw [if_neg hc] at hZV
        exact (Option.some.inj hZV).symm
    rw [eZ, ew, headSumR_size] at hw
    refine q2 w (mem_extract_mono ?_ hw)
    have a1 : headLs (Head.parOf (P5J.At.X Zp).hS (Head.Law.workOf (P5J.At.X Zp))) =
        (P5J.At.X Zp).hS.la - (P5J.At.X Zp).hS.lt := rfl
    have a2 : headLt (Head.parOf (P5J.At.X Zp).hS (Head.Law.workOf (P5J.At.X Zp))) =
        (P5J.At.X Zp).hS.lt := rfl
    omega
  · intro w hw
    rw [eH] at hw
    exact q7 w hw
  · intro w hw
    rw [eV] at hw
    exact q5 w hw
  · rw [eH, headSumR_size]
    rfl
  · rw [eV, headSumR_size]
    rfl

end

end P1K8

#print axioms P1K8.mem_extract_mono
#print axioms P1K8.heardFine_handed
