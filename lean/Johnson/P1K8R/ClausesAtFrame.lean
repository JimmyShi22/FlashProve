-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ClausesAtFrame.lean: THE HONEST SIDE's FRAME, THE TWELVE ATTENTION SEGMENTS: WHAT THE
BATCHING's AUTHORS' BOUND FOR THE FALL OF THE FREE SLOTS ASKS OF THE STATE, IN ITS FIRST THREE
CONJUNCTS, HOLDS AT THE STATES THAT THE FRAME's FIELD hP' HANDS IN FRONT OF THE BATCHING, FROM THE
MARKS' SILENCE. Lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness
or hiding.

  `site_pars`   site_facts (Johnson/Desc/ProofFile/Honest/K3/Law/MemberSite.lean)
  **`clause_at_step`**   the lookups' authors' clause_member
      (Johnson/Desc/ProofFile/Honest/K3/Good/Live/ClauseMark.lean), next_behind (Windows.lean),
      site_hub (K3/Law/Thread/AtLink.lean), site_block (K3/Law/MemberSite.lean), memberAtSite
      (MemberAtSite.lean), drawsWork (Steps.lean), sites_shape_ok (SitesOk.lean); `fit_at_silent`
      (Johnson/P1K8R/AttLiveAtFrame.lean); mark_silent
      (Johnson/Desc/ProofFile/Honest/Law/CoverFit.lean)
  **`attClauses_handed`**   `clause_at_step` twice; `mid_handed`
      (Johnson/P1K8R/MidStepAtWalk.lean), `pair_handed` (TwoStepsAtWalk.lean), `keeps_five`,
      `look_rides` (KeepsBetween.lean), `fold_head`, `fold_window_end` (AttLiveAtFrame.lean);
      mkLive_held_own (Johnson/Desc/ProofFile/Honest/K5/Law/MarksOwn.lean), k5Marks_head
      (MarksListLaw.lean), TlOpen.tl_behind_look (Johnson/Desc/K5/Honest/Law/TlOpen.lean); calls_att
      (Windows.lean); OnPublicFiles.sized_upTo (Johnson/Desc/First/Look/K03RowsBare.lean), sized_iff
      (OnBytes/Tie/Pv/Att/PadLawsPaid.lean), Att.P.fork_front
      (Johnson/Desc/First/Att/K05BehindLay.lean); the lines on the segment's own kind's step, its
      place and its rounds stand in `attLive_handed` (AttLiveAtFrame.lean) too
Kin. The lookups' authors' clause_member_thin (K3/Good/Live/ClauseMarkThin.lean) and
next_atSite_thin (K3/Law/Thread/NextThin.lean): `clause_at_step`'s two halves at a member, under
IM.Open, the first WITH the premise hc. Not called: site_hub hands the lot's block, so their own
forms serve; NextThin.lean stands over the files under Johnson/Desc/ProofFile/Honest/Thread/, which
this file does not need. ON hc: their canAll_of_kit (K3/Good/MarkKit.lean) ends in canDraw through
CanAll: AT TYPED CHALLENGES, under a kit's clauses: the payer that they name (and, at a toy's kit,
their canAll_toy, K3/Good/MarkToy.lean); from the fit's mark's silence at a member's own rounds:
none that we found. Of `clause_at_step`'s second half besides: their next_atSite, next_ofPlace
(K3/Law/Thread/NextBehind.lean), under two premises more; in the library k3_calls_next
(Johnson/Desc/First/Look/K3CallsLookOut.lean) and its like in K3CallsMade.lean, at the calls' own
block. Of `site_pars`: their site_shape (K3/Law/Thread/K3Keeps.lean) is its second half, site_p_is
(LaysNextLight.lean) its first. `site_pars` draws the same four clauses of their site_facts as
`site_made_place` (Johnson/P1K8R/DepthAtAtt.lean): that file is not among this one's imports, direct
or indirect.
Limits. The head h is a hypothesis; the full size alone. That the walk returns, that its start obeys
the frame's law, that the lists named are among the marks asked and that these have been silent are
premises: what the silence costs is the marks' authors' matter. THREE CONJUNCTS OF FOUR: in the form
that the docstring names the fourth is the ledger's planned number of claims; in those authors'
younger form (k9_fallDebt_att_list, Johnson/Desc/ProofFile/Honest/K9/FallDebtAttList.lean) the same
three stand and the fourth is that the state is reached by the wrapped blocks. The fourth and the
wrap into their bound are the batching's authors' own. The attention segments alone; the two
conditions on what was heard stand at all 25 segments in Johnson/P1K8R/ClausesAtLinks.lean.
`clause_at_step` speaks at all fifty lookups, behind the member's own step; from there to the
batching it is carried in this file at the twelve alone. Sufficient, not necessary.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.AttLiveAtFrame
import Johnson.P1K8R.MidStepAtWalk
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.ClauseMark
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Windows
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsF9Reach
import Johnson.Desc.ProofFile.Honest.K3.Law.Steps
import Johnson.Desc.K5.Honest.Law.TlOpen
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.Desc.First.Att.K05BehindLay
import OnBytes.Tie.Pv.Att.PadLawsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Maker
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (Reach StepYes step_less stepYes_decide)
open ProofFile.Honest (Lay ChainProgress Mid Step walk Mark markOf marksQuiet mark_silent drawsFit)
open ProofFile.Honest.K3 (lookSites Site canDraw siteAt)
open ProofFile.Honest.K3.Good (markK3 k3Marks)
open ProofFile.Honest.K3.Good.Live (Clause clause_member next_behind calls_att)
open ProofFile.Honest.K3.Law (sites_shape_ok site_block site_facts memberAtSite drawsWork seatOf)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty site_hub border_digits)
open ProofFile.Honest.K5 (k5Marks k5Marks_head mkLive mkLive_held_own)
open H2K5.Honest (Reads HeldLive)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  {W Y : Type}
include h

omit h in
/-- A site's public parameters are the library's at its link and sort, and their shape is the
site's: the first four clauses of the lookups' authors' site_facts
(Johnson/Desc/ProofFile/Honest/K3/Law/MemberSite.lean) at a member of the list of sites. -/
theorem site_pars (s : Site) (hs : s ∈ lookSites Zp) :
    Look.placeAt Zp.p.X s.link s.digits = some s.p ∧ s.p.shape = some s.shape := by
  unfold lookSites at hs
  obtain ⟨y, -, hsy⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, f2, f3, f4, -⟩ := site_facts _ _ y s hsy
  rw [f3, f4]
  exact ⟨f1, f2⟩

/-- **AT EACH OF THE FIFTY LOOKUPS: BEHIND THE MEMBER's OWN STEP, WHERE NO MARK ASKED AT ITS PLACE
SPEAKS ON ITS OWN CHALLENGES: THE LOOKUPS' AUTHORS' CONDITION `Clause`
(Johnson/Desc/ProofFile/Honest/K3/Good/Live/Clause.lean) AT WHAT THE STATE HOLDS AS HEARD; AND THE
LEDGER's NEXT SLOT.** Where the lookups' marks and the fit's mark at that member are among the marks
asked. THEIR clause_member's PREMISE hc (the challenges are such as the lookup's rounds can draw) IS
PAID HERE FROM THE FIT's MARK: the member's rounds are the plan's entries (site_block,
memberAtSite), and the frame's test reads no work bit (drawsWork). -/
theorem clause_at_step (G₀ : ProofFile.Ground) (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 25)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[borderOf s.link s.digits]? = some blk)
    (ms : List Mark) (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    (hfit : (⟨blk.place,
      fun _ own => if drawsFit blk.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    {ft n : ℕ} {sj sk : TS} {R : List Fmt.RoundView} {c : List Desc.OpenedColumn}
    (g3 : blk.step ft sj R c = .ok (sk, n)) {fr : List Fmt.Drawn}
    (hsil : markOf ms blk.place fr (R.map (·.drawn)) = none) :
    Clause s.p ((seatOf _root_.K3Lot.ofForm s.digits).heard sk) ∧
      ∃ G, sk.fork? = some G ∧ G.next = s.p.first + Forest.elems s.shape := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  obtain ⟨hface, -⟩ := sites_shape_ok Zp s hs
  obtain ⟨Fm, hent, -, hrd, -⟩ :=
    site_block _ _ _ _ Fd Zp Bs base cF A B O s hs lot blk hb hbs m1 m2 m3
  obtain ⟨-, hmr, -, -, hst⟩ := memberAtSite _ _ _ _ Fd Zp Bs base cF A B O lot hb blk m1 m2
  have hsh := (site_pars s hs).2
  have hc : canDraw (K3.faceOf s.shape) (R.map (·.drawn)) = true := by
    have k := fit_at_silent blk hfit hsil
    rw [hmr, hrd, drawsWork _ _ _ hent, hface] at k
    exact k
  have hk3 : markK3 blk.place (K3.faceOf s.shape) ∈ ms := by
    rw [m2, hbs, ← hface]
    exact hsub _ (List.mem_flatMap.2 ⟨s, hs, List.mem_cons_self⟩)
  have hk : (markK3 blk.place (K3.faceOf s.shape)).test fr (R.map (·.drawn)) = none :=
    mark_silent hk3 (by
      show (markOf ms blk.place fr (R.map (·.drawn))).isSome = false
      rw [hsil]
      rfl)
  refine ⟨clause_member _ _ _ _ Fd Zp Bs base cF A B O s hs lot blk hb hbs m1 m2 m3 ft sj sk n R c
    g3 hsh _ fr hk hc, ?_⟩
  obtain ⟨G, hG, hn⟩ := next_behind Fm hsh ft sj sk n R c ((hst ft sj sk n R c).1 g3).1
  refine ⟨G, ?_, hn⟩
  unfold seatOf at hG
  split at hG <;> exact hG

set_option maxHeartbeats 4000000 in
/-- **AT THE TWELVE ATTENTION SEGMENTS, AT THE STATES THAT THE FRAME's FIELD hP' HANDS IN FRONT OF
THE BATCHING: THE THREE CONDITIONS THAT THE BATCHING's AUTHORS' BOUND FOR THE FALL OF THE FREE SLOTS
ASKS OF THE STATE** (the first three conjuncts of hQ in their k9_fallDebt_att_clauses): what the
state holds of the segment's own rounds (`HeldLive`, Johnson/Desc/K5/Honest/Law/LiveState.lean),
from a ledger whose next slot was Forest.elems a.fs; `Clause` at what the lookup on the calls has
heard; `Clause` at what the lookup on the digits has heard. Where the lookups' marks (`k3Marks`),
the marks of the segment's own kind (`k5Marks`) and the fit's marks at A's members are among the
marks asked and these have been silent. NO PREMISE ON WHAT THE ROUNDS CAN DRAW. -/
theorem attClauses_handed (G₀ : ProofFile.Ground) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {pC pD : Look.P}
    (hC : Look.placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC)
    (hD : Look.placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
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
    (hz : walk L ss fr a₀ = .ok z) (hv : z.ver = some s') :
    HeldLive a.own (Forest.elems a.fs) s' ∧ Clause pC s'.lookHeard? ∧
      Clause pD (s'.tl?.bind (·.heard)) := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  have n24 : ¬ 2 * g + 1 = 24 := by omega
  have inA : ∀ {i : ℕ} {d : Block TS ProofFile.Cl}, i < 14 * (2 * g + 1) + 9 → cF.blocksInOrder[i]? = some d →
      d ∈ A := by
    intro i d hi hd
    rw [hall, List.getElem?_append_left (by omega)] at hd
    exact List.mem_of_getElem? hd
  -- the two sites and their parameters
  obtain ⟨s, hs, el, hd, -, -⟩ := site_at_all_fifty h (2 * g + 1) (by omega) false
  obtain ⟨sD, hsD, elD, hdD, -, -⟩ := site_at_all_fifty h (2 * g + 1) (by omega) true
  obtain rfl : s.p = pC := by
    have k := (site_pars s hs).1
    rw [el, hd] at k
    exact Option.some.inj (k.symm.trans hC)
  obtain rfl : sD.p = pD := by
    have k := (site_pars sD hsD).1
    rw [elD, hdD] at k
    exact Option.some.inj (k.symm.trans hD)
  obtain ⟨hshC, hfirst⟩ := calls_att h.pubOne (Att.P.p4_of_public h.pubOne ea) ea hC
  have hshape : s.shape = a.fs :=
    Option.some.inj ((site_pars s hs).2.symm.trans hshC)
  -- the members
  have hbC : borderOf (2 * g + 1) false = 14 * (2 * g + 1) + 3 := by
    rw [border_calls, if_neg n24]
  have hbD : borderOf (2 * g + 1) true = 14 * (2 * g + 1) + 8 := by
    rw [border_digits, if_neg n24]
  have K := keeps_five h.scope h.reads O h.laid.planOk (l := 2 * g + 1) (by omega)
  obtain ⟨b4, f4, D4⟩ := K 0 (by omega)
  obtain ⟨b5, f5, -⟩ := K 1 (by omega)
  obtain ⟨b6, f6, -⟩ := K 2 (by omega)
  obtain ⟨b7, f7, -⟩ := K 3 (by omega)
  obtain ⟨b8, f8, -⟩ := K 4 (by omega)
  obtain ⟨blk₁, hb₁⟩ : ∃ blk₁, cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₁ := by
    have hlt : 14 * (2 * g + 1) + 3 < cF.blocksInOrder.length := by
      rw [hall, List.length_append]
      omega
    exact ⟨_, List.getElem?_eq_getElem hlt⟩
  -- the digits' lookup is the last member in front: its own step leads into the state handed
  obtain ⟨tj, tk, Rt, dt, q₂, q₃, e₂, e₃, -, g8, -, hs8, -, -, hf8⟩ :=
    mid_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 14 * (2 * g + 1) + 8) f8 ms hall hfit (by omega)
      hpos L hft hm ha hn hq hz hv
  rw [hA] at hf8
  obtain rfl : s' = tk := fold_window_end hf8
  have JD := (clause_at_step h G₀ sD hsD (by omega) (blk := b8) (by
    rw [elD, hdD, hbD]
    exact f8) ms hsub (hfit b8 (inA (by omega) f8)) g8 hs8).1
  rw [hdD] at JD
  -- the calls' lookup and the segment's own kind's step
  obtain ⟨sj, sk, sl, R₁, R₂, d₁, d₂, r₂, r₃, c₂, c₃, f₁, f₂, -, g3, -, hs1, -, k3, -, hs2, -, hrk,
    -, hfold⟩ := pair_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 14 * (2 * g + 1) + 3) hb₁ f4 ms
      hall hfit (by omega) hpos L hft hm ha hn hq hz hv
  rw [hA] at hfold
  obtain ⟨JC, G, hG, hnext⟩ := clause_at_step h G₀ s hs (by omega) (blk := blk₁) (by
    rw [el, hd, hbC]
    exact hb₁) ms hsub (hfit blk₁ (inA (by omega) hb₁)) g3 hs1
  rw [hd] at JC
  have d4 := ((Sound.step_ok_iff 0 b4 sk sl R₂ d₂ d₂.length).1 k3).2.2.2
  have keep : OnPublicFiles.KeepsLook sk s' :=
    (D4 sk _ _ sl d4).trans (look_rides cF.blocksInOrder (14 * (2 * g + 1) + 5) 4 (fun i hi => by
               have k := K (i + 1) (by omega)
               rwa [show 14 * (2 * g + 1) + 4 + (i + 1) = 14 * (2 * g + 1) + 5 + i by omega] at k) hfold)
  obtain ⟨s6, rs5, gs5, r5, c5, d5, h5⟩ :=
    fold_head (n := 14 * (2 * g + 1) + 5) f5 (by omega) hfold
  obtain ⟨s7, rs6, gs6, r6, c6, d6, h6⟩ :=
    fold_head (n := 14 * (2 * g + 1) + 6) f6 (by omega) h5
  obtain ⟨s8, rs7, gs7, r7, c7, d7, h7⟩ :=
    fold_head (n := 14 * (2 * g + 1) + 7) f7 (by omega) h6
  obtain ⟨s9, rs8, gs8, r8, c8, d8, h8⟩ :=
    fold_head (n := 14 * (2 * g + 1) + 8) f8 (by omega) h7
  obtain rfl : s' = s9 := fold_window_end h8
  -- the open segment behind the calls' lookup, its ledger's sizes and next slot
  obtain ⟨-, -, att, e4, -⟩ := H2K5.Honest.TlOpen.tl_behind_look h.scope h.reads O g hg (zp, sk) hrk
  obtain rfl : att.F = G := Option.some.inj ((Att.P.fork_front e4).symm.trans hG)
  obtain ⟨-, Rr, Cc, hf0⟩ := hrk.fold
  obtain ⟨G', hG', hz'⟩ := OnPublicFiles.sized_upTo h.scope h.reads O h.laid.planOk (2 * g + 1)
    (by omega) 1 (by omega)
    (show foldBlocks 0 (cF.blocksInOrder.take (14 * (2 * g + 1) + 1 + 2 + 1)) (ProofFile.startS Zp zp) Rr Cc =
      .ok (sk, [], []) from hf0)
  obtain rfl : att.F = G' := Option.some.inj (hG.symm.trans hG')
  -- that kind's second mark
  have hf := fit_at_silent b4 (hfit b4 (inA (by omega) f4)) hs2
  have hp4 : b4.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
    obtain ⟨Lk, b', bq, aq, e1, e2, _, e4', _⟩ := IM.k5_of h.scope h.reads O g hg
    have k := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (by omega : 2 * g + 1 ≤ 24) 2] at k
    obtain rfl : b' = b4 := Option.some.inj (k.symm.trans f4)
    exact IM.alone_place e4'
  have hsay : (mkLive (2 * g + 1) a.own).test f₂ (R₂.map (·.drawn)) = none :=
    mark_silent (hsubA _ (k5Marks_head h hB hg ea).2) (by
      show (markOf ms ⟨1, some (2 * g + 1), 3, .K5⟩ f₂ (R₂.map (·.drawn))).isSome = false
      rw [← hp4, hs2]
      rfl)
  have hc : Reads ⟨#[], R₂.map (·.drawn)⟩ (R₂.map noDigest) := by
    intro i r hr
    rw [List.getElem?_map] at hr
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
    show ((R₂.map (·.drawn))[i]?).map (·.elems) = some (noDigest r').drawn.elems
    rw [List.getElem?_map, hr']
    rfl
  have hI := mkLive_held_own h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 e4
    ((OnBytes.Tie.Pv.Att.sized_iff _).2 hz') #[] hc hf hsay
  rw [hnext, hfirst, hshape, Nat.zero_add] at hI
  obtain ⟨H, eH, JH⟩ := JC
  exact ⟨hI, ⟨H, keep H eH, JH⟩, JD⟩

end

end P1K8

#print axioms P1K8.site_pars
#print axioms P1K8.clause_at_step
#print axioms P1K8.attClauses_handed
