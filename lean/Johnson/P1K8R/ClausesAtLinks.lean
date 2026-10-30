-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ClausesAtLinks.lean: THE HONEST SIDE's FRAME, ALL 25 SEGMENTS: THE LOOKUPS' AUTHORS'
CONDITION `Clause` (Johnson/Desc/ProofFile/Honest/K3/Good/Live/Clause.lean), AT WHAT EACH OF A
SEGMENT's TWO LOOKUPS HAS HEARD, HOLDS AT THE STATES THAT THE FRAME's FIELD hP' HANDS IN FRONT OF
THE SEGMENT's BATCHING, FROM THE MARKS' SILENCE. TYPED ON THE BATCHING's AUTHORS' SECOND «YES».
Lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  **`looksClauses_handed`**   l < 24: `clause_at_step` (Johnson/P1K8R/ClausesAtFrame.lean) twice;
      `mid_handed` (MidStepAtWalk.lean) twice; `keeps_five`, `look_rides` (KeepsBetween.lean);
      `fold_window_end` (AttLiveAtFrame.lean). AT AN ATTENTION SEGMENT IT IS THE SECOND AND THIRD
      CONJUNCT OF `attClauses_handed` (ClausesAtFrame.lean): THAT PROOF's LINES ON THE TWO STAND
      HERE A SECOND TIME, at a free l, with `mid_handed` where that has `pair_handed`
  **`headClauses_handed`**   the like at 340, 345 and 347: `keeps_six` (KeepsBetween.lean);
      `fold_head` (AttLiveAtFrame.lean); `P1K8S.merge_leaves` (WideAtSeat.lean)
Kin. As under "Kin" in Johnson/P1K8R/ClausesAtFrame.lean. `looks_below_handed`, `looks_head_handed`
(Johnson/P1K8R/LooksAtFrame.lean): at the same states, from the same marks' silence at the digits'
lookup: two tests of the smallness test on what was heard, where this has the lookups' authors'
condition.
Limits. The head h is a hypothesis; the full size alone. That the walk returns, that its start obeys
the frame's law, that the lists named are among the marks asked and that these have been silent are
premises: what the silence costs is the marks' authors' matter. TWO CONDITIONS ON WHAT WAS HEARD,
AND NO MORE: what else the batching's authors' bound asks of the state at a feed-forward segment or
at the output head's is not spoken of; from the state's two readings to the fields of the open
segment's own part is theirs. THE OUTPUT HEAD's FORM IS TYPED AHEAD OF THEIRS, WHICH MAY ASK
OTHERWISE. Sufficient, not necessary.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.ClausesAtFrame
import Johnson.P1K8R.WideAtSeat

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

set_option maxHeartbeats 4000000 in
/-- **AT EVERY SEGMENT BUT THE OUTPUT HEAD's (l < 24), AT THE STATES THAT THE FRAME's FIELD hP'
HANDS IN FRONT OF THE BATCHING: THE LOOKUPS' AUTHORS' CONDITION `Clause` AT WHAT THE LOOKUP ON THE
CALLS HAS HEARD, AND AT WHAT THE LOOKUP ON THE DIGITS HAS HEARD.** Where the lookups' marks
(`k3Marks`) and the fit's marks at A's members are among the marks asked and these have been silent.
The digits' lookup is the last member in front of the batching: its own step leads into the state
handed; what the calls' lookup has heard is carried over the five members between. -/
theorem looksClauses_handed (G₀ : ProofFile.Ground) {l : ℕ} (hl : l < 24) {pC pD : Look.P}
    (hC : Look.placeAt (P5J.At.X Zp) l false = some pC)
    (hD : Look.placeAt (P5J.At.X Zp) l true = some pD)
    (ms : List Mark) (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * l + 9) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a₀ z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a₀ = .ok z) (hv : z.ver = some s') :
    Clause pC s'.lookHeard? ∧ Clause pD (s'.tl?.bind (·.heard)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have n24 : ¬ l = 24 := by omega
  have inA : ∀ {i : ℕ} {d : Block TS ProofFile.Cl}, i < 14 * l + 9 → cF.blocksInOrder[i]? = some d → d ∈ A := by
    intro i d hi hd
    rw [hall, List.getElem?_append_left (by omega)] at hd
    exact List.mem_of_getElem? hd
  obtain ⟨s, hs, el, hd, -, -⟩ := site_at_all_fifty h l (by omega) false
  obtain ⟨sD, hsD, elD, hdD, -, -⟩ := site_at_all_fifty h l (by omega) true
  obtain rfl : s.p = pC := by
    have k := (site_pars s hs).1
    rw [el, hd] at k
    exact Option.some.inj (k.symm.trans hC)
  obtain rfl : sD.p = pD := by
    have k := (site_pars sD hsD).1
    rw [elD, hdD] at k
    exact Option.some.inj (k.symm.trans hD)
  have hbC : borderOf l false = 14 * l + 3 := by
    rw [border_calls, if_neg n24]
  have hbD : borderOf l true = 14 * l + 8 := by
    rw [border_digits, if_neg n24]
  have K := keeps_five h.scope h.reads O h.laid.planOk (l := l) hl
  obtain ⟨b8, f8, -⟩ := K 4 (by omega)
  obtain ⟨blk₁, hb₁⟩ : ∃ blk₁, cF.blocksInOrder[14 * l + 3]? = some blk₁ := by
    have hlt : 14 * l + 3 < cF.blocksInOrder.length := by
      rw [hall, List.length_append]
      omega
    exact ⟨_, List.getElem?_eq_getElem hlt⟩
  -- the digits' lookup
  obtain ⟨tj, tk, Rt, dt, q₂, q₃, e₂, e₃, -, g8, -, hs8, -, -, hf8⟩ :=
    mid_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 14 * l + 8) f8 ms hall hfit (by omega)
      hpos L hft hm ha hn hq hz hv
  rw [hA] at hf8
  obtain rfl : s' = tk := fold_window_end hf8
  have JD := (clause_at_step h G₀ sD hsD (by omega) (blk := b8) (by
    rw [elD, hdD, hbD]
    exact f8) ms hsub (hfit b8 (inA (by omega) f8)) g8 hs8).1
  rw [hdD] at JD
  -- the calls' lookup
  obtain ⟨sj, sk, R₁, d₁, r₂, r₃, c₂, c₃, -, g3, -, hs1, -, -, hfold⟩ :=
    mid_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 14 * l + 3) hb₁ ms hall hfit (by omega)
      hpos L hft hm ha hn hq hz hv
  rw [hA] at hfold
  have JC := (clause_at_step h G₀ s hs (by omega) (blk := blk₁) (by
    rw [el, hd, hbC]
    exact hb₁) ms hsub (hfit blk₁ (inA (by omega) hb₁)) g3 hs1).1
  rw [hd] at JC
  have keep : OnPublicFiles.KeepsLook sk s' := look_rides cF.blocksInOrder (14 * l + 4) 5 K hfold
  obtain ⟨H, eH, JH⟩ := JC
  exact ⟨⟨H, keep H eH, JH⟩, JD⟩

set_option maxHeartbeats 4000000 in
/-- **AT THE OUTPUT HEAD's SEGMENT: THE SAME TWO, AT THE STATES THAT THE FIELD HANDS IN FRONT OF ITS
BATCHING (the member number 347).** The calls' lookup stands at 340: what it has heard is carried
over the six members between. The digits' lookup stands at 345; one member, the merge, stands
between it and the batching, and leaves the smallness test's data as they are (`P1K8S.merge_leaves`,
Johnson/P1K8R/WideAtSeat.lean). -/
theorem headClauses_handed (G₀ : ProofFile.Ground) {pC pD : Look.P}
    (hC : Look.placeAt (P5J.At.X Zp) 24 false = some pC)
    (hD : Look.placeAt (P5J.At.X Zp) 24 true = some pD)
    (ms : List Mark) (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 347) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a₀ z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a₀ = .ok z) (hv : z.ver = some s') :
    Clause pC s'.lookHeard? ∧ Clause pD (s'.tl?.bind (·.heard)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have inA : ∀ {i : ℕ} {d : Block TS ProofFile.Cl}, i < 347 → cF.blocksInOrder[i]? = some d → d ∈ A := by
    intro i d hi hd
    rw [hall, List.getElem?_append_left (by omega)] at hd
    exact List.mem_of_getElem? hd
  have at_ : ∀ i, i < 347 → ∃ d, cF.blocksInOrder[i]? = some d := by
    intro i hi
    have hlt : i < cF.blocksInOrder.length := by
      rw [hall, List.length_append]
      omega
    exact ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨s, hs, el, hd, -, -⟩ := site_at_all_fifty h 24 (by omega) false
  obtain ⟨sD, hsD, elD, hdD, -, -⟩ := site_at_all_fifty h 24 (by omega) true
  obtain rfl : s.p = pC := by
    have k := (site_pars s hs).1
    rw [el, hd] at k
    exact Option.some.inj (k.symm.trans hC)
  obtain rfl : sD.p = pD := by
    have k := (site_pars sD hsD).1
    rw [elD, hdD] at k
    exact Option.some.inj (k.symm.trans hD)
  have hbC : borderOf 24 false = 340 := by
    rw [border_calls, if_pos rfl]
  have hbD : borderOf 24 true = 345 := by
    rw [border_digits, if_pos rfl]
  obtain ⟨blk₁, hb₁⟩ := at_ 340 (by omega)
  obtain ⟨blk₂, hb₂⟩ := at_ 345 (by omega)
  obtain ⟨bm, hbm, hLv⟩ := P1K8S.merge_leaves h.scope h.reads O
  -- the digits' lookup, and the merge behind it
  obtain ⟨tj, tk, Rt, dt, q₂, q₃, e₂, e₃, -, g8, -, hs8, -, -, hf8⟩ :=
    mid_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 345) hb₂ ms hall hfit (by omega)
      hpos L hft hm ha hn hq hz hv
  rw [hA] at hf8
  obtain ⟨t₁, rsm, gsm, rm, cm, dm, hm'⟩ := fold_head (n := 346) hbm (by omega) hf8
  obtain rfl : s' = t₁ := fold_window_end hm'
  have etl : s'.tl? = tk.tl? := hLv _ _ _ _ dm
  have JD := (clause_at_step h G₀ sD hsD (by omega) (blk := blk₂) (by
    rw [elD, hdD, hbD]
    exact hb₂) ms hsub (hfit blk₂ (inA (by omega) hb₂)) g8 hs8).1
  rw [hdD] at JD
  -- the calls' lookup
  obtain ⟨sj, sk, R₁, d₁, r₂, r₃, c₂, c₃, -, g3, -, hs1, -, -, hfold⟩ :=
    mid_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 340) hb₁ ms hall hfit (by omega)
      hpos L hft hm ha hn hq hz hv
  rw [hA] at hfold
  have JC := (clause_at_step h G₀ s hs (by omega) (blk := blk₁) (by
    rw [el, hd, hbC]
    exact hb₁) ms hsub (hfit blk₁ (inA (by omega) hb₁)) g3 hs1).1
  rw [hd] at JC
  have keep : OnPublicFiles.KeepsLook sk s' :=
    look_rides cF.blocksInOrder 341 6 (keeps_six h.scope h.reads O h.laid.planOk) hfold
  obtain ⟨H, eH, JH⟩ := JC
  refine ⟨⟨H, keep H eH, JH⟩, ?_⟩
  rw [etl]
  exact JD

end

end P1K8

#print axioms P1K8.looksClauses_handed
#print axioms P1K8.headClauses_handed
