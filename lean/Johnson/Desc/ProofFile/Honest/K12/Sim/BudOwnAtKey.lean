-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudOwnAtKey.lean: Sim/BudOwnAtHead.lean at the key file. At
the first member of the proximity test on G_omega that the key file's description seats on its
shared chain, whose first fold sends its own fresh table: the side's bound on positions `testBud`
(Sim/Row.lean) holds at the positions that the description's own declared rounds read of that
table's tree, at every list of challenges that passes `Draws.due`
(Johnson/Desc/ProofFile/Honest/Frame.lean); and `MeetsAt` (Sim/MeetsOwnAtHead.lean) holds there, at
these positions and at that list's own stretch of challenges. The job is any `TestJob` at the seated
place whose first fold sends its own table. General in the source X of `Key.descriptionFromSource`, under two public
premises: the description passes its tests on the plan, and its declared rounds, written out, are
the library's written lists of a key file. It imports Mathlib.

The statement `bud_first_KO` has the text of the field `bud₂` of the record `BudDebts`, which goes
with the frame, at one row and one member, as `bud_first_O` (Sim/BudOwnAtHead.lean) has it. That
record's file does not lie beneath this one: nothing in Lean ties this statement to the record: it
is held against it by reading.

  `key_written`  in the goals' scope, where `protocolDataWellFormed` says yes: the declared rounds of the key
                 file's description, written out, are `dryKeyFull`
  `cut_KO`, `front_KO`   the shared list cut at the test's place; the rounds in front are 43 and
                 send 7 roots
  `told_KO`, `told_first_KO`   the seated place's first stated message has a tenant that is not
                 sampled (kernel)
  `open_KO`, `cnts_KO`   at the seated place `pKO`, by Lean's kernel: a round of the test that
                 samples 49 positions opens the chain's own tree number 7 at the depth 13; of the
                 first member's six rounds the second alone states a message
  `asks_KO`      at every due list of challenges the frame's list of the positions read of the
                 shared chain's tree number 7 has at most 49 members, each below 2 ^ 13
  `budFirst_KO`, `cnts_job_KO`, `pre_KO`, `bud_first_KO`   the bound: as a test with code; in the
                 record's letters
  `draws_stretch_KO`, `facts_stretch_KO`   the member's own stretch of a due list has the declared
                 form; so the nine public tests hold at the place and that stretch
  `meets_due_KO`   `MeetsAt` at the frame's own positions and the list's own stretch

By what. That no other round of the file's three chains opens that tree is the library's test
`BookPlan.once` (Johnson/Desc/BookPlan.lean), a clause of `FileDescription.planOk`: `asks_at_block`
(TreeInFront.lean), `asks_of_one` (ReadsOfTree.lean). The 7. At the proof file the place's number
"free" is tied to the roots declared in front by `plain_free`; at this place of the key file by
`free_210` (Johnson/RunOne/Law/K12PlaceAtName.lean), under seven premises of its own, the scope
among them. Here the count goes over the written lists, as in the proof of the library's
`rounds_at_key_O`: `keyDecl_atO`, `keySharedPreO_bats`, `keyPlan_O`
(Johnson/Loose/H2K12/RoundsAtKeySeats.lean), `seat_rounds`, `pre_length_closed`, `roots_closed`
(Johnson/Loose/H2K12/WrittenAtSeats.lean), `chains_of_written`
(Johnson/Desc/K12/Law/WrittenOfDecl.lean), `bat_KOFull`, `roots_KOFull`
(Johnson/Desc/K12/Law/StretchKeyFull.lean). `key_written`: `theLive_made`
(Johnson/Goal/Description/Live.lean), `laid_bind_seat` (Johnson/Desc/Key/PinnedAtO.lean),
`seat_in_scope_key` (Johnson/Goal/Numbers/PlanWrittenDescScope.lean). The cut: `keyShared_cut_omega`
(Johnson/Desc/K12/Law/SitsKeyChains.lean), `cut_at_place`. From Sim/BudOwnAtHead.lean, called as
they are: `different_le`, `front_count`, `draws_front`. `MeetsAt`: `own_at_place`
(Sim/OwnAnyAtPlace.lean), which is general in the list of challenges.

Limits.
- 49 of 146: the bound is met with room. Nothing says that it could not be met with fewer random
  values, or that the equation fails beyond it.
- It speaks of the fold's own tree, number 7. The tree that this test and the test on G_u both open
  is another one; nothing is said of it here.
- One list of challenges: one request. Nothing on the positions that several requests read.
- `treeAsks` is computed of the declared rounds and the challenges: that a run asks for no position
  beyond that list is the frame's own law, not shown here.
- Nothing here shows that any list of challenges is due.
- The front is `bareFront chain m`, made of the stand, not the frame's front.
- The first member alone: `testBud` at the second member is not treated.
- "At every job at the place" says nothing on whether any job there is the prover's. This file's
  writer knows of no written job of the key file at this place. The state on entry is any function.
- The written lists are what a print of the planner showed (the limits of RoundsAtKeySeats.lean).
- All limits of Sim/KeyHead.lean and Sim/OwnAnyAtPlace.lean stand, but the latter's on positions
  that the frame lays.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudOwnAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.KeyPlaceFactsOwn
import Johnson.Loose.H2K12.RoundsAtKeySeats
import Johnson.Desc.Key.PinnedAtO

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference
open VerifiableInference.Desc (Block Oracle Key.descriptionFromSource)
open VerifiableInference.Desc
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open _root_.Desc.K14 (St)
open H2K.JointK (laidOf pGomega keyOmega keyGu keySharedPre keySharedEnd)
open Johnson.G.OfPlan (rootsOf)
open Johnson.KB8 (rangesNumsFull laterPlacesFull oT o_typed)

variable {V W X' Pb : Type}

/-! ## 1 The declared rounds, written out -/

/-- **In the goals' scope, where `protocolDataWellFormed` says yes**: the declared rounds of the key file's
description, written out, are the library's written lists. X₀ and X: as `key_head`
(Sim/KeyHead.lean) has them. -/
theorem key_written (Z : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (X₀ : OnBytes.Model.Verify.Public)
    (X : Key.Source)
    (h0 : PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀)
    (h4 : Key.descAt X₀ Z.lay Key.fixedDigest = .ok (Key.descriptionFromSource X rangesNumsFull laterPlacesFull)) :
    Johnson.G.OfPlan.writtenOf "key file" (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).roundsDeclaredByBlocks =
      .ok Johnson.G.dryKeyFull := by
  obtain ⟨K, _, _, hK, _, _⟩ := FlashProve.theLive_made (VerifierAndGoals.asDescriptionFiles Z) hL
  obtain ⟨D, r⟩ := K
  have hK' : (PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay)).bind
      (fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay) = .ok (D, r) := hK
  obtain ⟨X₁, F, a1, a2, a3, _, _⟩ := Key.laid_bind_seat hK'
  obtain rfl : X₁ = X₀ := Except.ok.inj (a1.symm.trans h0)
  obtain rfl : F = (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) := Except.ok.inj (a2.symm.trans h4)
  exact (PlanWritten.seat_in_scope_key _ _ Z hS a3).1

/-! ## 2 The place in the list -/

section Desc
variable (X : Key.Source)

/-- The library's cut of the shared list at the test's place. -/
theorem cut_KO : (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder =
    (keySharedPre X.chains laterPlacesFull ++ [keyGu laterPlacesFull]) ++
      keyOmega oT :: [keySharedEnd X.chains laterPlacesFull] :=
  H2K.JointK.keyShared_cut_omega X.chains laterPlacesFull oT o_typed

variable (hp : (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).planOk = true)
  (hW : Johnson.G.OfPlan.writtenOf "key file" (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).roundsDeclaredByBlocks =
    .ok Johnson.G.dryKeyFull)

include hp hW in
/-- **The rounds in front of the test are 43 and send 7 roots.** -/
theorem front_KO :
    ((keySharedPre X.chains laterPlacesFull ++ [keyGu laterPlacesFull]).flatMap
        (·.rounds)).length = 43 ∧
      rootsOf ((keySharedPre X.chains laterPlacesFull ++ [keyGu laterPlacesFull]).flatMap
        (·.rounds)) = 7 := by
  obtain ⟨_, r, R', er, hr⟩ := H2K.JointK.seat_rounds ⟨2, none, 10, .K12⟩ oT
    (H2K.JointK.keyPlan_O X rangesNumsFull laterPlacesFull hp oT o_typed)
  have hx := (H2K.Pub.chains_of_written hW).2.1
  rw [H2K.JointK.keyDecl_atO X rangesNumsFull laterPlacesFull oT o_typed] at hx
  have hl : ((keySharedPre X.chains laterPlacesFull ++ [keyGu laterPlacesFull]).flatMap
      (·.rounds)).length = 43 := by
    have hx' := hx
    rw [show (proximityTestKind guardedProximityTestParts (pGomega oT) : Block T12 Unit).rounds = r :: R' from er] at hx'
    exact H2K.JointK.pre_length_closed hx' hr
      (H2K.JointK.keySharedPreO_bats X rangesNumsFull laterPlacesFull hp) H2K.Member.bat_KOFull
  refine ⟨hl, ?_⟩
  rw [H2K.JointK.roots_closed hx, hl]
  exact H2K.Member.roots_KOFull

/-! ## 3 At the seated place, by the kernel -/

omit X in
theorem told_KO :
    ((pKO.oracles.flatMap id).head?.map fun T => T.tenants.all (·.sampled)) = some false := by
  decide +kernel

omit X in
/-- The seated place's first stated message has a tenant that is not sampled. -/
theorem told_first_KO : ∃ (T : Oracle) (rest : List Oracle),
    pKO.oracles.flatMap id = T :: rest ∧ T.tenants.all (·.sampled) = false := by
  have h := told_KO
  cases hl : pKO.oracles.flatMap id with
  | nil =>
    rw [hl] at h
    cases h
  | cons T rest =>
    rw [hl] at h
    exact ⟨T, rest, rfl, Option.some.inj h⟩

omit X in
theorem open_KO : (H2U.roundsOfNums pKO.nums).map
    (fun l => decide (((1, 7), 49, 13) ∈ openedOf 1 l)) = some true := by
  decide +kernel

omit X in
theorem cnts_KO : ((laidOf pKO).take (firstLen pKO.nums.stages)).map (·.2.length) =
    [0, 1, 0, 0, 0, 0] := by
  decide +kernel

/-! ## 4 The positions read of the fold's own tree -/

include hp hW in
/-- **At every due list of challenges.** -/
theorem asks_KO (ρ : Draws) (hρ : ρ.due (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) = true) :
    (treeAsks (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ρ 1 7).length ≤ 49 ∧
      ∀ x ∈ treeAsks (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ρ 1 7, x < 2 ^ 13 := by
  obtain ⟨T, rest, hT, hs⟩ := told_first_KO
  have h7 := (front_KO X hp hW).2
  have hT' : (keyOmega oT).oracles.flatMap id = T :: rest := by
    show (proximityTestKind guardedProximityTestParts pKO : Block T12 Unit).oracles.flatMap id = _
    rw [VerifiableInference.Desc.K12.k12_oracles guardedProximityTestParts pKO plan_KO]
    exact hT
  have he : ((1, rootsOf ((keySharedPre X.chains laterPlacesFull ++ [keyGu laterPlacesFull]).flatMap
      (·.rounds))), 49, 13) ∈ openedOf 1 (keyOmega oT).rounds := by
    have ho := open_KO
    rw [VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts pKO plan_KO] at ho
    rw [h7]
    exact of_decide_eq_true (Option.some.inj ho)
  have key : (treeAsks (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ρ 1
      (rootsOf ((keySharedPre X.chains laterPlacesFull ++ [keyGu laterPlacesFull]).flatMap
        (·.rounds)))).length ≤ 49 ∧
      ∀ x ∈ treeAsks (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ρ 1
        (rootsOf ((keySharedPre X.chains laterPlacesFull ++ [keyGu laterPlacesFull]).flatMap
          (·.rounds))), x < 2 ^ 13 :=
    asks_at_block hp _ _ (keyOmega oT) (cut_KO X) T rest hT' hs 49 13 he ρ hρ
  rw [h7] at key
  exact key

include hp hW in
/-- The bound as a test with code, at the positions that the declared rounds read. -/
theorem budFirst_KO (Js : SimJob Pb) (hJ : Js.p = pKO) (ρ : Draws)
    (hρ : ρ.due (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) = true) :
    budFirst Js.s₀ (asksFrom (treeAsks (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ρ 1)
      [0, 1, 0, 0, 0, 0] 7) = true := by
  obtain ⟨a1, a2⟩ := asks_KO X hp hW ρ hρ
  have e : Js.s₀ = pKO.nums.stages.headD default := by
    show Js.p.nums.stages.headD default = _
    rw [hJ]
  obtain ⟨_, _, n3, n4, _⟩ := stage_KO
  show ((treeAsks (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ρ 1 7).all
      (fun x => decide (x < 2 ^ Js.s₀.Z.a)) &&
    decide (different (treeAsks (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ρ 1 7) ≤
      Js.s₀.Z.r)) = true
  rw [e, n3, n4, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun x hx => decide_eq_true (a2 x hx),
    Nat.le_trans (different_le _) (Nat.le_trans a1 (by decide))⟩

/-! ## 5 The bound, in the record's letters -/

section Job
variable (Js : SimJob Pb) (J : TestJob W X') (hJp : J.p = pKO)

omit X in
include hJp in
theorem cnts_job_KO :
    (firstMember (V := V) J Js).rounds.map (·.2.length) = [0, 1, 0, 0, 0, 0] := by
  show ((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.2.length) = _
  rw [hJp]
  exact cnts_KO

include hJp in
/-- Whatever side `testSide` takes off the shared list, a cut of the list at its block is the
library's. -/
theorem pre_KO (hp : (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).planOk = true)
    (fs : List (Fall St)) (σ : Side St Key.Claim V W X' Pb)
    (hσ : testSide (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder J Js fs = some σ)
    (pre t : List (Block St Key.Claim))
    (hcut : (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder = pre ++ σ.block :: t) :
    pre = (keySharedPre X.chains laterPlacesFull ++ [keyGu laterPlacesFull]) := by
  have hbp : σ.block.place = pKO.place := by
    have hσ' := hσ
    unfold testSide Side.seated at hσ'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ'
    have := beq_iff_eq.1
      (List.find?_some (p := fun b : Block St Key.Claim => b.place == J.p.place) hb)
    rw [hJp] at this
    exact this
  have hpl : (keyOmega oT).place = pKO.place :=
    (H2K.JointK.keyOmega_place oT).trans (H2K.JointK.place_of_p12At _ _).symm
  exact cut_at_place hp pre _ t _ σ.block (keyOmega oT) hcut (cut_KO X) (hbp.trans hpl.symm)

include hp hW hJp in
/-- **`testBud` at the first member, at the positions that the description's declared rounds read,
at every due list of challenges.** n: the rounds of the shared chain in front of the member. -/
theorem bud_first_KO (hJ : Js.p = pKO) (fs : List (Fall St)) (σ : Side St Key.Claim V W X' Pb)
    (hσ : testSide (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder J Js fs = some σ)
    (pre t : List (Block St Key.Claim)) (n : ℕ)
    (hcut : (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder = pre ++ σ.block :: t)
    (hn : n = (pre.flatMap (·.rounds)).length +
      ((σ.row.take (firstMember (V := V) J Js).number).map fun x => x.1.moves.length).sum)
    (ρ : Draws) (hρ : ρ.due (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) = true) :
    testBud Js (firstMember (V := V) J Js).number
      ((ρ.shared.drop n).take (firstMember (V := V) J Js).rounds.length)
      (asksFrom (treeAsks (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ρ 1)
        ((firstMember (V := V) J Js).rounds.map (·.2.length))
        (((rowsOfChain (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder).take n).map
          (·.2.length)).sum) := by
  have hpp := pre_KO X Js J hJp hp fs σ hσ pre t hcut
  subst hpp
  have hn' : n = ((keySharedPre X.chains laterPlacesFull ++ [keyGu laterPlacesFull]).flatMap
      (·.rounds)).length := hn
  have hN : (((rowsOfChain (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder).take n).map
      (·.2.length)).sum = 7 :=
    front_count hp _ t σ.block hcut n 7 hn' (front_KO X hp hW).2
  rw [hN, cnts_job_KO (V := V) Js J hJp]
  exact testBud_own Js _ _ (budFirst_KO X hp hW Js hJ ρ hρ)

/-! ## 6 The list's own stretch of challenges; `MeetsAt` -/

include hJp in
/-- The member's own stretch of a due list has the declared form. -/
theorem draws_stretch_KO (hp : (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).planOk = true)
    (b : Block St Key.Claim) (pre t : List (Block St Key.Claim))
    (hcut : (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder = pre ++ b :: t)
    (hr : b.rounds = (proximityTestKind guardedProximityTestParts pKO : Block T12 Unit).rounds)
    (hor : b.oracles = (proximityTestKind guardedProximityTestParts pKO : Block T12 Unit).oracles) (ρ : Draws)
    (hρ : ρ.due (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) = true) :
    drawsFit ((firstMember (V := V) J Js).rounds.map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
        (firstMember (V := V) J Js).rounds.length) = true := by
  have hm : (firstMember (V := V) J Js).rounds =
      (laidOf pKO).take (firstLen pKO.nums.stages) := by
    show (laidOf J.p).take (firstLen J.p.nums.stages) = _
    rw [hJp]
  rw [hm]
  have hl : (proximityTestKind guardedProximityTestParts pKO : Block T12 Unit).rounds.length ≤
      (proximityTestKind guardedProximityTestParts pKO : Block T12 Unit).oracles.length := by
    have hs := shaped_len b (planOk_shaped hp b
      (by rw [hcut]; exact List.mem_append_right _ List.mem_cons_self))
    rw [hr, hor] at hs
    exact Nat.le_of_eq hs.symm
  have hz : b.rounds = (laidOf pKO).map (·.1) := by
    rw [hr, ← zip_laid pKO plan_KO, List.map_fst_zip hl]
  have hsplit : b.rounds = ((laidOf pKO).take (firstLen pKO.nums.stages)).map (·.1) ++
      ((laidOf pKO).drop (firstLen pKO.nums.stages)).map (·.1) := by
    rw [hz, ← List.map_append, List.take_append_drop]
  have h4 := draws_front pre t b hcut _ _ hsplit ρ hρ
  rw [List.length_map] at h4
  exact h4

omit X in
/-- The nine public tests at the seated place and any list of challenges of the declared form. -/
theorem facts_stretch_KO (ds : List Fmt.Drawn)
    (hd : drawsFit (((laidOf pKO).take (firstLen pKO.nums.stages)).map (·.1)) ds = true) :
    PlaceFactsOwn pKO ds :=
  ⟨plan_KO, form_KO, enough_KO, tab_KO, points_KO, count_KO, quiet_KO, hd, by
    rw [ProofFile.Honest.drawsFit_length _ _ hd, List.length_map, List.length_take]
    exact Nat.min_eq_left enough_KO⟩

include hp hW hJp in
/-- **`MeetsAt` at the positions that the description's declared rounds read and at the list's own
stretch of challenges, at every due list.** -/
theorem meets_due_KO (hfr : J.fresh.isNone = true) (hJ : Js.p = pKO) (ho : Js.own = true)
    (fs : List (Fall St)) (σ : Side St Key.Claim V W X' Pb)
    (hσ : testSide (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder J Js fs = some σ)
    (pre t : List (Block St Key.Claim)) (n : ℕ)
    (hcut : (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder = pre ++ σ.block :: t)
    (hn : n = (pre.flatMap (·.rounds)).length +
      ((σ.row.take (firstMember (V := V) J Js).number).map fun x => x.1.moves.length).sum)
    (ρ : Draws) (hρ : ρ.due (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) = true) (φ : Face V W Pb)
    (chain firstTree : ℕ) (ca : CsAll (firstMember (V := V) J Js).part.carries)
    (m : ProofFile.Honest.Mid W X') :
    MeetsAt φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js) ca m
      (bareFront chain m) ((ρ.shared.drop n).take (firstMember (V := V) J Js).rounds.length)
      (asksFrom (treeAsks (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ρ 1)
        ((firstMember (V := V) J Js).rounds.map (·.2.length))
        (((rowsOfChain (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder).take n).map
          (·.2.length)).sum) := by
  obtain ⟨b, hf₀, hpl, hr, hor⟩ := seat_KO X rangesNumsFull laterPlacesFull oT o_typed
  have hf : ((Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder.find? fun b =>
      b.place == pKO.place) = some b := hf₀
  have hσb : σ.block = b := by
    have hσ' := hσ
    unfold testSide Side.seated at hσ'
    rw [hJp, hf] at hσ'
    obtain rfl := Option.some.inj hσ'
    rfl
  have hn' : n = (pre.flatMap (·.rounds)).length := hn
  have hd := draws_stretch_KO (V := V) X Js J hJp hp σ.block pre t hcut (hσb ▸ hr) (hσb ▸ hor) ρ hρ
  rw [← hn'] at hd
  have hpp := pre_KO X Js J hJp hp fs σ hσ pre t hcut
  have hN : (((rowsOfChain (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).shared.blocksInOrder).take n).map
      (·.2.length)).sum = 7 :=
    front_count hp pre t σ.block hcut n 7 hn' (hpp ▸ (front_KO X hp hW).2)
  rw [hN, cnts_job_KO (V := V) Js J hJp]
  have hF : PlaceFactsOwn J.p
      ((ρ.shared.drop n).take (firstMember (V := V) J Js).rounds.length) := by
    rw [hJp]
    refine facts_stretch_KO _ ?_
    have hd' := hd
    rw [show (firstMember (V := V) J Js).rounds.map (·.1) =
      ((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) from rfl, hJp] at hd'
    exact hd'
  exact (own_at_place (V := V) J Js hF _ b (by rw [hJp]; exact hf) (by rw [hJp]; exact hpl)
    (by rw [hJp]; exact hr) (by rw [hJp]; exact hor) hfr (hJ.trans hJp.symm) ho).2.2 fs σ hσ
    |>.2.2.2.2 φ chain firstTree ca m _ (budFirst_KO X hp hW Js hJ ρ hρ)

end Job

end Desc

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.key_written
#print axioms ProofFile.Honest.K12.Light.cut_KO
#print axioms ProofFile.Honest.K12.Light.front_KO
#print axioms ProofFile.Honest.K12.Light.told_KO
#print axioms ProofFile.Honest.K12.Light.told_first_KO
#print axioms ProofFile.Honest.K12.Light.open_KO
#print axioms ProofFile.Honest.K12.Light.cnts_KO
#print axioms ProofFile.Honest.K12.Light.asks_KO
#print axioms ProofFile.Honest.K12.Light.budFirst_KO
#print axioms ProofFile.Honest.K12.Light.cnts_job_KO
#print axioms ProofFile.Honest.K12.Light.pre_KO
#print axioms ProofFile.Honest.K12.Light.bud_first_KO
#print axioms ProofFile.Honest.K12.Light.draws_stretch_KO
#print axioms ProofFile.Honest.K12.Light.facts_stretch_KO
#print axioms ProofFile.Honest.K12.Light.meets_due_KO
