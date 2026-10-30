-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.ChainAtGu
import Johnson.Loose.H2K12.CondAtLast
import Johnson.Desc.K12.Law.Sizes.LastAtScope
import Johnson.Desc.K12.Law.Sizes.ClosedAtScope
import Johnson.Desc.Ok.PlanWritten.LastOfPinned
/-
Johnson/Loose/H2K12/ChainAtLast.lean: "the chain at the first chain's last test": the proximity test
(the kind K12) at ⟨1, none, 2, .K12⟩, at the full size, at every three public files in the goals'
scope, from `proofDataAndDecisionOfPublicFiles`'s return AND ONE NAMED PREMISE. It is H2K12/ChainAtGu.lean and
H2K12/ChainAtGomega.lean [not in this library], carried to the first chain's seat, over
H2K12/CondAtLast.lean.

THE NAMED PREMISE, which stands bare in front of every top here: `LastIsTyped o S`: at what
`pubPlain` returns at S's three files, the record's stages of the last test are the typed list
(CondAtLast.lean's hL). It has two payers, and neither is whole:
  `lastIsTyped_of_pinned`: FROM A TEST WITH CODE ON PUBLIC DATA: `sizedPinnedAt`
    (Johnson/Desc/Ok/PlanWritten/SizedTest.lean) says yes at the scan and at what
    the planner configured. In scope the scan's key is the full size's (`key_of_pubPlain`): so the
    stages are the typed list: `last_of_pinnedAt` (Johnson/Desc/Ok/PlanWritten/LastOfPinned.lean):
    what the planner sized for the proof file is the written value, whole, and the
    written value's last test has the typed stages (`last_written`,
    Johnson/Desc/K12/Law/Sizes/WrittenIsTyped.lean: by the kernel). THAT THE LAID VALUE ASKS THIS
    TEST IS NOT SO: `proofDataAndDecisionOfPublicFiles`'s list of tests has no such row.

    (Where this and lean/THEOREM.md differ, the page holds.)
  `lastIsTyped_of_groups`: from the closed sentence `H2K.Sizes.LayoutGroupsAre`
    (Johnson/Desc/K12/Law/Sizes/LastAtScope.lean), in scope: it is proved in the side library:
    AtFullSide/LayoutRead/GroupsPaid.lean.
Main names:
  `stages_of_pubPlain`, `key_of_pubPlain`, `LastIsTyped` and its two payers.
  `chain_L`: `placesOfMade` lays the last test's place on chain 1.
  `labels_LFull`: at the closed place the test `ownLabelsFreeB` says yes: by the kernel.
  `PublicAtLast Z N pre`: the public half: pre declares 48,237 rounds of the written list; `ClosedL
    (pL N) rLFull 0 0 0 TLFull`; `rLFull` is the planner's radius at each stage; no own mask; the
    first free own number is the roots that pre's rounds declare; `ownLabelsFreeB`; `RoundsHoldAt`
    at the planner's radii.
  `public_at_seat_L`: it, under CondAtLast.lean's premises.
  `CondAtLast Z N`: the condition at `pL N`, the planner's radii, the codes of the record behind the
    door, and 2^-128.
  `chain_at_Last_run`: from `VerifierAndGoals.InScope S`, `LastIsTyped o S` and `LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol
    S.lay S.KL = .ok (D, r)`: there are Z, N, c, the cut's letters pre, l, J and the way out leave,
    each pinned, with `PublicAtLast`, `FirstOut` and "the entry sits", such that at every yes of the
    laid decision r the description's run returns, and `AtCutWith` holds at the seat with `PubAt`
    and `CondAtLast` at one pair of records.
Whose: the cut's letters: `k12_sits`; "the entry sits": `firstJ_sits`; `AtCut`: `run_atCut1`
(H2K12/SitsAtDescPure.lean, FirstSeatForm.lean, Johnson/Desc/K12/Law/Sits.lean); `atCut_pub`,
`PubAt`, `runEnd_of_run`: ChainAtGu.lean; `ClosedL.of_reads` and its like:
Law/Sizes/ClosedAtScope.lean; `closed_LFull`: Johnson/Desc/K12/Coin/LawAtFull.lean; `laidPOf_ok`,
`asks_written`: Johnson/Desc/Laid/.
What it is not: a conjunction of a law's public premises and a run's facts at one place: not a bound
on anything that the file's game counts. The condition is one premise of the kind's lemma; this file
does not call that lemma. 48,237 and 77 are facts of the written list, which is what a print
showed; the written sizes and the typed stages were laid by programs from prints of one planner: no
second witness. One round's share each, no sum; 20 of the 128 bits are work at "CS" and "BASE";
"BAT": its number is priced; its list's law is not shown. No member: nothing shows that `proofDataAndDecisionOfPublicFiles`
returns at any files in scope. Nothing on soundness of a verifier. Nothing on hiding.

-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (ClosedL ownLabelsFreeB)
open VerifiableInference.Desc.K12.Coin.At (TLFull closed_LFull)
open H2K.Member (piLFull rLFull)
open H2K.Pub (Letters radBy sgOf pubOk)
open OnBytes.Slice
open OnBytes.Maker (WholeD)
open Johnson.G (dryProofFull)
open scoped ENNReal

/-- **Under the closed premise, in scope**: the record's stages of the last test are the typed
list, at the plain road's public part. -/
theorem stages_of_pubPlain (hG : H2K.Sizes.LayoutGroupsAre) {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) :
    Z.made.p.chains.made.sized.proof.last.stages = H2K.Member.szLFull :=
  H2K.Sizes.last_of_plain hS
    (by rw [(Johnson.G.ScopeLines.inScope_files hS).2]; exact hG)
    (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts S.pol S.lay S.KL = .ok Z from hZ)))

/-- **THE NAMED PREMISE AT THIS SEAT**: at what `pubPlain` returns at S's three files the record's
stages of the last test are the typed list. -/
def LastIsTyped (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ Z, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z →
    Z.made.p.chains.made.sized.proof.last.stages = H2K.Member.szLFull

/-- In scope, on the plain road, the scan's key is the full size's. -/
theorem key_of_pubPlain {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    {Z : ProofFile.Pub} (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) :
    VerifiableInference.PlanWritten.keyOfScan Z.made.p.X.P =
        VerifiableInference.PlanWritten.fullKey := by
  obtain ⟨_, _, _, _, _, _, _, hX, _⟩ := H2K.Made.plain_parts (ProofFile.Law.madeOf_planned
    (ProofFile.Law.pubBy_made
      (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts S.pol S.lay S.KL = .ok Z from hZ)))
  exact VerifiableInference.PlanWritten.scan_key_in_scope hS
    (OnBytes.Model.Verify.polLayout_scan
        (VerifiableInference.PlanWritten.publicSteps_of_O hX).layout)

/-- Its payer by the test with code, in scope. That the laid value asks the test is not shown. -/
theorem lastIsTyped_of_pinned {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true)
    (h : ∀ Z, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z →
      VerifiableInference.PlanWritten.sizedPinnedAt Z.made.p.X.P Z.made.p.chains.made = true) :
    LastIsTyped o S :=
  fun Z hZ => VerifiableInference.PlanWritten.last_of_pinnedAt (h Z hZ) (key_of_pubPlain hS hZ)

/-- Its payer by the closed sentence on the layout file (proved in AtFullSide/LayoutRead/). -/
theorem lastIsTyped_of_groups (hG : H2K.Sizes.LayoutGroupsAre) {o : ProofFile.SecondHashFunctionArgument}
    {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true) : LastIsTyped o S :=
  fun _ hZ => stages_of_pubPlain hG hS hZ

/-- `placesOfMade` lays the last test's place on chain 1. -/
theorem chain_L (m : Johnson.G.OfPlan.Made) (X : H2U.Places4)
    (h : H2U.placesOfMade m = .ok X) : X.L.chain = 1 := by
  unfold H2U.placesOfMade at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          rfl

/-- At the closed place every opening of the first switch is the chain's own tree, in front of the
test, under its own label. -/
theorem labels_LFull : ownLabelsFreeB piLFull = true := by decide +kernel

/-- The public half at the first chain's seat. Its last clause and `ClosedL`'s chain and "BAT" say
"below" of one chain at two names of one radius, tied by the third clause: two forms for two
spenders. The fourth, fifth and sixth are what the law at the file's own piece asks on the plan. -/
def PublicAtLast (Z : ProofFile.Pub) (N : H2U.Places4) (pre : List (Block First.S ProofFile.Cl)) : Prop :=
  (pre.flatMap (·.rounds)).length = 48237 ∧
  ClosedL (pL N) rLFull 0 0 0 TLFull ∧
  (∀ a ∈ N.L.nums.stages,
      (radBy Z.made.p.chains.made.sized.proof.set Z.made.p.chains.made.sized.proof.last.stages)
      (sgOf a) = rLFull a) ∧
  (pL N).nums.ownMask = false ∧
  (pL N).nums.free = Johnson.G.OfPlan.rootsOf (pre.flatMap (·.rounds)) ∧
  ownLabelsFreeB (pL N) = true ∧
  H2K.Pub.RoundsHoldAt (pL N)
    (radBy Z.made.p.chains.made.sized.proof.set
      Z.made.p.chains.made.sized.proof.last.stages) ((2 : ℝ≥0∞)⁻¹ ^ 128)

/-- **The public half**, under the premises of CondAtLast.lean. -/
theorem public_at_seat_L (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (A : H2K.Sizes.AtFull Z.made.p.chains.made)
    (hL : Z.made.p.chains.made.sized.proof.last.stages = H2K.Member.szLFull)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull)
    (same : First.S → First.S → Bool) (pre l : List (Block First.S ProofFile.Cl))
    (J : Block First.S ProofFile.Cl)
    (hb : c.blocksInOrder = pre ++ firstEntry same J :: l) (hJ : FirstJ (pL N) J) :
    PublicAtLast Z N pre := by
  have pk := plan_at_seat_L o Z mk N c hp same pre l J hb hJ
  have hn : (pL N).nums = N.L.nums := H2K.Made.nums_of_planOk a12 N.L pk
  obtain ⟨hx, _, hl, hf⟩ :=
    stretch_at_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  obtain ⟨e1, _, e3⟩ := H2K.Sizes.place_L_of_full A hN hL
  have hR := rounds_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  have hWr := written_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  have h1 := rows_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  have h5 : N.L.nums.free = piLFull.nums.free := hf
  have h6 : N.L.nums.firstTree = piLFull.nums.firstTree :=
    (H2K.Made.places_firstTree Z.made N hN).1
  have hc : (pL N).place.chain = piLFull.place.chain :=
    (H2K.Sizes.chain_of_planOk a12 N.L pk).trans (chain_L Z.made N hN)
  have hD := H2K.Sizes.rdsAt_reads pk closed_LFull.plan (by rw [hn]; exact hR)
  refine ⟨hl, ?_, e3, ?_, ?_, ?_,
    roundsHold_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ⟩
  · exact H2K.Sizes.ClosedL.of_reads pk (by rw [hn]; exact e1) (by rw [hn]; exact hWr)
      (by rw [hn]; exact hR) (by rw [hn]; exact h1) (by rw [hn]; exact h5) hc closed_LFull.light
  · rw [hn]
    exact H2K.Member.places_ownL Z.made N hN
  · rw [hn, hf, roots_closed hx, hl]
    exact H2K.Member.roots_front_LFull.symm
  · rw [H2K.Sizes.ownLabelsFreeB_reads pk closed_LFull.plan (by rw [hn]; exact e1) hD
      (by rw [hn]; exact h6) (by rw [hn]; exact h5)]
    exact labels_LFull

/-- The condition at the first chain's seat, at the codes of the record behind the door in. -/
def CondAtLast (Z : ProofFile.Pub) (N : H2U.Places4) {T : Type} : T → T12 → Prop :=
  fun _ t0 => H2K.Pub.K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (radBy Z.made.p.chains.made.sized.proof.set
      Z.made.p.chains.made.sized.proof.last.stages)
    (pL N) t0.st.codes ((2 : ℝ≥0∞)⁻¹ ^ 128)

/-- **The chain at the first chain's last test, at the laid decision itself**: the named premise
stands bare in front. The way out `leave` and "the entry sits" stand in front of every run. -/
theorem chain_at_Last_run (X : Letters) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (hT : LastIsTyped o S) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N c pre l J leave, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).data "proof file" = .ok D ∧
      c.blocksInOrder = pre ++ firstEntry ProofFile.sameReply J :: l ∧ PublicAtLast Z N pre ∧
      FirstOut ProofFile.sameReply (pL N) J leave ∧
      Sits (firstEntry ProofFile.sameReply J) (proximityTestKind guardedProximityTestParts (pL N) : Blk') enterFinish leave ∧
      ∀ z (v₁ v₂ v₃ : Fmt.View), r z v₁ v₂ v₃ = true →
        ∃ e, (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).runEnd (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ =
            .ok e ∧
          AtCutWith X (pL N) 0 pre (firstEntry ProofFile.sameReply J) l enterFinish leave
            ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).start₁
              ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pub (LPFD.Full.instanceAsPlainRecord z))) e.1
            (withEmptySealRound v₁) fun m t0 => PubAt (pL N) m t0 ∧ CondAtLast Z N m t0 := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, e, _, pre, l, J, hb, _, hJ⟩ := k12_sits o S.pol S.lay S.KL F hF
  subst e
  subst hr
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hLs := hT Z hZ
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1
  have pk := plan_at_seat_L o Z _ N c hp ProofFile.sameReply pre l J hb hJ
  obtain ⟨leave, hout, hsit⟩ := firstJ_sits ProofFile.sameReply (pL N) J hJ
  refine ⟨Z, N, c, pre, l, J, leave, hZ, hN, hF, hD, hb,
    public_at_seat_L o S.pol S.lay S.KL Z hZ _ N c hN hp A hLs hW ProofFile.sameReply pre l J hb hJ,
    hout, hsit, fun z v₁ v₂ v₃ hy => ?_⟩
  obtain ⟨e, he⟩ := runEnd_of_run _ (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃
    ((FileDescription.pull_run LPFD.Full.instanceAsPlainRecord _ z v₁ v₂ v₃).symm.trans hy)
  have ha := run_atCut1 X (pL N) (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c)
    (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ e he pre _ l _ _ hb hsit
  exact ⟨e, he, (atCut_pub pk ha).mono fun m t0 hf =>
    ⟨hf, k12Condition_at_seat_L o S.pol S.lay S.KL Z hZ _ N c hN hp A hLs hW ProofFile.sameReply pre l J
      hb hJ t0.st.codes hf.2⟩⟩

end H2K.JointK

#print axioms H2K.JointK.stages_of_pubPlain
#print axioms H2K.JointK.key_of_pubPlain
#print axioms H2K.JointK.lastIsTyped_of_pinned
#print axioms H2K.JointK.lastIsTyped_of_groups
#print axioms H2K.JointK.labels_LFull
#print axioms H2K.JointK.public_at_seat_L
#print axioms H2K.JointK.chain_at_Last_run
