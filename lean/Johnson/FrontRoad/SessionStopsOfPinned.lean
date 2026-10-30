-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SessionStopsOfPinned.lean: an implication whose conclusion is the condition
HidSmall (E2E/BridgePrivacy.lean) at the family famG (E2E/BridgeJoinAtFiles.lean), at the planner's
bound: at every tied request of Yes, the set of the verifier's messages at which the sessions'
prover aborts privately has measure at most the bound (sessionStops_of_pinned). Its premises: public
conditions; two conditions on the rows and the prover; that the rows are pinned (RowsPinned); that
the planner's test passes at the pinned places' checks; and that at every tied request of Yes the
cells of the input's trace pass cellsSmall at the pinned places. cells is free; the values that par
names are free; l, oneTime, columnsFirst and batches are free: tied to nothing here.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  sessionStops_of_pinned   sessionStops_at_files (Johnson/FrontRoad/SessionStopsAtFiles.lean) with
      its premises on the parts replaced: PartsHeld by partsHeld_of_pinned and partsHeld_of_silent,
      the two sums by sharesSum_of_pinned, sharesSum_of_silent
      (Johnson/FrontRoad/SessionStopsPinned.lean) and shares_le_planner
      (Johnson/FrontRoad/SharesLePlanner.lean). The bound is the planner's, 2 ^ −(sec + the
      rounded-up logarithms of the slots, the batches and the copies), plus 0 for the second chain.
      The pin is asked at the first chain without its last member, at par, and at the second chain
      at the par that names none. In the shared chain no private abort test is asked, by type.
  kindFits_dropLast   at public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: the
      first chain's data fit the rounds of its members without the last. By kindFits_first
      (Johnson/Desc/ProofFile/Honest/Law/CoverData.lean), with file_head and cut_exists
      (Johnson/Desc/ProofFile/Honest/Law/CoverHeadFile.lean) and seal_cut
      (Johnson/Desc/ProofFile/Honest/Law/CoverCut.lean): the chain's last member has one round.

How it fits. It concludes HidSmall at every range ok and every set Gs of OOD seeds; at Gs := fun _
=> True that is the field sessionStops of PremWDebts (E2E/BridgeDebts.lean), with the bound + 0 as
its number (as premWDebts_stops, Johnson/FrontRoad/SessionStopsAtFiles.lean, proves of
sessionStops_at_files). That field is one premise of the implication on index privacy
(Johnson/FrontRoad/FromDebtsSpec.lean); that implication is not concluded here. The measure is
HidSmall's own: over the verifier's messages of a session; the index, the stored tables' pads and
encoding randomness, the OOD seed and the instance are bound by "for all". The private abort test of
the smallness test reads the input's trace alone, and the trace is a function of the index and the
instance (Prover.trace, Johnson/Desc/ProofFile/Honest/Frame.lean): so, at every prover of this
frame's type, the cells are fixed before the matrix is drawn, whatever H.trace and cells are.
Whether a prover program fills these matrices so is outside Lean. Words (member, half, part, public
and private abort test, stated share): Johnson/FrontRoad/SessionStopsPinned.lean. Glue and
arithmetic; not one of the release's goal statements.

Limits.
  No parameters are known at which its premises hold together. No value is given for the bound.
  The one premise that reads the hidden input at every request is hP; hR is asked at one input and
      one run's coins, any that the caller names. hP says that the cells which the reader cells
      yields of the trace that H.trace returns pass cellsSmall. Nothing here proves it.
  Asked by no premise here, and proved by nothing here: that the input's trace is theTrace
      (Johnson/HonestTrace/FullPlanes.lean) at the input's own index and instance; that the list P.2
      which par names at a place (the parameter mats of smallLot,
      Johnson/Desc/ProofFile/Honest/K8/Part.lean) is the list of the matrices that the description's
      test covers there, by owner, label and first column; that what the other kinds' parts send is
      read off the same reader.
  That any prover's rows are pinned is not proved here; nor that every other part has a private
      abort test that never fires and states a share of the value 0. Rows without a half at a
      member's place at which par names parameters are shut out by the pin (no_half_not_pinned,
      Johnson/FrontRoad/SessionStopsPinnedTests.lean). A par that names none at the place of a
      member of the kind K8 is shut out too (unnamed_not_pinned, in that file): so at every member
      of the kind K8 of the first chain without its last member a half stands with the one part. The
      pin does not see the last member. The library finds the members of the smallness test by that
      kind (drawIxs, Johnson/Desc/First/K8/PlanDoor.lean). The pin at the second chain, at the par
      that names none, also says that the second chain has no member of the kind K8. By inspection,
      not proved: the definitions under Johnson/Desc that write that kind into a place write the
      chain number 1 with it. Among them are the kind's own sub-protocol (hear,
      Johnson/Desc/First/K8/Hear.lean) and the first chain's driver (addresses at kindsBeforeBatching,
      Johnson/Desc/First/Driver/Chain.lean), which writes its place into each member (blockAt) and
      gives the chain's last member the kind frame (firstChainWithoutReplyGuard). That a half stands at every member
      whose rounds send something (lacking … = [], Johnson/Desc/ProofFile/Honest/Frame.lean) is not
      asked here either.
  The values that par names are free: the pin holds P.1 against a member by the number of entries
      that the round draws alone, and P.2 by its length alone
      (Johnson/FrontRoad/SessionStopsPinned.lean, Limits). That par names the description's own
      parameters, and none at a member of another kind, is not asked here.
  l, oneTime, columnsFirst and batches are free. That they are those of Z's public files, that the
      checks are those that the verifier gives the planner, and that public files in scope pass the
      planner's test at them are not proved here. At sec = 0 with at most one slot, one batch and
      one copy the bound is 1, and the conclusion then holds of every prover; nothing here shuts
      that choice out.
  The premise on the planner's test fails where no place has parameters. There the sum of the stated
      shares is 0 (sharesSum_of_pinned), and sessionStops_at_files applies at 0; no theorem here
      states that case.
  It is vacuous at rows that always abort publicly, at a reader that yields zeros alone, and where
      no tied request of Yes has a trace. All limits of Johnson/FrontRoad/SessionStopsAtFiles.lean,
      Johnson/FrontRoad/SessionStopsPinned.lean and Johnson/FrontRoad/SharesLePlanner.lean hold.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.SessionStopsAtFiles
import Johnson.FrontRoad.SessionStopsPinned
import Johnson.FrontRoad.SharesLePlanner
import Johnson.Desc.ProofFile.Honest.Law.CoverData
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadFile

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Params (Lines missedInTheChecks clog2)
open OnBytes.Maker (RDT WholeD)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Local Face Cells KindFits Ready Coins ready kindFits_first
  seal_cut cut_exists file_head)
open ProofFile.Honest.K8 (windowShare)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_ofPinned : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_ofPinned {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

/-- At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: the first chain's data
fit the rounds of its members without the last. -/
theorem kindFits_dropLast (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    List.Forall₂ KindFits (dataZ Z).ds₁
      ((descZ Zp Np cF).first.blocksInOrder.dropLast.flatMap (·.rounds)) := by
  obtain rfl := data_atFiles Z Zp Np cF scope live L
  obtain ⟨hd, -, hcut⟩ :=
    file_head (AtMg.of_olderK scope hr L (atPlanOk_of_laid Z Zp Np cF scope live hr L))
  obtain ⟨pre, e₁, cut, -⟩ := cut_exists hcut
  obtain ⟨z, he⟩ := seal_cut hcut cut
  have h := kindFits_first hd cut he
  rw [dropLast_of_cut cut] at h
  exact h

variable {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **An implication: HidSmall at famG, and so the field sessionStops of PremWDebts, at the
planner's bound**, from public conditions, two conditions on the rows and the prover, the pin on the
rows, the planner's test at the pinned places' checks, and the premise hP that at every tied request
of Yes the cells of the input's trace pass cellsSmall at the pinned places. cells is free; the
values that par names are free; l, oneTime, columnsFirst and batches are free: tied to nothing here.
Asked by no premise here, and proved by nothing here: that the input's trace is theTrace
(Johnson/HonestTrace/FullPlanes.lean) at the input's own index and instance; that the list P.2 which
par names at a place (the parameter mats of smallLot, Johnson/Desc/ProofFile/Honest/K8/Part.lean) is
the list of the matrices that the description's test covers there, by owner, label and first column;
that what the other kinds' parts send is read off the same reader. The one premise that reads the
hidden input at every request is hP; hR is asked at one input and one run's coins, any that the
caller names. No parameters are known at which its premises hold together; no value is given for the
bound; that any prover's rows are pinned is not proved here. The measure is over the verifier's
messages; the bound is asked at every index and every value of the stored tables' pads and encoding
randomness. It is vacuous at rows that always abort publicly, at a reader that yields zeros alone,
where no tied request of Yes has a trace, and at sec = 0 with at most one slot, one batch and one
copy, where the bound is 1. Rows without a half at a member's place with parameters are shut out by
the pin; so is a par that names none at the place of a member of the kind K8. The pin is asked at
the first chain without its last member: it does not see that member. That a half stands at every
member whose rounds send something (lacking … = []) is not asked. The premise h₃ also says that the
second chain has no member of the kind K8. -/
theorem sessionStops_of_pinned (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : ProofFile.Inst} {k : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr → Cells) (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par cells (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) cells (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (hP : ∀ n w a, TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a) →
      ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr →
        CellsSmallAt par cells (descZ Zp Np cF).first.blocksInOrder.dropLast
          ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_at_files Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes
    (CellsSmallAt par cells (descZ Zp Np cF).first.blocksInOrder.dropLast) _ 0 hP
    (partsHeld_of_pinned par cells h₁ (kindFits_dropLast Z Zp Np cF scope hr live L) _
      fun _ h => h)
    ((sharesSum_of_pinned par cells h₁ _).trans (by
      have g := shares_le_planner l _ oneTime columnsFirst batches hm
      rw [List.map_map] at g
      exact g))
    (partsHeld_of_silent cells h₃ _) (sharesSum_of_silent cells h₃ _) ok Gs

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_ofPinned
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_ofPinned
#print axioms OnBytes.FrontRoad.kindFits_dropLast
#print axioms OnBytes.FrontRoad.sessionStops_of_pinned
