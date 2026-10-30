-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/ZeroKnowledgeAtTheProtocolLaws.lean: ZeroKnowledgeOnServedRequests from its run-by-run premises.

1.  In scope some request is served, in range: the online lines are not idle. So that field is discharged here.
2.  The whole view at the protocol's budget gives the claim at the life of one commitment, up to 710,324 further tables with
    688,127 requests each.
3.  So the statement follows from: simulators with which the provers are honest-verifier zero knowledge. That is not proved
    in this file.
4.  And that follows from EIGHT named premises: the work bits are the three verifiers' own, the provers speak of their tables,
    each of the three has a simulator that is exact outside its private stops, and each one's stops have the stated measure. Two of
    the structure's fields read no prover: two indices in range (proved here) and that the work bits are the verifiers' own (workFaithful_atFiles,
    E2E/CompleteAsIOPWorkBits.lean; it is completeness's conjunct too).
-/
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocol
import E2E.CompleteAsIOPServedLaws
import Johnson.T3.WholeViewFollows
import E2E.ObjectGuards
import Johnson.T3.AtHome
import VerifiableInference.Final.RefuseUnserved

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles readFiles InScope)
open FlashProve (committerCoinCountLessOne)

/-- **In scope some request is served, in range.** -/
theorem someRequestIsServed_holds (Z : PublicFiles) (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) : ∃ i x, rangeAtFiles i ∧ ServedRequest committerCoinCountLessOne Z hr i x := by
  obtain ⟨i, x, h⟩ := servedRequest_met (b := committerCoinCountLessOne) (Z := Z) scope hr
  refine ⟨i, x, ?_, h⟩
  obtain ⟨w, -, -, hi, -⟩ := h
  rw [hi]
  exact OnBytes.FrontRoad.inRange_backThe Z _ w

/-- **The whole view at the protocol's budget gives the claim at the life of one commitment.** -/
theorem wholeLife_atFiles {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp} {Hs : HonestProvers (protocolAtFiles Z)}
    {a b c : ℝ≥0∞} {simulators : RunSimulators (protocolAtFiles Z)}
    (h : WholeView (workAtFiles Z) (proversAtFiles Z hr Hs) simulators rangeAtFiles
      (ServedRequest committerCoinCountLessOne Z hr) (budgetAtFiles a b c))
    (copyNumber : ℕ → ℕ) (copies sessionsPerCopy : ℕ) (hc : copies ≤ 710324)
    (hs : sessionsPerCopy ≤ 688127) :
    WholeLife (workAtFiles Z) (proversAtFiles Z hr Hs) simulators rangeAtFiles
      (ServedRequest committerCoinCountLessOne Z hr) (budgetAtFiles a b c) copyNumber copies sessionsPerCopy :=
  wholeLife_of_wholeView h copyNumber copies sessionsPerCopy
    (by show 62 + copies * 62 ≤ 44040191; omega)
    (by show 62 + sessionsPerCopy * 64 ≤ 44040191; omega)

/-- **The statement follows from its first part.** -/
theorem zeroKnowledgeOnServedRequests_of {Z : PublicFiles} (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    {hr : readFiles Z = .ok pp} {Hs : HonestProvers (protocolAtFiles Z)} {a b c : ℝ≥0∞} (simulators : RunSimulators (protocolAtFiles Z))
    (two : TwoIndicesServeOneRequest Z hr)
    (h : HonestVerifierZeroKnowledge (workAtFiles Z) (proversAtFiles Z hr Hs) simulators rangeAtFiles
      (ServedRequest committerCoinCountLessOne Z hr) (budgetAtFiles a b c)) :
    ZeroKnowledgeOnServedRequests Z hr Hs a b c where
  someRequestIsServed := someRequestIsServed_holds Z scope hr
  twoIndicesServeOneRequest := two
  simulated := ⟨simulators, h, fun copyNumber copies s hc hs =>
    wholeLife_atFiles h.wholeView copyNumber copies s hc hs⟩

/-- **Every oracle of the three proofs is blinded**: the view shows no oracle whole. -/
theorem allBlinded_atFiles (Z : PublicFiles) :
    (∀ p, (protocolAtFiles Z).offline.blinded p = true) ∧ (∀ p, (protocolAtFiles Z).link.blinded p = true) ∧
      ∀ p, (protocolAtFiles Z).onlineBatch.loc.blinded p = true :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- **The protocol is the object in the input of the soundness theorem's own description**, at every digest and further reading. -/
theorem protocol_of_the_description (Z : PublicFiles) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    objectOf ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) = ⟨FullSizeMatrix, LPFD.Full.XF, protocolAtFiles Z⟩ :=
  object_description Z c m

/-- The range has two indices. -/
theorem twoIndices_atFiles : ∃ i i' : FullSizeMatrix, i ≠ i' ∧ rangeAtFiles i ∧ rangeAtFiles i' :=
  Exists.elim ix_two fun i h => Exists.elim h fun i' hne =>
    ⟨i.1, i'.1, fun e => hne (Subtype.ext e), i.2, i'.2⟩

/-- **FROM EIGHT PREMISES.** For public files in scope the statement at the protocol follows from eight things: the work bits are the three
verifiers' own; the provers speak of their tables; each of the three provers has a simulator that is exact outside its private
stops; each one's stops have the stated measure. -/
theorem zeroKnowledgeOnServedRequests_of_runs {Z : PublicFiles} (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    {hr : readFiles Z = .ok pp} {Hs : HonestProvers (protocolAtFiles Z)} {a b c : ℝ≥0∞} (simulators : RunSimulators (protocolAtFiles Z))
    (faithful : (workAtFiles Z).Faithful) (two : TwoIndicesServeOneRequest Z hr)
    (tables : Hs.SpeakOfTheirTables)
    (offline : ExactOutsideStops Hs.offlineProver
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline.cleared simulators.offline)
    (link : ExactOutsideStops Hs.linkProver
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validL w y) (workAtFiles Z).link.cleared simulators.link)
    (online : ∀ n, ExactOutsideStops (Hs.onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online.cleared (simulators.online n))
    (offlineStops : PrivateStopsAtMost Hs.offlineProver
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline a)
    (linkStops : PrivateStopsAtMost Hs.linkProver
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validL w y) (workAtFiles Z).link b)
    (onlineStops : ∀ n, PrivateStopsAtMost (Hs.onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online c) :
    ZeroKnowledgeOnServedRequests Z hr Hs a b c :=
  have hRun : RunByRun (workAtFiles Z) (proversAtFiles Z hr Hs) simulators rangeAtFiles
      (ServedRequest committerCoinCountLessOne Z hr) (budgetAtFiles a b c) :=
    refuseUnserved_runByRun (workAtFiles Z) Hs simulators rangeAtFiles
      (ServedRequest committerCoinCountLessOne Z hr) (budgetAtFiles a b c) tables offline link online offlineStops
      linkStops onlineStops
  have hReads : Hiop.Seeded.ReadsG (protocolAtFiles Z) (fun _ => True) (budgetAtFiles a b c).columns
      (budgetAtFiles a b c).offlineReads (budgetAtFiles a b c).linkReadsFirst
      (budgetAtFiles a b c).linkReadsCopy (budgetAtFiles a b c).onlineReads :=
    AtPublicFiles.Premises.readsG_atFiles Z scope _
  zeroKnowledgeOnServedRequests_of scope simulators two
    { twoIndices := twoIndices_atFiles
      faithful := faithful
      runByRun := hRun
      wholeView := wholeViewFollows _ _ _ _ _ _ hReads hRun }

/-- **One prover.** Completeness is stated of Hs, zero knowledge of Hs made to refuse what is not served: completeness holds of the one
exactly if it holds of the other. -/
theorem completeOnServedRequests_refuse_iff (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) (Hs : HonestProvers (protocolAtFiles Z)) :
    CompleteOnServedRequests Z hr (proversAtFiles Z hr Hs) ↔ CompleteOnServedRequests Z hr Hs := by
  unfold CompleteOnServedRequests CompleteIOP
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨a, b, c, h, hc⟩
    exact ⟨a, b, c, h, (completeInParts_refuse_iff (L := protocolAtFiles Z) (provers := Hs) _ _ _ _ _).1 hc⟩
  · rintro ⟨a, b, c, h, hc⟩
    exact ⟨a, b, c, h, (completeInParts_refuse_iff (L := protocolAtFiles Z) (provers := Hs) _ _ _ _ _).2 hc⟩

/-- **FROM SIX PREMISES.** Where the link's prover and simulator are the explicit ones, six of the eight are premises, and the link's error
is 0. -/
theorem zeroKnowledgeOnServedRequests_of_runs_link {Z : PublicFiles} (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    {hr : readFiles Z = .ok pp} {Hs : HonestProvers (protocolAtFiles Z)} {a c : ℝ≥0∞} (simulators : RunSimulators (protocolAtFiles Z))
    (hLink : Hs.linkProver = linkProverAtFiles committerCoinCountLessOne Z) (hSim : simulators.link = OnBytes.LinkSim.AtHome.homeSim Z)
    (faithful : (workAtFiles Z).Faithful) (two : TwoIndicesServeOneRequest Z hr)
    (tables : Hs.SpeakOfTheirTables)
    (offline : ExactOutsideStops Hs.offlineProver
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline.cleared simulators.offline)
    (online : ∀ n, ExactOutsideStops (Hs.onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online.cleared (simulators.online n))
    (offlineStops : PrivateStopsAtMost Hs.offlineProver
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline a)
    (onlineStops : ∀ n, PrivateStopsAtMost (Hs.onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online c) :
    ZeroKnowledgeOnServedRequests Z hr Hs a 0 c := by
  have hp : Hs.linkProver = OnBytes.LinkSim.AtHome.explicitLinkProver committerCoinCountLessOne Z := hLink
  have h2 := OnBytes.LinkSim.AtHome.home_runByRun_link committerCoinCountLessOne Z rangeAtFiles
    Hs simulators (workAtFiles Z) hp hSim
  exact zeroKnowledgeOnServedRequests_of_runs scope simulators faithful two tables offline h2.1 online
    offlineStops h2.2 onlineStops

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.someRequestIsServed_holds
#print axioms VerifiableInference.Compilation.wholeLife_atFiles
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_of
#print axioms VerifiableInference.Compilation.twoIndices_atFiles
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_of_runs
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_of_runs_link
#print axioms VerifiableInference.Compilation.completeOnServedRequests_refuse_iff
#print axioms VerifiableInference.Compilation.allBlinded_atFiles
#print axioms VerifiableInference.Compilation.protocol_of_the_description
