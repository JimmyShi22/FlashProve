-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/FileShare.lean: THE FILE's OWN SHARE OF THE TESTS ON THE PLAN, AT THE PLANNER's
CHAINS: **OkD.AtC.front2 c = true ∧ OkD.AtC.beside X c = true** (Johnson/Desc/OnPlan/OkFrontC.lean,
OkBesideC.lean: 28 conjuncts), FROM HYPOTHESES BY FIELD. They are the two premises that
Johnson/AtFull/Desc/SharedShare.lean leaves (hFront · hBeside). Statements with their proofs.

What the 28 read. Of c.made: sized.proof; proof (the three made plans). Of c.proof (what is read
back): shared.lin · shared.codes · shared.given.plan · second.given.plan · of first.given.plan the
entries and the samples · first.shape. Of X: X.P.frame, and, through subproofsWith X alone, the
plans' rounds.

  finishHeld_holds · finishHeld_set   what Params.finishHeld returns holds; its setting is the one
                      handed in.
  The conjuncts, one lemma each, by kind:
    closed at the written values (proofSizedFull · proofThree), by Lean's kernel, once the fields
    are rewritten: stagesU stagesO stagesW n1 n2 n3 n4 n5 n6 n8 n9 ahead firstU firstO firstW frontS
    sealS sizedS readSamples;
    by the hypotheses themselves: readShape readCodes readPlans settingZ;
    a planner run anew: remadeF (e₁) · remadeS remadeW (the library's proof_shared_written,
    proof_second_written: Johnson/Desc/Ok/NumberPrices/ProofLaterListed.lean);
    by the make: heldS madeSets.
  file_share          **the two.**
  bend_stage          [Lean's kernel] a closed test can fail.
  bend_samples · bend_seal   [Lean's kernel] NO NEGATIVE TESTS: each lays a number into its own
                      statement and compares it (2 with 1; 1 with 0): it holds whatever the plan is.
NOT PAID HERE: the eleven hypotheses.
Limits. No soundness is claimed. No example of the head is shown in this file; two, at storedPublicFiles and at
zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they
are worth.

-/
import Johnson.Desc.Ok.NumberPrices.ProofLaterListed
import Johnson.Desc.OnPlan.OkBesideC
import Johnson.Desc.OnPlan.OkFrontC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Number.ByRuns VerifiableInference.PlanWritten
open VerifiableInference.OnPublicFiles.OkD

/-! ## What finishHeld returns -/

theorem finishHeld_holds {s : Setting} {scope : Scope} {x : Planning Unit} {p : Planned}
    (h : finishHeld s scope x = .ok p) : p.holds = true := by
  unfold finishHeld at h
  cases e : finish s scope x with
  | error w =>
    rw [e] at h
    cases h
  | ok q =>
    rw [e] at h
    have h' : (if q.holds = true then (Except.ok q : Except String Planned)
      else .error notAdmitted) = .ok p := h
    split at h'
    · rename_i hq
      obtain rfl := Except.ok.inj h'
      exact hq
    · cases h'

theorem finishHeld_set {s : Setting} {scope : Scope} {x : Planning Unit} {p : Planned}
    (h : finishHeld s scope x = .ok p) : p.set = s := by
  unfold finishHeld at h
  cases e : finish s scope x with
  | error w =>
    rw [e] at h
    cases h
  | ok q =>
    rw [e] at h
    have h' : (if q.holds = true then (Except.ok q : Except String Planned)
      else .error notAdmitted) = .ok p := h
    split at h'
    · obtain rfl := Except.ok.inj h'
      unfold finish at e
      split at e
      · cases e
      · split at e
        · cases e
        · rw [← Except.ok.inj e]
    · cases h'

/-! ## The conjuncts -/

section
variable {X : Verify.Public} {c : Verify.Chains} {first : Planned}
  (hz : c.made.sized.proof = proofSizedFull)
  (hm : c.made.proof = [first, proofThree.B.plan, proofThree.C.plan])
  (e₁ : firstPlan proofSizedFull (Verify.subproofsWith X proofSizedFull.request.link) = .ok first)
  (r₁ : c.proof.first.given.plan.entries = first.plan.entries)
  (r₂ : c.proof.shared.given.plan = proofThree.B.plan.plan)
  (r₃ : c.proof.second.given.plan = proofThree.C.plan.plan)
  (r₄ : c.proof.shared.lin = proofSizedFull.batch.shape)
  (r₅ : c.proof.shared.codes = proofSizedFull.codes)
  (r₆ : c.proof.first.given.plan.samples = first.plan.samples)
  (r₇ : c.proof.first.shape = proofSizedFull.request)
  (hs : proofSizedFull.set = settingOf X.P.frame)

include r₂ r₄ r₅ in
theorem stagesU_w : AtC.stagesU c = true := by
  unfold AtC.stagesU AtC.codesS AtC.linS
  rw [r₂, r₄, r₅]
  decide +kernel

include r₂ r₄ r₅ in
theorem stagesO_w : AtC.stagesO c = true := by
  unfold AtC.stagesO AtC.codesS AtC.linS
  rw [r₂, r₄, r₅]
  decide +kernel

include r₃ r₄ r₅ in
theorem stagesW_w : AtC.stagesW c = true := by
  unfold AtC.stagesW AtC.codesS AtC.linS
  rw [r₃, r₄, r₅]
  decide +kernel

include r₄ in
theorem n8_w : AtC.n8 c = true := by
  show (!c.proof.shared.lin.testOwn.isEmpty) = true
  rw [r₄]
  decide +kernel

include e₁ r₆ in
theorem n1_w : AtC.n1 c = true := by
  show (c.proof.first.given.plan.samples == 1) = true
  have h1 : first.plan.samples = proofSizedFull.set.samples :=
    congrArg (·.samples) (finishHeld_set e₁)
  rw [r₆, h1]
  decide +kernel

include r₇ in
theorem n2_w : AtC.n2 c = true := by
  show c.proof.first.shape.choice.masksRide = true
  rw [r₇]
  decide +kernel

include r₇ in
theorem n9_w : AtC.n9 c = true := by
  show (!c.proof.first.shape.link.isEmpty) = true
  rw [r₇]
  decide +kernel

include hz e₁ r₁ in
theorem remadeF_w : AtC.remadeF X c = true := by
  unfold AtC.remadeF
  simp only [hz, e₁, r₁, decide_true]

include r₃ in
theorem n4_w : AtC.n4 c = true := by
  show (c.proof.second.given.plan.samples == 1) = true
  rw [r₃]
  decide +kernel

include hz r₃ in
theorem remadeW_w : AtC.remadeW c = true := by
  unfold AtC.remadeW
  simp only [hz, proof_second_written, r₃, decide_true]

include r₄ in
theorem n5_w : AtC.n5 c = true := by
  show c.proof.shared.lin.choice.masksRide = true
  rw [r₄]
  decide +kernel

include r₄ in
theorem n6_w : AtC.n6 c = true := by
  show (!c.proof.shared.lin.ownSplitNeeded) = true
  rw [r₄]
  decide +kernel

include r₄ in
theorem ahead_w : AtC.ahead c = true := by
  unfold AtC.ahead AtC.linS
  rw [r₄]
  decide +kernel

include r₄ in
theorem firstU_w : AtC.firstU c = true := by
  unfold AtC.firstU AtC.linS
  rw [r₄]
  decide +kernel

include r₄ in
theorem firstO_w : AtC.firstO c = true := by
  unfold AtC.firstO AtC.linS
  rw [r₄]
  decide +kernel

include r₄ in
theorem firstW_w : AtC.firstW c = true := by
  unfold AtC.firstW AtC.linS
  rw [r₄]
  decide +kernel

include hm e₁ in
theorem heldS_w : AtC.heldS c = true := by
  unfold AtC.heldS
  rw [hm]
  have h1 : first.holds = true := finishHeld_holds e₁
  have h2 : proofThree.B.plan.holds = true := finishHeld_holds proof_shared_written
  have h3 : proofThree.C.plan.holds = true := finishHeld_holds proof_second_written
  simp only [List.all_cons, List.all_nil, h1, h2, h3, Bool.and_self]

include hm r₁ r₂ r₃ in
theorem readPlans_w : AtC.readPlans c = true := by
  unfold AtC.readPlans
  rw [hm, r₁, r₂, r₃]
  simp only [List.map_cons, List.map_nil, decide_true]

include hz hs in
theorem settingZ_w : AtC.settingZ X c = true := by
  unfold AtC.settingZ
  rw [hz, hs]
  simp only [decide_true]

include hz hm e₁ in
theorem madeSets_w : AtC.madeSets c = true := by
  unfold AtC.madeSets
  rw [hm, hz]
  have h1 : first.set = proofSizedFull.set := finishHeld_set e₁
  have h2 : proofThree.B.plan.set = proofSizedFull.set := finishHeld_set proof_shared_written
  have h3 : proofThree.C.plan.set = proofSizedFull.set := finishHeld_set proof_second_written
  simp only [List.all_cons, List.all_nil, h1, h2, h3, decide_true, Bool.and_self]

include r₂ r₄ r₅ in
theorem frontS_w : AtC.frontS c = true := by
  unfold AtC.frontS AtC.frontWant AtC.sentU AtC.sentO AtC.proofWu AtC.codesS AtC.linS Given.rounds
  show _ = true
  simp only [AtC.proofTail, Proof.tailPublic, Proof.TailPublic.lin, r₂, r₄, r₅]
  decide +kernel

include r₂ in
theorem sealS_w : AtC.sealS c = true := by
  unfold AtC.sealS Given.rounds
  rw [r₂]
  decide +kernel

include r₂ in
theorem n3_w : AtC.n3 c = true := by
  show (c.proof.shared.given.plan.samples == 1) = true
  rw [r₂]
  decide +kernel

include hz in
theorem sizedS_w : AtC.sizedS c = true := by
  unfold AtC.sizedS
  rw [hz]
  decide +kernel

include hz r₄ in
theorem readShape_w : AtC.readShape c = true := by
  unfold AtC.readShape
  rw [hz, r₄]
  simp only [decide_true]

include hz r₅ in
theorem readCodes_w : AtC.readCodes c = true := by
  unfold AtC.readCodes
  rw [hz, r₅]
  simp only [decide_true]

include hz r₂ in
theorem readSamples_w : AtC.readSamples c = true := by
  unfold AtC.readSamples
  rw [hz, r₂]
  decide +kernel

include hz r₂ in
theorem remadeS_w : AtC.remadeS c = true := by
  unfold AtC.remadeS
  simp only [hz, proof_shared_written, r₂, decide_true]

include hz hm e₁ r₁ r₂ r₃ r₄ r₅ r₆ r₇ hs in
/-- **The file's own share of the tests on the plan.** -/
theorem file_share : AtC.front2 c = true ∧ AtC.beside X c = true := by
  constructor
  · unfold AtC.front2
    rw [n3_w r₂, sizedS_w hz, readShape_w hz r₄, readCodes_w hz r₅, readSamples_w hz r₂,
      remadeS_w hz r₂]
    rfl
  · unfold AtC.beside AtC.k12 AtC.front1 AtC.front3 AtC.file AtC.entries
    rw [stagesU_w r₂ r₄ r₅, stagesO_w r₂ r₄ r₅, stagesW_w r₃ r₄ r₅, n8_w r₄, n1_w e₁ r₆, n2_w r₇,
      n9_w r₇, remadeF_w hz e₁ r₁, n4_w r₃, remadeW_w hz r₃, n5_w r₄, n6_w r₄, ahead_w r₄,
      firstU_w r₄, firstO_w r₄, firstW_w r₄, heldS_w hm e₁, readPlans_w hm r₁ r₂ r₃,
      settingZ_w hz hs, madeSets_w hz hm e₁, frontS_w r₂ r₄ r₅, sealS_w r₂]
    rfl

end

/-! ## One closed test that can fail, and two statements that are no tests -/

/-- With one stage fewer in the test on the folded row's group. -/
theorem bend_stage : ioppOk proofSizedFull.codes proofSizedFull.batch.shape.testU.dropLast
    proofThree.B.plan.plan.samples = false := by
  decide +kernel

/-- With two samples. NO NEGATIVE TEST: the statement lays the 2 in itself and compares it with 1:
it holds whatever the plan is, and calls no routine of the library. -/
theorem bend_samples : (({ proofThree.B.plan.plan with samples := 2 } : Fmt.Plan).samples == 1) =
    false := by
  decide +kernel

/-- With a last entry that counts a batched row. NO NEGATIVE TEST: the statement lays that entry
in itself and reads it back: it holds whatever the plan's rounds are, and calls no routine of the
library. -/
theorem bend_seal : (((proofThree.B.plan.plan.rounds ++
    [({ name := "SEAL", rows := 1 } : Fmt.Entry)]).getLast?.map (·.rows == 0)).getD false) =
    false := by
  decide +kernel

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.finishHeld_holds
#print axioms Johnson.AtFull.Desc.finishHeld_set
#print axioms Johnson.AtFull.Desc.stagesU_w
#print axioms Johnson.AtFull.Desc.stagesO_w
#print axioms Johnson.AtFull.Desc.stagesW_w
#print axioms Johnson.AtFull.Desc.n8_w
#print axioms Johnson.AtFull.Desc.n1_w
#print axioms Johnson.AtFull.Desc.n2_w
#print axioms Johnson.AtFull.Desc.n9_w
#print axioms Johnson.AtFull.Desc.remadeF_w
#print axioms Johnson.AtFull.Desc.n4_w
#print axioms Johnson.AtFull.Desc.remadeW_w
#print axioms Johnson.AtFull.Desc.n5_w
#print axioms Johnson.AtFull.Desc.n6_w
#print axioms Johnson.AtFull.Desc.ahead_w
#print axioms Johnson.AtFull.Desc.firstU_w
#print axioms Johnson.AtFull.Desc.firstO_w
#print axioms Johnson.AtFull.Desc.firstW_w
#print axioms Johnson.AtFull.Desc.heldS_w
#print axioms Johnson.AtFull.Desc.readPlans_w
#print axioms Johnson.AtFull.Desc.settingZ_w
#print axioms Johnson.AtFull.Desc.madeSets_w
#print axioms Johnson.AtFull.Desc.frontS_w
#print axioms Johnson.AtFull.Desc.sealS_w
#print axioms Johnson.AtFull.Desc.n3_w
#print axioms Johnson.AtFull.Desc.sizedS_w
#print axioms Johnson.AtFull.Desc.readShape_w
#print axioms Johnson.AtFull.Desc.readCodes_w
#print axioms Johnson.AtFull.Desc.readSamples_w
#print axioms Johnson.AtFull.Desc.remadeS_w
#print axioms Johnson.AtFull.Desc.file_share
#print axioms Johnson.AtFull.Desc.bend_stage
#print axioms Johnson.AtFull.Desc.bend_samples
#print axioms Johnson.AtFull.Desc.bend_seal
