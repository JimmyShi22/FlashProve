-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean: what a yes and a no of the two tests on a proof
file's sizes say (`sizedPinned`, `firstPinned`, Johnson/Desc/Ok/PlanWritten/SizedTest.lean), that
each has a member, and plants that they refuse.

Statements and proofs.
  `sameTest_eq`, `sameLines_eq`, `sameLin_eq`, `sameProof_eq`: a yes of each comparison gives the
    equation of whole records: so no field is left out. `sameTest_self`, `sameLines_self`,
    `sameLin_self`, `sameProof_self`: each says yes of a record and itself.
  `sizedPinned_eq`: at the full size's key a yes gives z = `proofSizedFull`. `sizedPinned_other`: at
    every other key the test says yes. `sizedPinned_no`: a no says that the key is the full size's
    and that z is another value than the written one.
  `sized_of_pinnedAt`, `pinnedAt_no`: the same of `sizedPinnedAt`.
  `sizedPinned_self`: the written value passes.
  The plants: with one more in one number the test says no; each of the six fields of a proof file's
    sizes has one: `plant_set` (the setting's target), `plant_front` (a number of the first code),
    `plant_link` (the positions of the links' group), `plant_test` (the positions of the last test),
    `plant_request` (the number of the code that the request's shape names), `plant_requests` and
    `plant_last` (in the test on the table: the requests of a batch; the batches that a stored copy
    covers, which is the last field of the last record). `sizedPlant_other_key`: at a key that is
    not the full size's the last of these passes: that arm is open.
  `firstPinned_eq`, `firstPinned_other`, `firstPinned_no`, `first_of_pinnedAt`: the like of the test
    on the first chain's parameters as read back: a yes at the full size's key gives five equations;
    a no says that the key is the full size's and that one of the five fails. `first_self`: a record
    with the five written fields passes. `first_plants`: with one of the five turned the test says
    no: a plant a field.
  `codes_written`: the written sizes' codes are the library's written codes of the proof file's
    chains (`codesFull2`, Johnson/G/PackLit.lean).
By evaluations in Lean's kernel (`decide +kernel`): the eight statements on plants of the first
test, `first_plants`, `codes_written`.

What of OnBytes/Model/ is used: `PolScan`.

Limits. That the planner's sizes at any public files pass the test is not said: that is a run's to
show. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.SizedTest
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes.Params

/-! ## A yes of a comparison is an equation of whole records -/

theorem sameTest_eq {a b : TestSizes} (h : sameTest a b = true) : a = b := by
  simp only [sameTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  cases a
  cases b
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem sameLines_eq {a b : LinLines} (h : sameLines a b = true) : a = b := by
  simp only [sameLines, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases a
  cases b
  simp only at h1 h2 h3 h4 h5 h6 h7 h8
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

theorem sameLin_eq {a b : LinSized} (h : sameLin a b = true) : a = b := by
  simp only [sameLin, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have k1 := sameLines_eq h1
  have k5 := sameTest_eq h5
  have k6 := sameTest_eq h6
  have k7 := sameTest_eq h7
  cases a
  cases b
  simp only at k1 h2 h3 h4 k5 k6 k7 h8
  subst k1 h2 h3 h4 k5 k6 k7 h8
  rfl

/-- **A yes gives the equation of the two records, whole.** -/
theorem sameProof_eq {a b : ProofSized} (h : sameProof a b = true) : a = b := by
  simp only [sameProof, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have k4 := sameTest_eq h4
  have k6 := sameLin_eq h6
  cases a
  cases b
  simp only at h1 h2 h3 k4 h5 k6
  subst h1 h2 h3 k4 h5 k6
  rfl

theorem sameTest_self (a : TestSizes) : sameTest a a = true := by simp [sameTest]

theorem sameLines_self (a : LinLines) : sameLines a a = true := by simp [sameLines]

theorem sameLin_self (a : LinSized) : sameLin a a = true := by
  simp [sameLin, sameLines_self, sameTest_self]

theorem sameProof_self (a : ProofSized) : sameProof a a = true := by
  simp [sameProof, sameTest_self, sameLin_self]

/-! ## The test -/

/-- **At the full size's key a yes gives the written value.** -/
theorem sizedPinned_eq {z : ProofSized} (h : sizedPinned fullKey z = true) :
    z = proofSizedFull := by
  unfold sizedPinned at h
  rw [if_pos rfl] at h
  exact sameProof_eq h

/-- At every other key the test says yes. -/
theorem sizedPinned_other {k : ℕ × ℕ × ℕ} (z : ProofSized) (hk : k ≠ fullKey) :
    sizedPinned k z = true := by
  unfold sizedPinned
  rw [if_neg hk]

/-- **What a no says.** -/
theorem sizedPinned_no {k : ℕ × ℕ × ℕ} {z : ProofSized} (h : sizedPinned k z = false) :
    k = fullKey ∧ z ≠ proofSizedFull := by
  by_cases hk : k = fullKey
  · refine ⟨hk, fun e => ?_⟩
    unfold sizedPinned at h
    rw [if_pos hk, e, sameProof_self] at h
    cases h
  · rw [sizedPinned_other z hk] at h
    cases h

theorem sized_of_pinnedAt {P : OnBytes.Model.PolScan} {made : Configured}
    (h : sizedPinnedAt P made = true) (hk : keyOfScan P = fullKey) :
    made.sized.proof = proofSizedFull := by
  unfold sizedPinnedAt at h
  rw [hk] at h
  exact sizedPinned_eq h

theorem pinnedAt_no {P : OnBytes.Model.PolScan} {made : Configured}
    (h : sizedPinnedAt P made = false) :
    keyOfScan P = fullKey ∧ made.sized.proof ≠ proofSizedFull :=
  sizedPinned_no h

/-- The written value passes. -/
theorem sizedPinned_self : sizedPinned fullKey proofSizedFull = true := by
  unfold sizedPinned
  rw [if_pos rfl]
  exact sameProof_self _

/-! ## Plants -/

/-- The written value with one more in the last field of its last record. -/
def plantLast : ProofSized :=
  { proofSizedFull with batch := { proofSizedFull.batch with
      batches := proofSizedFull.batch.batches + 1 } }

/-- With one more in a number of the first code. -/
def plantFront : ProofSized :=
  { proofSizedFull with codes := { proofSizedFull.codes with
      base := proofSizedFull.codes.base.modify 0 fun c => { c with r := c.r + 1 } } }

/-- With one more request of a batch. -/
def plantRequests : ProofSized :=
  { proofSizedFull with batch := { proofSizedFull.batch with
      lines := { proofSizedFull.batch.lines with
        requests := proofSizedFull.batch.lines.requests + 1 } } }

/-- With one more position of the last test. -/
def plantTest : ProofSized :=
  { proofSizedFull with last := { proofSizedFull.last with t := proofSizedFull.last.t + 1 } }

/-- With one more in the setting's target. -/
def plantSet : ProofSized :=
  { proofSizedFull with set := { proofSizedFull.set with target := proofSizedFull.set.target + 1 } }

/-- With one more position of the links' group. -/
def plantLink : ProofSized :=
  { proofSizedFull with link := { proofSizedFull.link with t := proofSizedFull.link.t + 1 } }

/-- With one more in the number of the code that the request's shape names. -/
def plantRequest : ProofSized :=
  { proofSizedFull with request := { proofSizedFull.request with
      code := proofSizedFull.request.code + 1 } }

theorem plant_last : sizedPinned fullKey plantLast = false := by decide +kernel

theorem plant_front : sizedPinned fullKey plantFront = false := by decide +kernel

theorem plant_requests : sizedPinned fullKey plantRequests = false := by decide +kernel

theorem plant_test : sizedPinned fullKey plantTest = false := by decide +kernel

theorem plant_set : sizedPinned fullKey plantSet = false := by decide +kernel

theorem plant_link : sizedPinned fullKey plantLink = false := by decide +kernel

theorem plant_request : sizedPinned fullKey plantRequest = false := by decide +kernel

/-- At a key that is not the full size's the first plant passes: that arm is open. -/
theorem sizedPlant_other_key : sizedPinned (48, 5120, 202049) plantLast = true := by decide +kernel

/-! ## The first chain's parameters as read back -/

/-- **At the full size's key a yes gives the five equations.** -/
theorem firstPinned_eq {f : First} (h : firstPinned fullKey f = true) :
    f.codes = proofSizedFull.codes ∧ f.lin = proofSizedFull.batch.shape ∧
      f.shape = proofSizedFull.request ∧ f.pendingRows = 13 ∧ f.binding = ⟨6, 40⟩ := by
  unfold firstPinned at h
  rw [if_pos rfl] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- At every other key the test says yes. -/
theorem firstPinned_other {k : ℕ × ℕ × ℕ} (f : First) (hk : k ≠ fullKey) :
    firstPinned k f = true := by
  unfold firstPinned
  rw [if_neg hk]

/-- **What a no says.** -/
theorem firstPinned_no {k : ℕ × ℕ × ℕ} {f : First} (h : firstPinned k f = false) :
    k = fullKey ∧ ¬ (f.codes = proofSizedFull.codes ∧ f.lin = proofSizedFull.batch.shape ∧
      f.shape = proofSizedFull.request ∧ f.pendingRows = 13 ∧ f.binding = ⟨6, 40⟩) := by
  by_cases hk : k = fullKey
  · refine ⟨hk, fun e => ?_⟩
    obtain ⟨e1, e2, e3, e4, e5⟩ := e
    unfold firstPinned at h
    rw [if_pos hk, e1, e2, e3, e4, e5] at h
    simp at h
  · rw [firstPinned_other f hk] at h
    cases h

theorem first_of_pinnedAt {P : OnBytes.Model.PolScan} {f : First}
    (h : firstPinnedAt P f = true) (hk : keyOfScan P = fullKey) :
    f.codes = proofSizedFull.codes ∧ f.lin = proofSizedFull.batch.shape ∧
      f.shape = proofSizedFull.request ∧ f.pendingRows = 13 ∧ f.binding = ⟨6, 40⟩ := by
  unfold firstPinnedAt at h
  rw [hk] at h
  exact firstPinned_eq h

/-- A record with the five fields of the written sizes; its four other fields are empty. -/
def firstOfWritten : First :=
  { given := ⟨ByteArray.empty, ⟨.two, 0, 0, 0, 0, 0, []⟩, ByteArray.empty, []⟩,
    codes := proofSizedFull.codes, lin := proofSizedFull.batch.shape,
    shape := proofSizedFull.request, layout := ⟨[]⟩, identifiers := [], pendingRows := 13,
    binding := ⟨6, 40⟩, more := [] }

/-- That record passes. -/
theorem first_self : firstPinned fullKey firstOfWritten = true := by
  unfold firstPinned
  rw [if_pos rfl]
  simp [firstOfWritten]

/-- With one of the five fields turned the test says no: a plant a field. -/
theorem first_plants :
    firstPinned fullKey { firstOfWritten with codes := plantFront.codes } = false ∧
      firstPinned fullKey { firstOfWritten with lin := { firstOfWritten.lin with
        kLo := firstOfWritten.lin.kLo + 1 } } = false ∧
      firstPinned fullKey { firstOfWritten with shape := plantRequest.request } = false ∧
      firstPinned fullKey { firstOfWritten with pendingRows := 14 } = false ∧
      firstPinned fullKey { firstOfWritten with binding := ⟨6, 41⟩ } = false := by
  decide +kernel

/-! ## The written codes are the library's -/

/-- The written sizes' codes are the library's written codes of the proof file's chains. -/
theorem codes_written : proofSizedFull.codes = Johnson.G.codesFull2 := by decide +kernel

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.sameTest_eq
#print axioms VerifiableInference.PlanWritten.sameLines_eq
#print axioms VerifiableInference.PlanWritten.sameLin_eq
#print axioms VerifiableInference.PlanWritten.sameProof_eq
#print axioms VerifiableInference.PlanWritten.sameTest_self
#print axioms VerifiableInference.PlanWritten.sameLines_self
#print axioms VerifiableInference.PlanWritten.sameLin_self
#print axioms VerifiableInference.PlanWritten.sameProof_self
#print axioms VerifiableInference.PlanWritten.sizedPinned_eq
#print axioms VerifiableInference.PlanWritten.sizedPinned_other
#print axioms VerifiableInference.PlanWritten.sizedPinned_no
#print axioms VerifiableInference.PlanWritten.sized_of_pinnedAt
#print axioms VerifiableInference.PlanWritten.pinnedAt_no
#print axioms VerifiableInference.PlanWritten.sizedPinned_self
#print axioms VerifiableInference.PlanWritten.plant_last
#print axioms VerifiableInference.PlanWritten.plant_front
#print axioms VerifiableInference.PlanWritten.plant_requests
#print axioms VerifiableInference.PlanWritten.plant_test
#print axioms VerifiableInference.PlanWritten.plant_set
#print axioms VerifiableInference.PlanWritten.plant_link
#print axioms VerifiableInference.PlanWritten.plant_request
#print axioms VerifiableInference.PlanWritten.sizedPlant_other_key
#print axioms VerifiableInference.PlanWritten.firstPinned_eq
#print axioms VerifiableInference.PlanWritten.firstPinned_other
#print axioms VerifiableInference.PlanWritten.firstPinned_no
#print axioms VerifiableInference.PlanWritten.first_of_pinnedAt
#print axioms VerifiableInference.PlanWritten.first_self
#print axioms VerifiableInference.PlanWritten.first_plants
#print axioms VerifiableInference.PlanWritten.codes_written
