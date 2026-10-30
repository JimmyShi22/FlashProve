-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondReads.lean: what the condition of the law of a proximity test (the kind
K12) reads of a place.

The condition (`K12Condition`, ChainHolds.lean) reads of a place's numbers two fields: `nums` and
`idx`; and `nums` through three doors alone: its stages, its bits of work, and its declared rounds
as written rounds (`writtenOf`, PubOk.lean). It reads neither the address, nor the oracle messages,
nor what must have been sent before, nor the answers, nor whether the masks come early. Of its four
clauses only the first, the test `pubOk`, reads `idx`, the bits of work by themselves and the
record's codes K.
Main names:
  `walkL_reads`, `pubOk_reads`, `spendOk_reads`: the two tests with code at two places that agree in
    what is read.
  `k12Condition_reads`: the condition at two such places is one. `k12Condition_nums`: the same from
    `p.nums = q.nums` and `p.idx = q.idx`.
  `K12Condition.of_pub`: from the condition at a place q and some codes: the condition at a place p
    with the same stages and written rounds, at any codes K at which `pubOk p K` says yes.
Limits: `writtenOf` reads all seven fields of `nums`: no field is shown idle here. The radii are the
same letter on both sides. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.ChainHolds

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open scoped ENNReal

theorem walkL_reads {p q : P12} (K : Codes) (hw : p.nums.work = q.nums.work)
    (hi : p.idx = q.idx) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (a : Fmt.M1.Stage) (l : List WR),
    walkL p K j a rest l = walkL q K j a rest l
  | [], j, a, l => by
    conv_lhs => rw [walkL.eq_def]
    conv_rhs => rw [walkL.eq_def]
    simp only [hi, hw]
  | b :: rest, j, a, l => by
    have ih := walkL_reads K hw hi rest
    conv_lhs => rw [walkL.eq_def]
    conv_rhs => rw [walkL.eq_def]
    simp only [ih, hi, hw]

theorem pubOk_reads {p q : P12} (K : Codes) (hs : p.nums.stages = q.nums.stages)
    (hw : p.nums.work = q.nums.work) (hW : writtenOf p.nums = writtenOf q.nums)
    (hi : p.idx = q.idx) : pubOk p K = pubOk q K := by
  unfold pubOk pubL
  rw [hs, hW]
  simp only [walkL_reads K hw hi]

theorem spendOk_reads {p q : P12} (hs : p.nums.stages = q.nums.stages)
    (hW : writtenOf p.nums = writtenOf q.nums) : spendOk p = spendOk q := by
  unfold spendOk spendAll
  rw [hs, hW]

/-- One way. -/
theorem K12Condition.of_reads {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {p q : P12} {K : Codes}
    {εs : ℝ≥0∞} (hs : p.nums.stages = q.nums.stages) (hw : p.nums.work = q.nums.work)
    (hW : writtenOf p.nums = writtenOf q.nums) (hi : p.idx = q.idx)
    (h : K12Condition L mC mS mW rad q K εs) : K12Condition L mC mS mW rad p K εs :=
  ⟨(pubOk_reads K hs hw hW hi).trans h.pub, (spendOk_reads hs hW).trans h.spend, hs ▸ h.codes,
    fun a rest w0 l c e1 e2 e3 => h.small a rest w0 l c (hs ▸ e1) (hW ▸ e2) e3⟩

/-- **With the first clause as a premise**: the three other clauses read the stages and the written
rounds alone, and neither `idx` nor the record's codes. -/
theorem K12Condition.of_pub {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {p q : P12} {K K' : Codes}
    {εs : ℝ≥0∞} (hs : p.nums.stages = q.nums.stages)
    (hW : writtenOf p.nums = writtenOf q.nums) (hpub : pubOk p K = true)
    (h : K12Condition L mC mS mW rad q K' εs) : K12Condition L mC mS mW rad p K εs :=
  ⟨hpub, (spendOk_reads hs hW).trans h.spend, hs ▸ h.codes,
    fun a rest w0 l c e1 e2 e3 => h.small a rest w0 l c (hs ▸ e1) (hW ▸ e2) e3⟩

/-- **The condition at two places that agree in what it reads is one.** -/
theorem k12Condition_reads {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {p q : P12} {K : Codes}
    {εs : ℝ≥0∞} (hs : p.nums.stages = q.nums.stages) (hw : p.nums.work = q.nums.work)
    (hW : writtenOf p.nums = writtenOf q.nums) (hi : p.idx = q.idx) :
    K12Condition L mC mS mW rad p K εs ↔ K12Condition L mC mS mW rad q K εs :=
  ⟨K12Condition.of_reads hs.symm hw.symm hW.symm hi.symm, K12Condition.of_reads hs hw hW hi⟩

/-- The same from the two fields. -/
theorem k12Condition_nums {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {p q : P12} {K : Codes}
    {εs : ℝ≥0∞} (hn : p.nums = q.nums) (hi : p.idx = q.idx) :
    K12Condition L mC mS mW rad p K εs ↔ K12Condition L mC mS mW rad q K εs :=
  k12Condition_reads (by rw [hn]) (by rw [hn]) (by rw [hn]) hi

end H2K.Pub

#print axioms H2K.Pub.pubOk_reads
#print axioms H2K.Pub.spendOk_reads
#print axioms H2K.Pub.K12Condition.of_pub
#print axioms H2K.Pub.k12Condition_reads
#print axioms H2K.Pub.k12Condition_nums
