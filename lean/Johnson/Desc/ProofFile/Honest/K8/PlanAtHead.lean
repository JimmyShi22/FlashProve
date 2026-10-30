-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/PlanAtHead.lean: the smallness test (K8): public data alone: UNDER
THE LIBRARY's HEAD THE PLAN's RECORD OF EACH OF THE 25 SEGMENTS HAS THE WRITTEN VIEW; SO ITS COUNT
OF MATRICES, THEIR LABELS, ROWS AND COLUMNS ARE WRITTEN VALUES; THE SIZES `Sz.ref` GIVE EACH MATRIX
THESE ROWS AND COLUMNS; AND SEGMENT 0's NINE MATRICES ARE ITS OWN, IN ORDER. No definition; four
closed facts by Lean's kernel, two of them controls; lemmas.

  `view_at_head`     tailView (Meaning.tlAt (P5J.At.X Zp) l) = K8Q35.tvW l
  `nm_at_head`, `lab_at_head`, `rows_at_head`   the count, the label, the rows and columns of matrix
                    μ, off the written view
  `rows_of_view`     the sister of the library's `lab_of_view` at the rows and columns
  `shapesW`          BY LEAN's KERNEL: at each of the 25 written views, at each matrix below the
                    written count: `Sz.ref.shapeNo l μ` is the view's rows and columns
  `shapesW_bite`     A CONTROL THAT SAYS NO: with one row more the test fails at each of the 25: at
                    each some matrix turns it; that every matrix does is not said
  **`shapesFit_plan`**   `ShapesFit (Meaning.tlAt (P5J.At.X Zp) l) Sz.ref l`
                    (Johnson/HonestTrace/PackedJoins.lean, of other authors)
  `ownW`             BY LEAN's KERNEL: the written count at segment 0 is 9, and the label of its
                    matrix μ names the owner (0, μ)
  `ownW_bite`        A CONTROL THAT SAYS NO: read at segment 1's labels the second clause fails
  **`own_first`**      at segment 0: the count is 9; `ownerK` of the label is 0 and `ownerA` is μ
The recipe for `view_at_head` stands inside the library's own proof of `mats_of_written`
(Johnson/K8Q35R/MatsAtHead.lean): `tail_at` at `xShape_in_scope`, `pub_public` and
`publicOfO_older`.
Two options are raised at the closed facts (maxRecDepth, maxHeartbeats), one in the whole file
(maxHeartbeats), and one instance is taken away, as in the files beneath. No tactic that searches;
four lines are an evaluation each by Lean's kernel (`decide +kernel`).
Limits. The head is a hypothesis. The full size alone; decided at one version of the written view.
No prover, no Script, no input, no coin, no state of the verifier.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.K8Q35R.MatsAtHead
import Johnson.HonestTrace.PackedJoins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz ShapesFit)
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (tailView)
open K8Q35 (tvW nmW labW tm0)
open P5J (AtMgA TS)

/-- The rows and columns of a matrix, off the view. -/
theorem rows_of_view (t : HTailF2) (μ : ℕ) :
    ((tailView t).2.1.getD μ tm0).2 = ((t.mats.getD μ {}).m, (t.mats.getD μ {}).k) := by
  show ((t.mats.toList.map fun x => (x.aId, x.m, x.k)).getD μ tm0).2 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases t.mats[μ]? <;> rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The sizes give each written matrix its written rows and columns. -/
theorem shapesW : ((List.range 25).all fun l => (List.range (nmW l)).all fun μ =>
    decide (Sz.ref.shapeNo l μ = ((tvW l).2.1.getD μ tm0).2)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: with one row more the test says no at each of the 25. -/
theorem shapesW_bite : ((List.range 25).any fun l => (List.range (nmW l)).all fun μ =>
    decide (((Sz.ref.shapeNo l μ).1 + 1, (Sz.ref.shapeNo l μ).2) =
      ((tvW l).2.1.getD μ tm0).2)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Segment 0 has nine matrices, each its own, in order. -/
theorem ownW : (decide (nmW 0 = 9) && (List.range 9).all fun μ =>
    decide (Meaning.ownerK (labW 0 μ) = 0) && decide (Meaning.ownerA (labW 0 μ) = μ)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at segment 1's labels the clause on the owners says no. -/
theorem ownW_bite : ((List.range (nmW 1)).all fun μ =>
    decide (Meaning.ownerK (labW 1 μ) = 0) && decide (Meaning.ownerA (labW 1 μ) = μ)) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the plan's record of segment l has the written view. -/
theorem view_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l ≤ 24) :
    tailView (Meaning.tlAt (P5J.At.X Zp) l) = tvW l := by
  have hy := h.toAtMg.made_accepts
  obtain ⟨pp, hR⟩ := IM.reads_of_scope h.scope
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public h.laid.pub
  exact K8Q35.tail_at h.scope hR hpub
    (VerifiableInference.PlanWritten.Joined.xShape_in_scope h.scope h.laid.pub hy) hl

/-- The plan's count of matrices is the written one. -/
theorem nm_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l ≤ 24) :
    (Meaning.tlAt (P5J.At.X Zp) l).NM = nmW l := congrArg (·.1) (view_at_head h hl)

/-- The label of the plan's matrix μ is the written one. -/
theorem lab_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l ≤ 24) (μ : ℕ) :
    Meaning.labAt (P5J.At.X Zp) l μ = labW l μ := by
  unfold labW
  rw [← view_at_head h hl]
  exact (K8Q35.lab_of_view _ μ).symm

/-- The rows and columns of the plan's matrix μ are the written ones. -/
theorem rows_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l ≤ 24) (μ : ℕ) :
    (((Meaning.tlAt (P5J.At.X Zp) l).mats.getD μ {}).m,
      ((Meaning.tlAt (P5J.At.X Zp) l).mats.getD μ {}).k) = ((tvW l).2.1.getD μ tm0).2 := by
  rw [← view_at_head h hl]
  exact (rows_of_view _ μ).symm

/-- **The sizes fit the plan's record**, at each of the 25 segments. -/
theorem shapesFit_plan (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) :
    ShapesFit (Meaning.tlAt (P5J.At.X Zp) l) Sz.ref l := by
  intro μ hμ
  rw [nm_at_head h (Nat.le_of_lt_succ hl)] at hμ
  rw [rows_at_head h (Nat.le_of_lt_succ hl) μ]
  exact of_decide_eq_true (List.all_eq_true.1
    (List.all_eq_true.1 shapesW l (List.mem_range.2 hl)) μ (List.mem_range.2 hμ))

/-- **Segment 0's nine matrices are its own, in order.** -/
theorem own_first (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (Meaning.tlAt (P5J.At.X Zp) 0).NM = 9 ∧ ∀ μ, μ < 9 →
      Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) 0 μ) = 0 ∧
        Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) 0 μ) = μ := by
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) ownW
  refine ⟨(nm_at_head h (Nat.zero_le 24)).trans (of_decide_eq_true h1), fun μ hμ => ?_⟩
  obtain ⟨h3, h4⟩ := Eq.mp (Bool.and_eq_true _ _)
    (List.all_eq_true.1 h2 μ (List.mem_range.2 hμ))
  rw [lab_at_head h (Nat.zero_le 24) μ]
  exact ⟨of_decide_eq_true h3, of_decide_eq_true h4⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.rows_of_view
#print axioms ProofFile.Honest.K8.shapesW
#print axioms ProofFile.Honest.K8.shapesW_bite
#print axioms ProofFile.Honest.K8.ownW
#print axioms ProofFile.Honest.K8.ownW_bite
#print axioms ProofFile.Honest.K8.view_at_head
#print axioms ProofFile.Honest.K8.nm_at_head
#print axioms ProofFile.Honest.K8.lab_at_head
#print axioms ProofFile.Honest.K8.rows_at_head
#print axioms ProofFile.Honest.K8.shapesFit_plan
#print axioms ProofFile.Honest.K8.own_first
