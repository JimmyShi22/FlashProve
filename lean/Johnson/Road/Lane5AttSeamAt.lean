-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttSeamAt.lean

THE SEAM BEFORE THE LOOKUP OF ATTENTION FROM publicOf's LINE, THE ONE LIST OF NUMBERS, AND ONE TEST.

linkOK_of_public (Johnson/Road/Lane5AttSeamPub.lean) asks profile 4, the number of groups and the
fourteen numbers FillRef. All three follow from publicOf's line and "Hd.PublicAt X.P" (the numbers
of the parameter file are the reference's: Johnson/Road/HeadL5Pub.lean, HeadL5All.lean). What is
left beside these two is the test on publicOf's own record:

* "attUsualK X": at every group g below 12, the configuration in the shape of the plan X.A[g] passes
  usualB (the usual call list; one shift in the group) and has kFD = 16. A program can run it.
* **"linkOK_of_publicAt"**, "attOrd_iff_publicAt": for every g below 12, and in the first for any
  parameters nf of the norm (the link does not read them). AttR0 is the light part: cells small,
  bits, the row's maximum and denominator. The scores and the accumulators stand in "InTables".

The test is no test of the verifier: see the head of Lane5AttSeamPub.lean. Whoever calls these
theorems from "a verifier accepts" must bring PublicAt and attUsualK as public premises of the end
statement.
Not claimed: that a parameter file has PublicAt or passes the test (a run at the parameter text
linesKF and the scale words scalesKF of Johnson/Road/FormsKeysRunK.lean:
Johnson/Road/Lane5AttSeamRun.lean; no Lean code compares them with files); all
that Lane5AttSeamPub.lean does not claim.
The two premises with content. At this record's own plan, if the scale file's words are scalesKF,
for every request that is true under a policy within its bounds both hold at a named list:
seam_of_true_file, Johnson/Road/Lane5AttSeamTrueAt.lean. Named true requests at this record's table:
seam_zero_all_file (there); true_real_gap_file, Johnson/Road/Lane5TrueGapAt.lean; in both every
layer's weights are 0; true_layer_file, seam_layer_file, Johnson/Road/Lane5TrueLayerAt.lean: values
and an output projection in layer 0, no counted position.
The key vectors in "InTables" are kvA (OnBytes/Tie/Pv/Lookup/Ends/A.lean), a term of this library
over the verifier's records, at the cells that addrA (Johnson/Road/Lane5AttDef.lean) places. The
verifier holds no key vector. That its key forms evaluate kvA is shown elsewhere under a premise
(rule, OnBytes/Tie/Pv/Lookup/Ends/AlgAW.lean); that addrA is the program's rule is shown nowhere.
"The verifier's own" is said here of shapeHid's record alone: sizes, pieces, tables.
-/
import Johnson.Road.Lane5AttSeamPub
import Johnson.Road.HeadL5All

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (ppref Instance Mat AcceptancePolicy NormPar)

/-- **The test on publicOf's own record.** -/
def attUsualK (X : Model.Verify.Public) : Bool :=
  (List.range 12).all fun g =>
    usualB (Hd.shapeA X g).cf && decide ((Hd.shapeA X g).cf.kFD = 16)

theorem attUsualK_at {X : Model.Verify.Public} (h : attUsualK X = true) {g : ℕ} (hg : g < 12) :
    usualB (Hd.shapeA X g).cf = true ∧ (Hd.shapeA X g).cf.kFD = 16 := by
  unfold attUsualK at h
  rw [List.all_eq_true] at h
  have k := h g (List.mem_range.2 hg)
  rw [Bool.and_eq_true, decide_eq_true_eq] at k
  exact k

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **The seam before the lookup of attention of group g, from publicOf's line, the one list of
numbers and the test.** -/
theorem linkOK_of_publicAt (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (A : Hd.PublicAt X.P) (U : attUsualK X = true) (nf : NormPar) {g : ℕ} (hg : g < 12) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      ∀ (Z : Zs) (po : AcceptancePolicy) (Wz : Mat) (x : Instance ppref), AttR0 Ag.S Z →
        (callsA Ag.S Ag.fs Z).InTables →
        LinkOK Cm.Seg.Hd.main
          (Policy.segPol (scalesOf (Model.Verify.layerShape X.P) X.layers.sc nf) po) Wz x
          (2 * g + 1) (attMx Ag.S g Z) := by
  have H := Hd.public_of_publicOf h A
  exact linkOK_of_public h H.p4 (Hd.fillRef_of_at A H) (by rw [H.groups]; exact hg) hg
    (Model.Verify.layerShape X.P) nf (attUsualK_at U hg).1 (attUsualK_at U hg).2

/-- At that plan the attention link is in order if and only if its part without the lookup clause
holds and every call's keys lie in its table. -/
theorem attOrd_iff_publicAt (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (A : Hd.PublicAt X.P) (U : attUsualK X = true) {g : ℕ} (hg : g < 12) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      ∀ Z : Zs, AttOrd Ag.S Z ↔ AttR0 Ag.S Z ∧ (callsA Ag.S Ag.fs Z).InTables := by
  have H := Hd.public_of_publicOf h A
  exact attOrd_iff_public h H.p4 (Hd.fillRef_of_at A H) (by rw [H.groups]; exact hg)
    (attUsualK_at U hg).1 (attUsualK_at U hg).2

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.linkOK_of_publicAt
#print axioms OnBytes.Road.L5.attOrd_iff_publicAt
