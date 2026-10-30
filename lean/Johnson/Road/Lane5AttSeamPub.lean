-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttSeamPub.lean

THE SEAM BEFORE THE LOOKUP OF ATTENTION, FROM THE PUBLIC PART OF THE VERIFIER's STAGE: if publicOf
(OnBytes/Model/VerifyPublic.lean) returns X on the three public files, then at the attention plan
X.A[g] of every group g: the link's meaning without its lookup clause, and "every call's keys lie in
its table", give that link 2 g + 1 is in order; and the two together say what "the attention link
is in order" says. AttR0 is the light part: cells small, bits, the row's maximum and denominator.
The scores and the accumulators stand in "InTables".

linkOK_of_usual (Johnson/Road/Lane5AttSeam.lean) begins at shapeHid's equation and premises on the
configuration. Here the configuration is the one that the verifier's own fill makes of the
parameter file's numbers, the layers' layout and the file of scales, on some call list "lines":
that this list is the parameter file's is not shown, which is why the call list must be a test.
The table of scales is scalesOf of that file, at any layer shape hL and any parameters nf of the
norm: the link reads neither.

What is left as public premises:
* publicOf's call; profile 4; g below the number of groups and below 12;
* FillRef X.P X.y: fourteen numbers of the parameter file and of the layers' layout are the
  reference numbers (Johnson/Road/Lane5AttPub.lean);
* TWO TESTS ON publicOf's OWN RECORD, which a program can run: usualB (the usual call list; one
  shift in the group) and kFD = 16, both at the configuration in the shape of the plan X.A[g].
UsualCalls is no test of the verifier: the verifier takes other call lists, and groups with two
shifts; at these this file says nothing. Whoever calls these theorems from "a verifier accepts"
must bring the two tests as public premises of the end statement.

* "hid_of_public": the plan X.A[g]: its shape and its lookup's record are what shapeHid returns on
  what fill returns.
* **"linkOK_of_public"**, **"attOrd_iff_public"**.

Not claimed: that a parameter file has the fourteen numbers or passes the two tests; "InTables" for
a proof that a verifier accepts; all that Lane5AttSeam.lean does not claim.
The two premises with content. Under the premises of Johnson/Road/Lane5AttSeamAt.lean (PublicAt,
attUsualK): at this record's own plan, if the scale file's words are scalesKF, for every request
that is true under a policy within its bounds both hold at a named list: seam_of_true_file,
Johnson/Road/Lane5AttSeamTrueAt.lean. Named true requests at this record's table: seam_zero_all_file
(there); true_real_gap_file, Johnson/Road/Lane5TrueGapAt.lean; in both every layer's weights are 0;
true_layer_file, seam_layer_file, Johnson/Road/Lane5TrueLayerAt.lean: values and an output
projection in layer 0, no counted position.
The key vectors in "InTables" are kvA (OnBytes/Tie/Pv/Lookup/Ends/A.lean), a term of this library
over the verifier's records, at the cells that addrA (Johnson/Road/Lane5AttDef.lean) places. The
verifier holds no key vector. That its key forms evaluate kvA is shown elsewhere under a premise
(rule, OnBytes/Tie/Pv/Lookup/Ends/AlgAW.lean); that addrA is the program's rule is shown nowhere.
"The verifier's own" is said here of shapeHid's record alone: sizes, pieces, tables.
-/
import Johnson.Road.Lane5AttSeamMet
import Johnson.Road.Lane5AttPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (ppref Instance Mat AcceptancePolicy NormPar)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **The plan of group g in the public part of a stage**: its shape and its lookup's record are
what shapeHid returns on the configuration that fill returns on some call list "lines": that it is
the parameter file's is not shown. -/
theorem hid_of_public (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) {g : ℕ} (hg : g < X.y.NGr) :
    ∃ (Ag : Attention.Plan) (lines : List Attention.Line) (cf : Attention.Cfg),
      X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      Attention.fill X.P X.y X.layers.sc lines g = Except.ok cf ∧
      Attention.shapeHid X.P.settings.lidb cf = Except.ok (Ag.S, Ag.fs) ∧ Ag.S.Lam = X.y.Lam := by
  obtain ⟨lines, A0, seenG, seenA, -, H⟩ := Hd.groups_of_public h hp4
  obtain ⟨Xg, Ag, s, hG, -, -, hA, eAS, eAf, -, -, eS⟩ := H g hg
  obtain ⟨cf, hf, hp, hLam⟩ := group_plan hG
  refine ⟨Ag, lines, cf, hA, eAS.trans eS.symm, hf, ?_, ?_⟩
  · rw [eAS, eAf]
    exact (plan_shape hp).1
  · rw [eAS]
    exact hLam

/-- **The seam before the lookup of attention of group g, from the public part of the verifier's
stage.** -/
theorem linkOK_of_public (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) (F : FillRef X.P X.y) {g : ℕ}
    (hg : g < X.y.NGr) (hg12 : g < 12) (hL : Model.Layer.Shape) (nf : NormPar)
    (hU : usualB (Hd.shapeA X g).cf = true) (hk : (Hd.shapeA X g).cf.kFD = 16) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      ∀ (Z : Zs) (po : AcceptancePolicy) (Wz : Mat) (x : Instance ppref), AttR0 Ag.S Z →
        (callsA Ag.S Ag.fs Z).InTables →
        LinkOK Cm.Seg.Hd.main (Policy.segPol (scalesOf hL X.layers.sc nf) po) Wz x (2 * g + 1)
          (attMx Ag.S g Z) := by
  obtain ⟨Ag, lines, cf, hA, eS, hf, hh, hLam⟩ := hid_of_public h hp4 hg
  obtain ⟨hc, h12, h8, -⟩ := cfRef_of_fill hf F
  have ec : (Hd.shapeA X g).cf = cf := by rw [← eS]; exact (shaped_of_hid hh).cfg
  rw [ec] at hU hk
  have hS := attSized_hid hh hc h12 h8
  refine ⟨Ag, hA, eS, fun Z po Wz x R I => ?_⟩
  exact linkOK_of_usual hh hc hk h12 h8 (usual_of_test hU) hg12
    (hsh_of_fill hf (hLam.symm.trans hS.Lam) hg12 hL nf) po Wz x R I

/-- **At that plan the attention link is in order if and only if its part without the lookup clause
holds and every call's keys lie in its table.** -/
theorem attOrd_iff_public (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) (F : FillRef X.P X.y) {g : ℕ}
    (hg : g < X.y.NGr) (hU : usualB (Hd.shapeA X g).cf = true)
    (hk : (Hd.shapeA X g).cf.kFD = 16) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      ∀ Z : Zs, AttOrd Ag.S Z ↔ AttR0 Ag.S Z ∧ (callsA Ag.S Ag.fs Z).InTables := by
  obtain ⟨Ag, lines, cf, hA, eS, hf, hh, -⟩ := hid_of_public h hp4 hg
  obtain ⟨hc, h12, h8, -⟩ := cfRef_of_fill hf F
  have ec : (Hd.shapeA X g).cf = cf := by rw [← eS]; exact (shaped_of_hid hh).cfg
  rw [ec] at hU hk
  exact ⟨Ag, hA, eS, fun Z => attOrd_iff_usual hh hc hk h12 h8 (usual_of_test hU) Z⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.hid_of_public
#print axioms OnBytes.Road.L5.linkOK_of_public
#print axioms OnBytes.Road.L5.attOrd_iff_public
