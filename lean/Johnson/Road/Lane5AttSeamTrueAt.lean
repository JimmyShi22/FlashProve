-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5AttSeamTrueAt.lean

At the plan of group g in the record that the verifier's publicOf returns, the two premises with
content of the seam before attention's lookup hold together, at a named list: for every request that
is true under its policy.

"linkOK_of_publicAt" (Johnson/Road/Lane5AttSeamAt.lean) has two premises with content: "AttR0" and
"InTables". That they can be met is shown at the record that "shapeHid" returns, on conditions
("seam_met", Johnson/Road/Lane5AttSeamMet.lean), and for every true request at a shape that is a
letter ("seam_of_trueL", Johnson/Road/Lane5AttSeamTrueL.lean). Here both stand at the record's own
plan.

Main theorems. X is what publicOf has returned; "Hd.PublicAt X.P" and the test "attUsualK X" are the
public premises of "linkOK_of_publicAt"; the plan Ag is fixed by X.A[g]? = some Ag.
* "seam_of_true_publicAt": at a lawful table "scalesOf (layerShape X.P) X.layers.sc nf" and a policy
  with "Policy.PolCond": for every index i and request x that is true under the policy, "AttR0" and
  "InTables" hold at the list "zsOf Ag.S g T", T the matrices of the library's honest trace with the
  ledger.
* "seam_of_true_file": the same at nf := "Hd.npOf X.hS", where the table is lawful if the scale
  file's words are "scalesKF" ("lawful_of_at", Johnson/Road/Lane5TopPub.lean).
* "seam_zero_all_file": so at all weights 0 and a policy with 257 ≤ theta and 257 ≤ C: for every
  request that has its form, with y = 0 if e = 1,024, whatever its other tokens, the list read off
  its own honest trace meets both ("Policy.TrueGuards.zero_all", Policy/Rel/TrueGuards.lean). Such a
  request may have up to 1,023 counted positions.

Limits. The key vectors in "InTables" are kvA (OnBytes/Tie/Pv/Lookup/Ends/A.lean), a term of this
library over the verifier's records, at the cells that addrA (Johnson/Road/Lane5AttDef.lean) places.
The verifier holds no key vector; that addrA is the program's rule is shown nowhere. "AttR0" is the
light part: the scores and the accumulators stand in "InTables". No case is shown in this file in
which a layer's weights are not 0 (one with values and an output projection in layer 0:
Johnson/Road/Lane5TrueLayerAt.lean). The library's model has no cell for a lookup's counts: in
"zsOf" the matrix that would hold them is 0, and the statements do not read it. No request at
weights that are not all 0 is named here. The library has such requests at the reference table
"Cm.sRef" alone; that X's table is that table is "scales_at_ref" (Johnson/Road/Lane5ScalesRef.lean),
which is not put in here: Johnson/Road/Lane5TrueGapAt.lean puts it in, at a request in which all 48
layers' weights are 0; at the library's request with layer 0 not zero: seam_layer_file,
Johnson/Road/Lane5TrueLayerAt.lean. That publicOf returns and that "Hd.PublicAt" and "attUsualK"
hold of any parameter file is a run's matter (Johnson/Road/Lane5AttSeamRun.lean), and so is that a
scale file has the words "scalesKF" (Johnson/Road/FormsKeysRunK.lean): no theorem. The runs are made
with no layout file; the theorems stand for every lay.

Not claimed: that a prover's committed cells are this list; that an honest prover's proof is
accepted (completeness of the protocol). It is a statement on integers and tables alone.

-/
import Johnson.Road.Lane5AttSeamAt
import Johnson.Road.Lane5AttSeamTrueL
import Johnson.Road.Lane5TopPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (ppref Instance Mat AcceptancePolicy NormPar)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **At the record's own plan: every true request's honest list meets both premises.** -/
theorem seam_of_true_publicAt (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (A : Hd.PublicAt X.P) (U : attUsualK X = true) (nf : NormPar)
    (hs : (scalesOf (Model.Verify.layerShape X.P) X.layers.sc nf).Lawful) {po : AcceptancePolicy}
    (hpol : Policy.PolCond po) {g : ℕ} (hg : g < 12) (i : Cm.Idx) (x : Instance ppref)
    (ht : Policy.IsTrueUnder (scalesOf (Model.Verify.layerShape X.P) X.layers.sc nf) po i x) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      AttR0 Ag.S (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf
        (scalesOf (Model.Verify.layerShape X.P) X.layers.sc nf) po) i x))) ∧
      (callsA Ag.S Ag.fs (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf
        (scalesOf (Model.Verify.layerShape X.P) X.layers.sc nf) po) i x)))).InTables := by
  have H := Hd.public_of_publicOf h A
  obtain ⟨Ag, lines, cf, hA, eS, hf, hh, hLam⟩ :=
    hid_of_public h H.p4 (g := g) (by rw [H.groups]; exact hg)
  obtain ⟨hc, h12, h8, hN⟩ := cfRef_of_fill hf (Hd.fillRef_of_at A H)
  have ec : (Hd.shapeA X g).cf = cf := by rw [← eS]; exact (shaped_of_hid hh).cfg
  have hU := (attUsualK_at U hg).1
  have hk := (attUsualK_at U hg).2
  rw [ec] at hU hk
  have hS := attSized_hid hh hc h12 h8
  exact ⟨Ag, hA, eS, seam_of_trueL hh hc hk h12 h8 (usual_of_test hU) hN hs hpol hg
    (hsh_of_fill hf (hLam.symm.trans hS.Lam) hg (Model.Verify.layerShape X.P) nf) i x ht⟩

/-- **The same where the scale file's words are those written out: the table is lawful.** -/
theorem seam_of_true_file (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (A : Hd.PublicAt X.P) (U : attUsualK X = true)
    (hW : Model.fileWords KL = scalesKF.toArray) {po : AcceptancePolicy} (hpol : Policy.PolCond po) {g : ℕ}
    (hg : g < 12) (i : Cm.Idx) (x : Instance ppref)
    (ht : Policy.IsTrueUnder (scalesOf (Model.Verify.layerShape X.P) X.layers.sc (Hd.npOf X.hS))
      po i x) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      AttR0 Ag.S (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf
        (scalesOf (Model.Verify.layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po) i x))) ∧
      (callsA Ag.S Ag.fs (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf
        (scalesOf (Model.Verify.layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po) i
        x)))).InTables :=
  seam_of_true_publicAt h A U (Hd.npOf X.hS) (lawful_of_at h A hW) hpol hg i x ht

/-- **At all weights 0: every request that has its form, with y = 0 if e = 1,024, at the list of its
own honest trace.** -/
theorem seam_zero_all_file (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (A : Hd.PublicAt X.P) (U : attUsualK X = true)
    (hW : Model.fileWords KL = scalesKF.toArray) {po : AcceptancePolicy} (hpol : Policy.PolCond po)
    (hθ : 257 ≤ po.theta) (hC : 257 ≤ po.C) {g : ℕ} (hg : g < 12) (x : Instance ppref)
    (h3 : Inst.Model.Head3 x) (hy0 : x.e = ppref.T → x.y.val = 0) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      AttR0 Ag.S (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf
        (scalesOf (Model.Verify.layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po)
        (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero) x))) ∧
      (callsA Ag.S Ag.fs (zsOf Ag.S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf
        (scalesOf (Model.Verify.layerShape X.P) X.layers.sc (Hd.npOf X.hS)) po)
        (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero) x)))).InTables :=
  seam_of_true_file h A U hW hpol hg (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero) x
    (Policy.TrueGuards.zero_all (lawful_of_at h A hW) po hθ hC x h3 hy0)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.seam_of_true_publicAt
#print axioms OnBytes.Road.L5.seam_of_true_file
#print axioms OnBytes.Road.L5.seam_zero_all_file
