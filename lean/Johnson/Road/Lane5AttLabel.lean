-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttLabel.lean

The label of the attention sub-proof's copy of qa. The verifier's plans give each matrix of a list a
label (the field aId of a record TMat); a matrix that a sub-proof borrows bears its owner's label.

* "matrices_qa": in the list of matrices of an attention sub-proof
  (OnBytes/Model/AttentionPlan.lean: matrices), number NAs + 3 is qa, of kind 1, with the label midQ
  that the caller passed.
* "plan_mats": the list in the plan that the function plan returns is that list, but for two fields
  (foreign, ttOff) of the matrix of kind 1.
* "plan_label_qa": so number NAs + 3 of the plan's own list bears the label X.inp.midQ.
* "midQ_lab": the label that the caller of OnBytes/Model/VerifyPublic.lean passes for group g (the
  label of number iQA in the list of the layer sub-proof of group g) is the one that the layers'
  formula labA (Johnson/Road/FormsKeysDictA.lean) gives.
* "group_label_qa": both together, for the plan that the function group returns on that caller's
  midQ.

What is compared with what: texts of the verifier with each other, and with the formula labA of
these files. Not claimed: that a matrix which bears another sub-proof's label is the matrix to which
the owner committed; what publicOf does to a plan's list behind group (it replaces seam.tl).
-/
import Johnson.Road.Lane5AttPlan
import Johnson.Road.FormsKeysPlan
import Johnson.Road.FormsKeysDictA

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Model (TMat)
open OnBytes.Model.Layer (Lay tailsOf matIx)

/-- A member of the second of two arrays that are joined. -/
theorem append_at {α : Type} (l : List α) (b : Array α) {n : ℕ} (j : ℕ) (h : l.length = n) :
    (l.toArray ++ b)[n + j]? = b[j]? := by
  subst h
  rw [Array.getElem?_append_right (by simp)]
  simp

/-- **Number NAs + 3 of the list is qa, with the label that the caller passed.** -/
theorem matrices_qa (S : Attention.Shape) (i : Attention.In) :
    (Attention.matrices S i)[S.cf.NAs + 3]? =
      some { name := "qa", m := S.cf.wcQ * S.T, k := S.fillQ / S.cf.wcQ, kind := 1,
             foreign := some 0, aId := i.midQ, wp := i.wpq } := by
  unfold Attention.matrices
  exact (append_at _ _ 3 (by simp)).trans (by simp)

/-- What Seam.shape does to a matrix of the list. -/
def fixed (M : TMat) : TMat := if M.kind == 1 then { M with foreign := some 0, ttOff := 0 } else M

theorem fixed_aId (M : TMat) : (fixed M).aId = M.aId := by
  unfold fixed
  split <;> rfl

theorem seamShape_mats {g : Model.Settings} {m : Array TMat} {tau col0F ktO aO : ℕ}
    {s : Attention.Seam} (h : Attention.Seam.shape g m tau col0F ktO aO = Except.ok s) :
    s.tl.mats = m.map fixed := by
  unfold Attention.Seam.shape at h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨tl, ht, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact (shape_mats ht).1

theorem seamPlan_mats {s s' : Attention.Seam} {nU3 hb hbLine : ℕ}
    (h : s.plan nU3 hb hbLine = Except.ok s') : s'.tl.mats = s.tl.mats := by
  unfold Attention.Seam.plan at h
  obtain ⟨r, hr, h⟩ := bind_ok h
  have k := (addTrees_keeps hr).1
  obtain ⟨tl, Fp, T⟩ := r
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨Tp, -, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact k

/-- **The plan's own list.** -/
theorem plan_mats {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {X : Attention.Plan} (h : Attention.plan settings i cf = Except.ok X) :
    X.seam.tl.mats = (Attention.matrices X.S X.inp).map fixed := by
  unfold Attention.plan at h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨S, fs⟩ := r
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam0, h0, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam, h1, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact (seamPlan_mats h1).trans (seamShape_mats h0)

/-- **Number NAs + 3 of the plan's own list bears the label that the caller passed.** -/
theorem plan_label_qa {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {X : Attention.Plan} (h : Attention.plan settings i cf = Except.ok X) :
    (X.seam.tl.mats[X.S.cf.NAs + 3]?).map (fun M => M.aId) = some X.inp.midQ := by
  rw [plan_mats h, Array.getElem?_map, matrices_qa]
  rfl

/-- The label that the caller passes for group g is the one that the layers' formula gives. -/
theorem midQ_lab (y : Lay) {g : ℕ} (hg : g < y.NGr) :
    (((tailsOf y).getD g {}).mats.getD (matIx y).iQA {}).aId = labA y g (matIx y).iQA :=
  labA_tails y hg (by
    show y.parts.getD 0 0 + y.parts.getD 1 0 + 2 < y.parts.getD 0 0 + y.parts.getD 1 0 + 5
    omega)

/-- **In the plan of group g, on the caller's midQ, the copy of qa bears the label that the layers'
formula gives the matrix qa of group g.** -/
theorem group_label_qa {P : Model.PolScan} {y : Lay} {sc : Model.Layer.Scales}
    {lines : List Attention.Line} {g : ℕ} {X : Attention.Plan}
    (h : Attention.group P y sc
      (fun g => (((tailsOf y).getD g {}).mats.getD (matIx y).iQA {}).aId) lines g = Except.ok X)
    (hg : g < y.NGr) :
    (X.seam.tl.mats[X.S.cf.NAs + 3]?).map (fun M => M.aId) = some (labA y g (matIx y).iQA) := by
  obtain ⟨cf, -, hp, -⟩ := group_plan h
  rw [plan_label_qa hp, (plan_shape hp).2]
  exact congrArg some (midQ_lab y hg)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.matrices_qa
#print axioms OnBytes.Road.L5.plan_mats
#print axioms OnBytes.Road.L5.group_label_qa
