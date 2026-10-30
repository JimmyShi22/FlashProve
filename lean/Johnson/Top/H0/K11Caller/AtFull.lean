-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/AtFull.lean: the merge's record at the head's place, at the full size's numbers: what the proved block and this folder's theorems ask there is met.

The proved block (Cb/Pv/Lay/Weights.lean) asks of whoever fills its record that each summand has degree at most 2 in each variable; this folder's theorems ask, beside, that the claim is on the place's
unit, passes wsClaimShape, and that the unit has OnBytes.Road.UnitOK. Here, at every shape of the weights that agrees with the library's reference parameters (SizedW s ppref) and every layout that
wsLayOf returns with the library's 18 column bits:
    headPlace         the place: that layout; one claim; on the last unit
    headClaim_shape   the head's claim (headClaim, HeadSays.lean) passes wsClaimShape, if AV has one member for each entry of the vocabulary and rs at least 13
    head_fit          so ClaimsFit (Items.lean) holds at the place, whatever the ledger
    K11Condition, k11Condition   one closed proposition, and its proof: the place exists; it has 18 column bits and one claim; at the library's field Cb.Gl.E and all letters the record's summand has degree at most 2
                      in each variable and the sumcheck's four conditions of the library hold (MergeL.conds); ClaimsFit holds at every head's claim of these sizes
    full_returns, full_member    it is not empty: at the full-size example's shape, written out (shapeV hKF 202048, Johnson/Road/FormsKeysRunWK.lean), wsLayOf returns (by the kernel's evaluation), and
                      that shape agrees with the reference parameters (sizedW_KF)
SPENT OF THE LIBRARY: OnBytes.Road.Hd.head_unit, units_head (Johnson/Road/HeadWeight.lean) · OnBytes.Road.layout_eq, the fields of SizedW (Johnson/Road/FormsKeysWLay.lean) · OnBytes.Road.eqTab_size
(Johnson/Road/FormsKeysEq.lean) · OnBytes.Road.sizedW_KF (Johnson/Road/FormsKeysRunWK.lean) · Cb.Pv.Lay.MergeL.conds (Cb/Pv/Lay/Merge.lean) · the two facts behind the field Cb.Gl.E's instances: on pure functions and plain records.
Limits: the head's place alone (one claim); the layers' places (32 and 33 claims) are not treated. The numbers of the slots (Nums, AtSlots.lean) stay letters: that a plan's numbers meet their three bounds is
not shown. That a file's shape of the weights is the written one is not shown. Nothing on the errors (Rounds.lean). On hiding nothing.

-/
import Johnson.Top.H0.K11Caller.Items
import Johnson.Top.H0.K11Caller.HeadSays
import Johnson.Road.FormsKeysRunWK

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes
open OnBytes.Model (WsShape WsLay WsClaim WsFac Fork wsLayOf wsClaimShape eqLow eqTab)
open OnBytes.Road (SizedW shapeOf placeP shapeV hKF sizedW_KF)
open OnBytes.Road.Hd (facKK head_unit askH units_head)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.Head (nV nD)

section
variable {s : WsShape} {lay : WsLay}

theorem head_size (Z : SizedW s ppref) (h : wsLayOf s true kRef = .ok lay) : lay.U.size = 386 :=
  (OnBytes.Road.layout_eq Z h).2.1.trans units_head.1

/-- **The head's place.** -/
def headPlace (Z : SizedW s ppref) (h : wsLayOf s true kRef = .ok lay) : Place :=
  Place.ofLay lay h 1 fun _ => ⟨lay.U.size - 1, by rw [head_size Z h]; decide⟩

/-- **The head's claim passes the program's test on a claim's sizes.** -/
theorem headClaim_shape (Z : SizedW s ppref) (h : wsLayOf s true kRef = .ok lay) (AV rs : Array E) (hA : AV.size = nV) (hs : 13 ≤ rs.size) :
    wsClaimShape lay (headClaim lay AV rs) = .ok () := by
  obtain ⟨o, hu⟩ := head_unit h
  have hd : (shapeOf s true).d = 5120 := Z.d
  have hV : (shapeOf s true).V = 202048 := Z.V
  have hH : ((eqLow rs 10 13).extract 0 5).size = 5 := by
    have e : (eqLow rs 10 13).size = 8 := by
      unfold eqLow
      rw [OnBytes.Road.eqTab_size]
      have : (rs.extract 10 13).reverse.size = 3 := by
        simp
        omega
      rw [this]
      rfl
    simp [e]
  unfold wsClaimShape headClaim
  simp only [hu]
  unfold OnBytes.Road.unitP askH
  rw [hd, hV]
  have hA' : AV.size = 202048 := hA
  simp [placeP, OnBytes.Road.yP, WsFac.fits, facKK, WsLay.A_, WsLay.E_, hA', hH]
  decide

/-- So what Items.lean asks of the claims holds at the head's place. -/
theorem head_fit (Z : SizedW s ppref) (h : wsLayOf s true kRef = .ok lay) (AV rs : Array E) (hA : AV.size = nV) (hs : 13 ≤ rs.size) (F : Fork) :
    ClaimsFit (headPlace Z h) ⟨fun _ => headClaim lay AV rs, F⟩ where
  ui := fun _ => rfl
  shape := fun _ => headClaim_shape Z h AV rs hA hs
  unit := fun _ u hu => ofLay_unit h _ u hu

end

/-- **The row, as one closed proposition.** -/
def K11Condition : Prop :=
  ∀ (s : WsShape) (lay : WsLay), SizedW s ppref → wsLayOf s true kRef = .ok lay →
    ∃ P : Place, P.lay = lay ∧ P.n = 1 ∧ P.lay.lk = 18 ∧ (∀ a, P.ui a = lay.U.size - 1) ∧
      (∀ (T : Letters Cb.Gl.E P), (∀ a st m, Alg.DegLE (fun _ : Fin P.lay.lk => 2) ((G P T).fa a st m)) ∧
        ((G P T).L.T.VarsOK ∧ (G P T).L.T.ValInj ∧ (G P T).L.T.DegX ∧ (G P T).L.T.DegY)) ∧
      ∀ (AV rs : Array E) (F : Fork), AV.size = nV → 13 ≤ rs.size → ClaimsFit P ⟨fun _ => headClaim lay AV rs, F⟩

theorem k11Condition : K11Condition := fun _ _ Z h =>
  ⟨headPlace Z h, rfl, rfl, (head_rows Z h).2, fun _ => rfl, fun T => ⟨G_deg _ T, (G _ T).L.conds⟩,
    fun AV rs F hA hs => head_fit Z h AV rs hA hs F⟩

/-- An Except's «it returned», as a Bool. -/
def okB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

set_option maxRecDepth 100000 in
/-- At the full-size example's shape wsLayOf returns: by the kernel's evaluation. -/
theorem full_returns : okB (wsLayOf (shapeV hKF 202048) true kRef) = true := by decide +kernel

/-- **The row is not empty.** -/
theorem full_member : ∃ lay, SizedW (shapeV hKF 202048) ppref ∧ wsLayOf (shapeV hKF 202048) true kRef = .ok lay := by
  have h := full_returns
  cases e : wsLayOf (shapeV hKF 202048) true kRef with
  | error x =>
    rw [e] at h
    exact absurd h Bool.false_ne_true
  | ok lay => exact ⟨lay, sizedW_KF, rfl⟩

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.headClaim_shape
#print axioms VerifiableInference.Desc.First.K11Caller.k11Condition
#print axioms VerifiableInference.Desc.First.K11Caller.full_member
