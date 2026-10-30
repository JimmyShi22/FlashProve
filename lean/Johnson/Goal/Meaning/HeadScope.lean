-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadScope.lean: the head's joint: at all public files in the goals' scope, the
library's record on the head's sub-proof (Hd.HeadOrdLB, Johnson/Road/HeadL5BL.lean) follows from two
named relations at the head's own list, with no premise on public data left.

The theorem headBridge_of_test (Johnson/Road/Ends/HeadInSeamPub.lean:52) has the bridge under one
test on public data, headPubB. That test asks PublicAt, all 46 numbers of the parameter file: five
of them (eps1, eps2, MF, KF, epsF) are free in the goals' scope, so the test is not true at all
files there.
Its proof spends PublicAt only on the record LayersHeadAt, which the 41 numbers of the public core
give as well (public_of_core, Johnson/Meaning/PublicCore.lean).
  headShape_of_public: X.hS is headShape X.P X.y.
  famF_in_scope, border_in_scope: F = 24; the stream has five limbs.
  headBridge_in_scope: the bridge (L5.HeadBridge, Johnson/Road/Lane5SplitH.lean) at X's own letters,
    at the final normalisation npOf X.hS and the weights' layout X.layers.wsLay: for every run's
    record R with the head's shape and layout of X at which ReqFits holds.
  headOrd_in_scope: so HeadR0 and InTables, at the calls callsH R (borderOf X.y) X.layers.wsLay Mh
    Wz, give Hd.HeadOrdLB X.hS X.HLy X.y (npOf X.hS) pl Wz x Mh.
Premises that stay: R.h = X.hS, R.L = X.HLy, and ReqFits: it speaks of a request and of the run's
covered positions (reqFits_of_instance, Johnson/Road/HeadLaid.lean:380, pays it for an instance with
the request file's tokens).
Not claimed: HeadR0 or InTables of anything; all that Johnson/Road/Ends/HeadInSeam.lean does not
claim.
-/
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Road.Ends.HeadInSeam
import Johnson.Road.Lane5SplitH
import Johnson.Road.FormsKeysLawP

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.HeadS

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf Public borderOf weightShape headShape layerShape)
open Inst.Model (Mat ppref AcceptancePolicy Instance)

/-- The head's shape in the public part. -/
theorem headShape_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) : X.hS = headShape X.P X.y := by
  obtain ⟨P, y, -, eP, ey, eS, -⟩ := Hd.public_parts h
  rw [eS, eP, ey]

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

theorem famF_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.hS.famF = 24 := by
  rw [headShape_of_public h]
  show X.P.h.famF = 24
  rw [Hd.scan_of_scope hZ hR h]
  rfl

theorem border_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : (borderOf X.y).nl = 5 := by
  have B := Hd.public_of_core h (Hd.core_of_scope hZ hR h)
  show X.y.xb.nl = 5
  rw [(laid_of_layout B.lay B.switches.p3).2.xb]
  show X.y.h.xl = 5
  rw [shape_of_public h, P34.shape_in_scope hZ hR h]
  rfl

/-- THE BRIDGE AT THE HEAD, at all public files in the goals' scope. -/
theorem headBridge_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {R : Head.Run} (e1 : R.h = X.hS) (e2 : R.L = X.HLy)
    {pl : AcceptancePolicy} {x : Instance ppref}
    (Rq : Hd.ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pl x)) (Wz : Mat) (Mh : Mats ℤ) :
    HeadBridge X.hS X.HLy X.y (Hd.npOf X.hS) pl Wz x Mh
      (Hd.callsH R (borderOf X.y) X.layers.wsLay Mh Wz) := by
  have B := Hd.public_of_core h (Hd.core_of_scope hZ hR h)
  obtain ⟨-, -, -, -, -, -, -, -, Zw, -, hlw, -⟩ := P34.pub34_public hZ hR h
  have hy : Head.layout R.h Hd.tauFCw = .ok R.L := by
    rw [e1, e2, ← Hd.tauFC_of_layout B.lay]
    exact B.head
  have key := Hd.headBridge_of_layout (R := R) hy (by rw [e1]; exact B.full)
    (by rw [e1]; exact famF_in_scope hZ hR h) (by rw [e1]; exact B.sT) (by rw [e1]; exact B.sh)
    (np := Hd.npOf X.hS) (by rw [e1]; rfl) (y := X.y) (border_in_scope hZ hR h) Zw hlw Rq Wz Mh
  rw [e1, e2] at key
  exact key

/-- THE HEAD's JOINT. -/
theorem headOrd_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {R : Head.Run} (e1 : R.h = X.hS) (e2 : R.L = X.HLy)
    {pl : AcceptancePolicy} {x : Instance ppref}
    (Rq : Hd.ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pl x)) {Wz : Mat} {Mh : Mats ℤ}
    (R0 : HeadR0 X.hS X.HLy X.y (Hd.npOf X.hS) pl x Mh)
    (I : (Hd.callsH R (borderOf X.y) X.layers.wsLay Mh Wz).InTables) :
    Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) pl Wz x Mh :=
  headOrdLB_iff_split.2 ⟨R0, headBridge_in_scope hZ hR h e1 e2 Rq Wz Mh I⟩

#print axioms famF_in_scope
#print axioms border_in_scope
#print axioms headBridge_in_scope
#print axioms headOrd_in_scope

end Meaning.HeadS
