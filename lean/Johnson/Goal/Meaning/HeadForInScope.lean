-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadForInScope.lean: the head's joint both ways, at the lookup's own clause, at
all public files in the goals' scope; and the least logarithm of the number of keys of a call of the
head.

  headOrd_iff_in_scope: Hd.HeadOrdLB at X's own letters holds if and only if HeadR0 holds and the
    clause Hd.ForInH holds (Johnson/Road/Ends/HeadForIn.lean:73: what the typed lookup asks of its
    caller's key vectors, at the record's own numbers and rows), at the key vectors of
    callsH R (borderOf X.y) X.layers.wsLay Mh Wz. By headOrdLB_iff_split and
    headKeys_iff_forIn (Johnson/Road/Ends/HeadBack.lean:219), under the ten premises that
    headBridge_in_scope (Johnson/Goal/Meaning/HeadScope.lean) pays: headOrd_iff_forIn
    (:226) at X's letters. The key vectors are the library's kvH.
  headKeys_iff_in_scope: the clause on keys alone: HeadKeys if and only if ForInH.
  keyFloor_in_scope: Head.keyFloor X.hS = 27.
No test on public data is asked. Premises that stay: the three facts on the files (that publicOf
returns among them); R.h = X.hS, R.L = X.HLy, ReqFits.
-/
import Johnson.Goal.Meaning.HeadScope
import Johnson.Road.Ends.HeadBack

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.HeadS

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf Public borderOf)
open Inst.Model (Mat ppref AcceptancePolicy Instance)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- The clause on the head's keys is the lookup's own clause. -/
theorem headKeys_iff_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {R : Head.Run} (e1 : R.h = X.hS) (e2 : R.L = X.HLy)
    {pl : AcceptancePolicy} {x : Instance ppref}
    (Rq : Hd.ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pl x)) (Wz : Mat) (Mh : Mats ℤ) :
    HeadKeys X.hS X.HLy X.y (Hd.npOf X.hS) pl Wz x Mh ↔
      Hd.ForInH R (Hd.callsH R (borderOf X.y) X.layers.wsLay Mh Wz).K := by
  have B := Hd.public_of_core h (Hd.core_of_scope hZ hR h)
  obtain ⟨-, -, -, -, -, -, -, -, Zw, -, hlw, -⟩ := P34.pub34_public hZ hR h
  have hy : Head.layout R.h Hd.tauFCw = .ok R.L := by
    rw [e1, e2, ← Hd.tauFC_of_layout B.lay]
    exact B.head
  have key := Hd.headKeys_iff_forIn (R := R) hy (by rw [e1]; exact B.full)
    (by rw [e1]; exact famF_in_scope hZ hR h) (by rw [e1]; exact B.sT) (by rw [e1]; exact B.sh)
    (np := Hd.npOf X.hS) (by rw [e1]; rfl) (y := X.y) (border_in_scope hZ hR h) Zw hlw Rq Wz Mh
  rw [e1, e2] at key
  exact key

/-- THE HEAD's JOINT, BOTH WAYS, AT THE LOOKUP's OWN CLAUSE. -/
theorem headOrd_iff_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {R : Head.Run} (e1 : R.h = X.hS) (e2 : R.L = X.HLy)
    {pl : AcceptancePolicy} {x : Instance ppref}
    (Rq : Hd.ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pl x)) (Wz : Mat) (Mh : Mats ℤ) :
    Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) pl Wz x Mh ↔
      HeadR0 X.hS X.HLy X.y (Hd.npOf X.hS) pl x Mh ∧
        Hd.ForInH R (Hd.callsH R (borderOf X.y) X.layers.wsLay Mh Wz).K :=
  headOrdLB_iff_split.trans
    (and_congr_right fun _ => headKeys_iff_in_scope hZ hR h e1 e2 Rq Wz Mh)

/-- The least logarithm of the number of keys of a call of the head. -/
theorem keyFloor_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : Head.keyFloor X.hS = 27 := by
  rw [headShape_of_public h, Hd.scan_of_scope hZ hR h]
  rfl

#print axioms headShape_of_public
#print axioms headKeys_iff_in_scope
#print axioms headOrd_iff_in_scope
#print axioms keyFloor_in_scope

end Meaning.HeadS
