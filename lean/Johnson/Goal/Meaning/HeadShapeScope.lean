-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadShapeScope.lean: at all public files in the goals' scope: the head's shape
X.hS, every field by one equation; and the security lines X.P.frame.

  hS_in_scope: X.hS = headShape (scanAt frameRef (freeLinesOf pp)) X.y: headShape
    (OnBytes/Model/VerifyPublic.lean:49) reads the scan, which in scope is a written record but for
    the eight free numbers (Hd.scan_of_scope), and of the layers' layout the field lPd alone.
  d_in_scope, d_pos_in_scope: X.hS.d = 5120; 0 < X.hS.d.
  sizes_in_scope: lt = 10, la = 16, V = 202048, digSh = 8, tabS = 4, famF = 24, XL = 5.
  policy_in_scope: clipC, theta, cap, MF, KF are the free numbers that the goals' reader read.
  frame_in_scope: X.P.frame = VerifierAndGoals.Lines.frameRef.
-/
import Johnson.Goal.Meaning.HeadScope

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.HeadS

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Verify (publicOf Public headShape)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

theorem hS_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    X.hS = headShape (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef (VerifierAndGoals.freeLinesOf pp)) X.y := by
  rw [headShape_of_public h, Hd.scan_of_scope hZ hR h]

theorem d_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.hS.d = 5120 := by
  rw [hS_in_scope hZ hR h]
  rfl

theorem d_pos_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : 0 < X.hS.d := by
  rw [d_in_scope hZ hR h]
  decide

theorem sizes_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    X.hS.lt = 10 ∧ X.hS.la = 16 ∧ X.hS.V = 202048 ∧ X.hS.digSh = 8 ∧ X.hS.tabS = 4 ∧
      X.hS.famF = 24 ∧ X.hS.XL = 5 := by
  rw [hS_in_scope hZ hR h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem policy_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    X.hS.clipC = (VerifierAndGoals.freeLinesOf pp).C ∧ X.hS.theta = (VerifierAndGoals.freeLinesOf pp).theta ∧
      X.hS.cap = (VerifierAndGoals.freeLinesOf pp).cap ∧ X.hS.MF = (VerifierAndGoals.freeLinesOf pp).MF ∧
      X.hS.KF = (VerifierAndGoals.freeLinesOf pp).KF := by
  rw [hS_in_scope hZ hR h]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem frame_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.P.frame = VerifierAndGoals.Lines.frameRef := by
  rw [Hd.scan_of_scope hZ hR h]
  rfl

#print axioms hS_in_scope
#print axioms d_pos_in_scope
#print axioms sizes_in_scope
#print axioms policy_in_scope
#print axioms frame_in_scope

end Meaning.HeadS
