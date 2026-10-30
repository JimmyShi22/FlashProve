-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadAtFullIs.lean: at the two named sets of public files the head's public
numbers are the records that Johnson/Desc/Kinds/Law/K06Condition.lean types by hand.

What the file holds. X: whatever publicOf returns on the named files, with or without the layout
file.
  shape_at_stored, shape_at_gap   the head's shape that is made of the scan of the parameter file
                   at the stored free numbers, and at the second set's: the typed record hFull,
                   field by field, but for lPd, which comes from the layers' layout.
  hS_at_full       **X.hS = Cond.hFull**, all 29 fields, at the stored full-size files
                   (VerifierAndGoals.storedPublicFiles).
  hS_at_gap        at the second named set (VerifierAndGoals.zGap): hFull with the policy (25856, 512, 1).
  border_in_scope  what the head reads of the layers' layout is Cond.bFull, at all files in scope.
  letters_in_scope the bits of work, the instances and the number of the array of reads are
                   Cond.workAt, Cond.instAt, Cond.readsAt, at all files in scope.
Why. K06Condition.lean states its record at numbers that were typed off a program's print
(k06Cond_full). HeadCondAtFiles.lean states the same record at what publicOf returns (head_at_full).
Here they are seen to speak of the same numbers. It also gives the
VALUES of the six free numbers at the stored files, as hFull has them: MF 44, KF 30, epsF 53687,
C 256, theta 256, cap 0.

What it does not give. THAT publicOf RETURNS ON THE NAMED FILES IS NO THEOREM (an evaluation alone:
see the head of HeadCondAtFiles.lean). The named files are the bytes written in Ladder/Stored.lean.
Nothing of the small record hSmall: the small files are outside the goals' scope. Nothing on
soundness.

-/
import Johnson.Goal.Meaning.HeadCondAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model.Verify (publicOf Public headShape borderOf)

set_option maxRecDepth 100000 in
theorem shape_at_stored (y : OnBytes.Model.Layer.Lay) :
    headShape (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines) y =
      { Cond.hFull with lPd := y.lPd } := by
  unfold headShape Cond.hFull
  simp only [OnBytes.Model.Head.Shape.mk.injEq]
  repeat' constructor

set_option maxRecDepth 100000 in
theorem shape_at_gap (y : OnBytes.Model.Layer.Lay) :
    headShape (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.Read.gapLines) y =
      { Cond.hFull with lPd := y.lPd, clipC := 25856, theta := 512, cap := 1 } := by
  unfold headShape Cond.hFull
  simp only [OnBytes.Model.Head.Shape.mk.injEq]
  repeat' constructor

variable {lay : Option ByteArray} {X : Public}

/-- **At the stored full-size files the head's shape is the typed record.** -/
theorem hS_at_full (h : publicOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL lay = .ok X) :
    X.hS = Cond.hFull := by
  obtain ⟨hZ, pp, hR, -⟩ := VerifierAndGoals.filesRead.full
  have hl : X.hS.lPd = 13 := (numbers_in_scope hZ hR h).lPd
  have hX := OnBytes.Road.Hd.scan_of_public h
  rw [VerifierAndGoals.pol_zFull] at hX
  have e := Meaning.HeadS.headShape_of_public h
  rw [VerifierAndGoals.Lines.scan_closed hX, shape_at_stored] at e
  rw [e] at hl
  rw [e, show X.y.lPd = 13 from hl]
  rfl

/-- At the second named set: the same with the second policy. -/
theorem hS_at_gap (h : publicOf VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL lay = .ok X) :
    X.hS = { Cond.hFull with clipC := 25856, theta := 512, cap := 1 } := by
  obtain ⟨hZ, pp, hR, -⟩ := VerifierAndGoals.filesRead.other
  have hl : X.hS.lPd = 13 := (numbers_in_scope hZ hR h).lPd
  have hX := OnBytes.Road.Hd.scan_of_public h
  rw [VerifierAndGoals.pol_zGap] at hX
  have e := Meaning.HeadS.headShape_of_public h
  rw [VerifierAndGoals.Lines.scan_closed hX, shape_at_gap] at e
  rw [e] at hl
  rw [e, show X.y.lPd = 13 from hl]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- A record with the typed record's six numbers is the typed record. -/
theorem border_is (b : OnBytes.Model.Head.Border) (h1 : b.mxb = 65536) (h2 : b.kxb = 400)
    (h3 : b.off = 0) (h4 : b.nl = 5) (h5 : b.cnt = 1) (h6 : b.J = 5120) : b = Cond.bFull := by
  cases b
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

theorem border_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : borderOf X.y = Cond.bFull :=
  have S := stream_in_scope hZ hR h
  border_is _ S.mxb S.kxb S.off S.nl S.cnt S.J

theorem letters_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    (OnBytes.Params.settingOf X.P.frame).workOf .field .request = Cond.workAt ∧
      (OnBytes.Params.settingOf X.P.frame).instances = Cond.instAt ∧
      X.H.tl.ix.U.getD 2 none = Cond.readsAt := by
  refine ⟨?_, rfl, ReadsNamed.public_third h⟩
  rw [Meaning.HeadS.frame_in_scope hZ hR h]
  exact work_ref

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.hS_at_full
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.hS_at_gap
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.border_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.letters_in_scope
