-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/PublicAtMeaning.lean: laws of four files under Johnson/Goal/Meaning/
(ScopeCore.lean, ScopeScanTies.lean, EmbScope.lean, Pub34Scope.lean) that take the premise
"`publicOf` returns X" (OnBytes/Model/VerifyPublic.lean), each once more at the text that takes the
second hash function as an argument o (`publicOfO o`, Johnson/Desc/Ok/PlanWritten/PublicAt.lean).

What is here. For each such declaration a twin: the statement and the proof are the library's, line
for line, with `publicOfO o` for `publicOf` and the twin's name for each called declaration that has
one (Johnson/Desc/Ok/PlanWritten/PublicAtBase.lean, PublicAtAbove.lean;
Johnson/Goal/Numbers/PublicAtBaseScope.lean; this file). A twin's name is the source file's name, a
dot, and the declaration's name with an O behind it. The twins were made by a program from the
library's text. They stand in the order in which they call one another. They stand here, apart from
their fellows, because their source files import the goals; and apart from those of
Johnson/Goal/Numbers/PublicAtMeaningPlans.lean [not in this library], so that no name of a later
file of the library is in sight where a statement of an earlier file is read again.

The twins: `ScopeCore.scan_of_publicO`, `ScopeCore.core_of_scopeO`, `ScopeScanTies.scan_of_scopeO`,
`Pub34Scope.shape_in_scopeO`, `EmbScope.lkW_of_scopeO`, `EmbScope.emb_public_in_scopeO`,
`Pub34Scope.scales_in_scopeO`, `Pub34Scope.cap_in_scopeO`, `ScopeScanTies.calls_of_scopeO`,
`Pub34Scope.linesAre_in_scopeO`, `Pub34Scope.floor_in_scopeO`, `Pub34Scope.pub34_publicO`,
`Pub34Scope.mats_of_publicO`, `Pub34Scope.tails_of_publicO`.

The statements are tools: where the scope is named it is the goals' own (`VerifierAndGoals.InScope`), as in
the library's statement; no description of the protocol is named. What of OnBytes/Model/ is used:
what the library's declarations use.

Limits. Which declarations are wanted was found by a program that follows the names in the proofs
downward from the laws that two other authors asked for; a law that nobody asked for has no twin
here. No theorem says that `publicOfO o` returns a value at any files in scope. Nothing on
soundness.
-/
import Johnson.Desc.Ok.PlanWritten.PublicAtAbove
import Johnson.Goal.Numbers.PublicAtBaseScope
import Johnson.Goal.Meaning.ScopeCore
import Johnson.Goal.Meaning.ScopeScanTies
import Johnson.Goal.Meaning.EmbScope
import Johnson.Goal.Meaning.Pub34Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.Hd
open OnBytes.Model (polScan PolScan hdrOf)
open OnBytes.Flat (otherLinesHeld otherLinesHeld_all otherLinesOf settingsAtRef_held)
open VerifierAndGoals (FreeLines policyFile)

/-- At o: The field P of what the verifier's `publicOf` returns is the strict scan of the parameter
file. -/
theorem ScopeCore.scan_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOfO o pol KL lay = .ok X) : polScan pol = .ok X.P := by
  obtain ⟨P, y, hpl, eP, -⟩ := HeadPub.public_partsO h
  unfold Model.Verify.polLayout at hpl
  obtain ⟨P0, hP, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨y0, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hpl
  rw [eP]
  exact hP

end

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.Hd
open OnBytes.Model (polScan PolScan hdrOf)
open OnBytes.Flat (otherLinesHeld otherLinesHeld_all otherLinesOf settingsAtRef_held)
open VerifierAndGoals (FreeLines policyFile)

/-- At o: **At all public files in the goals' scope the 41 numbers are the reference's**, in what
the verifier's own function returns on them, with or without the layout file. -/
theorem ScopeCore.core_of_scopeO {o : Nat → ByteArray → ByteArray}
    {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) : PublicCore X.P := by
  obtain ⟨S, hS, hh⟩ := settingsAtRef_held hR
  have hX := ScopeCore.scan_of_publicO h
  have e : S = X.P := Except.ok.inj (hS.symm.trans hX)
  rw [policy_of_scope hZ hR] at hX
  exact core_of_stored hX (e ▸ hh)

end

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.Hd
open OnBytes.Model (polScan PolScan hdrOf)
open VerifierAndGoals (FreeLines policyFile)

/-- At o: **At all public files in the goals' scope: the scan in what the verifier's `publicOf`
returns is the closed form at the free numbers that the goals' reader read.** -/
theorem ScopeScanTies.scan_of_scopeO {o : Nat → ByteArray → ByteArray}
    {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) :
    X.P = VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef (VerifierAndGoals.freeLinesOf pp) := by
  have hX := ScopeCore.scan_of_publicO h
  rw [policy_of_scope hZ hR] at hX
  exact VerifierAndGoals.Lines.scan_closed hX

end

section
open _root_.Meaning _root_.Meaning.P34
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: THE PLAN's SHAPE IS THE HAND-WRITTEN hKF (Johnson/Road/FormsKeysRunK.lean:276) but for the
three free numbers eps1, eps2, epsF, which are those that the goals' reader read. -/
theorem Pub34Scope.shape_in_scopeO {o : Nat → ByteArray → ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) :
    layerShape X.P = { hKF with
      eps1 := (VerifierAndGoals.freeLinesOf pp).eps1, eps2 := (VerifierAndGoals.freeLinesOf pp).eps2,
      epsF := (VerifierAndGoals.freeLinesOf pp).epsF } := by
  have hX := ScopeCore.scan_of_publicO h
  rw [Hd.policy_of_scope hZ hR] at hX
  obtain ⟨e1, -, -, e4, -, -, -⟩ := VerifierAndGoals.Lines.hdr_free hX
  have e : layerShape X.P = { hKF with
      eps1 := X.P.h.eps.getD 0 0, eps2 := X.P.h.eps.getD 1 0, epsF := X.P.h.epsF } := by
    rw [ScopeScanTies.scan_of_scopeO hZ hR h]
    exact shape_of_closed _
  rw [e, e1, e4]
  rfl

end

section
open _root_.Meaning _root_.Meaning.Emb
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv Lay Shape layout layoutBase)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (embR)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: At all public files in the goals' scope the number of column bits is the library's. -/
theorem EmbScope.lkW_of_scopeO {o : Nat → ByteArray → ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) : X.P.lkW = kRef := by
  rw [ScopeScanTies.scan_of_scopeO hZ hR h]
  exact lkW_ref

end

section
open _root_.Meaning _root_.Meaning.Emb
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv Lay Shape layout layoutBase)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (embR)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: THE FOUR PUBLIC PREMISES, at all public files in the goals' scope. -/
theorem EmbScope.emb_public_in_scopeO {o : Nat → ByteArray → ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) :
    EmbNums X.y ∧ SizedW (weightShape X.P X.y) ppref ∧
      wsLayOf (weightShape X.P X.y) true kRef = .ok X.layers.wsLay ∧ X.layers.V = ppref.V := by
  have A := ScopeCore.core_of_scopeO hZ hR h
  have B := HeadMade.publicH_of_publicO h
  have hp3 := (Hd.switches_of_core A).p3
  obtain ⟨eh, -⟩ := laid_of_layout B.lay hp3
  have hws := B.ws
  rw [eh, hp3, EmbScope.lkW_of_scopeO hZ hR h] at hws
  exact ⟨embNums_of_layout B.lay hp3 (A.num 2) (A.num 4), sizedW_of_core A B.lay, hws,
    (PlanV.publicOf_VO h).trans (A.num 11)⟩

end

section
open _root_.Meaning _root_.Meaning.P34
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: hs. -/
theorem Pub34Scope.scales_in_scopeO {o : Nat → ByteArray → ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) :
    scalesHeld (layerShape X.P) X.layers.sc = .ok () := by
  have A := ScopeCore.core_of_scopeO hZ hR h
  have B := HeadMade.publicH_of_publicO h
  obtain ⟨eh, -⟩ := laid_of_layout B.lay (Hd.switches_of_core A).p3
  rw [← eh]
  exact HeadL5Grp.scalesHeld_of_publicO h

end

section
open _root_.Meaning _root_.Meaning.P34
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: hc. -/
theorem Pub34Scope.cap_in_scopeO {o : Nat → ByteArray → ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) : DF.cap = (layerShape X.P).lidb := by
  rw [ScopeScanTies.scan_of_scopeO hZ hR h]
  rfl

end

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.Hd
open OnBytes.Model (polScan PolScan hdrOf)
open VerifierAndGoals (FreeLines policyFile)

/-- At o: So its call lines are the stored example's. -/
theorem ScopeScanTies.calls_of_scopeO {o : Nat → ByteArray → ByteArray}
    {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) :
    X.P.polCalls = VerifierAndGoals.Lines.callsRef ∧ X.P.polCallsA = VerifierAndGoals.Lines.callsARef ∧
      X.P.polCallsH = VerifierAndGoals.Lines.callsHRef := by
  rw [ScopeScanTies.scan_of_scopeO hZ hR h]
  exact ⟨rfl, rfl, rfl⟩

end

section
open _root_.Meaning _root_.Meaning.P34
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: hN. -/
theorem Pub34Scope.linesAre_in_scopeO {o : Nat → ByteArray → ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) : LinesAre X.y := by
  have B := HeadMade.publicH_of_publicO h
  have hc := (ScopeScanTies.calls_of_scopeO hZ hR h).1
  have hl := B.lay
  rw [hc] at hl
  unfold LinesAre
  rw [lines_of_layout hl rfl]
  exact callsRef_lines

end

section
open _root_.Meaning _root_.Meaning.P34
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: hfl. -/
theorem Pub34Scope.floor_in_scopeO {o : Nat → ByteArray → ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) : ∀ k : Fin 8,
    (layerShape X.P).nmin - (layerShape X.P).ll - (layerShape X.P).lt ≤
      Nat.clog 2 (used DF k) := by
  have A := ScopeCore.core_of_scopeO hZ hR h
  have e1 : (layerShape X.P).ll = 2 := A.num 3
  have e2 : (layerShape X.P).lt = 10 := A.num 1
  have e3 : (layerShape X.P).nmin = 20 := by
    rw [ScopeScanTies.scan_of_scopeO hZ hR h]
    rfl
  rw [e1, e2, e3]
  exact floor_ref

end

section
open _root_.Meaning _root_.Meaning.P34
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: THE PUBLIC FIELDS OF Pub34, at all public files in the goals' scope, in the record's own
names: hy · S · hs · hrd · Z · hc · hN · hfl · Zw · hsL · hlw · h4. -/
theorem Pub34Scope.pub34_publicO {o : Nat → ByteArray → ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOfO o Z.pol Z.KL lay = .ok X) :
    layout (layerShape X.P) X.P.polCalls = .ok X.y ∧ Switches (layerShape X.P) ∧
      scalesHeld (layerShape X.P) X.layers.sc = .ok () ∧ readsOf X.y = .ok X.layers.rd ∧
      Sized (layerShape X.P) DF ∧ DF.cap = (layerShape X.P).lidb ∧ LinesAre X.y ∧
      (∀ k : Fin 8, (layerShape X.P).nmin - (layerShape X.P).ll - (layerShape X.P).lt ≤
        Nat.clog 2 (used DF k)) ∧
      SizedW (weightShape X.P X.y) DF.P ∧ (weightShape X.P X.y).L = (layerShape X.P).L ∧
      wsLayOf (weightShape X.P X.y) true kRef = .ok X.layers.wsLay ∧
      (layerShape X.P).p4 = true := by
  have A := ScopeCore.core_of_scopeO hZ hR h
  have H := PublicCore.public_of_coreO h A
  obtain ⟨-, S, W, -⟩ := EmbScope.emb_public_in_scopeO hZ hR h
  exact ⟨H.lay, H.switches, Pub34Scope.scales_in_scopeO hZ hR h, (Pub34Scope.more_of_publicO h).1,
      H.sized,
    Pub34Scope.cap_in_scopeO hZ hR h, Pub34Scope.linesAre_in_scopeO hZ hR h,
        Pub34Scope.floor_in_scopeO hZ hR h, S, rfl, W, H.p4⟩

end

section
open _root_.Meaning _root_.Meaning.P34
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: hmats: the rows and columns of the matrices that the check of group g takes from the
public record are matsR. -/
theorem Pub34Scope.mats_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL lay = .ok X) (g : ℕ) :
    ((X.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR X.y g := by
  rw [(Pub34Scope.more_of_publicO h).2.1]
  rfl

end

section
open _root_.Meaning _root_.Meaning.P34
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At o: htm | hNM, for the plan of every group: the library's plan_sizes at X's own plans. No
premise on the files but that publicOf returns. -/
theorem Pub34Scope.tails_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL lay = .ok X) {g : ℕ} {hp : Layer.HPlan2} (hg : X.G[g]? = some hp) :
    (hp.tl.mats.map fun M => (M.m, M.k)) = matsR X.y g ∧ hp.tl.NM = hp.tl.mats.size := by
  obtain ⟨-, -, -, hP, hG⟩ := Pub34Scope.more_of_publicO h
  exact plan_sizes hP hG hg

end

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.ScopeCore.scan_of_publicO
#print axioms VerifiableInference.PlanWritten.ScopeCore.core_of_scopeO
#print axioms VerifiableInference.PlanWritten.ScopeScanTies.scan_of_scopeO
#print axioms VerifiableInference.PlanWritten.Pub34Scope.shape_in_scopeO
#print axioms VerifiableInference.PlanWritten.EmbScope.lkW_of_scopeO
#print axioms VerifiableInference.PlanWritten.EmbScope.emb_public_in_scopeO
#print axioms VerifiableInference.PlanWritten.Pub34Scope.scales_in_scopeO
#print axioms VerifiableInference.PlanWritten.Pub34Scope.cap_in_scopeO
#print axioms VerifiableInference.PlanWritten.ScopeScanTies.calls_of_scopeO
#print axioms VerifiableInference.PlanWritten.Pub34Scope.linesAre_in_scopeO
#print axioms VerifiableInference.PlanWritten.Pub34Scope.floor_in_scopeO
#print axioms VerifiableInference.PlanWritten.Pub34Scope.pub34_publicO
#print axioms VerifiableInference.PlanWritten.Pub34Scope.mats_of_publicO
#print axioms VerifiableInference.PlanWritten.Pub34Scope.tails_of_publicO
