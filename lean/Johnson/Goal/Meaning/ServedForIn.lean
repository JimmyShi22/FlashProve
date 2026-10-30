--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Meaning/ServedForIn.lean: at a request that can be served, the clauses ForInG, ForInA
and ForInH hold at the numbers and rows of the verifier's own records: for the lookups on the calls
of the twelve groups of layers and of the twelve attention sub-proofs; for the head's at every run
record that fits the request. A theorem on integers, on the library's key vectors and on the
records' tables; it names no block of the protocol's description.

Why. means_of_served (Johnson/Goal/Meaning/ServedMeans.lean) ends in Means and Hd.HeadOrdLB, whose
clauses on keys stand at the library's tables. What a lookup asks of its caller stands at the
record's own numbers n, k and rows: Alg.ForInG (Johnson/Road/Lane5ForInG.lean), ForInA
(Johnson/Road/Lane5ForIn.lean), Hd.ForInH (Johnson/Road/Ends/HeadForIn.lean): for every call, the
caller's key vector lies in the table whose rows are read off the record. For attention and the head
the way between the two is landed in scope, both ways. For the layers it is landed in scope in one
direction (layerKeys_of_scope, Johnson/Goal/Meaning/WeighedScope.lean): here is the other.

Main names.
  P34.forInG_iff_keys_in_scope   the layers' clause ForInG is the group's lookup clause LayerKeys,
    under the three facts on the files and g < 12 alone.
  P34.forInG_of_means, Att.forInA_of_means   from Means.
  HeadS.forInH_of_ord   from the head's record.
    These three take Means (or the head's record) as a letter: whoever holds one w gets the clauses
    at that w. They end unlike: attention's keeps AttR0; the head's drops HeadR0; the layers' has no
    LayerR0: Means holds the rest.
  HeadS.head_record_met   the three premises on the head's run record R are met together.
  forIn_of_served   THE STATEMENT: at a request that can be served, ONE x, w, Mh with the whole end
    of means_of_served AND the three clauses.

It adds no strength: compositions of landed links. Alg.forInG_iff_keys
(Johnson/Road/Lane5KeysIffG.lean), its public premises paid as layerKeys_in_scope
(Johnson/Goal/Meaning/ForInScope.lean) pays them, with hl_in_scope (HlScope.lean) and
weighed_in_scope (WeighedScope.lean); attOrd_iff_forIn_in_scope (AttForInScope.lean);
headOrd_iff_in_scope (HeadForInScope.lean); Hd.reqFits_runReq, Hd.blankRun
(Johnson/Road/Ends/HeadWit.lean).

Every "there is", walked: as in ServedMeans.lean: x is pinned by requestOfTokens; w and Mh by
nothing but the clauses.

Limits. NO LAW OF THE DESCRIPTION's KINDS NAMES THESE THREE CLAUSES: no file under Johnson/Desc
does. What stands in front of the description's lookup at a layers' segment is the right side of
lay_says (Johnson/Desc/First/Look/K3CallerLay.lean), at the library's keyVec and the readings
Port.nOf, Port.kOf, FoNums.tauN: ForInG has its shape and stands four terms off. The landed files'
own: the key vectors kvG, kvA, kvH are terms of this library over the verifier's records, no
functions of the verifier's ("no such caller is written in this library",
Johnson/Road/Lane5ForInG.lean); the readings nF, kN, tauF are typed with the bodies that the
lookup's readings have, by a reading. At the head R, its two equations and ReqFits stay premises:
head_record_met meets them at a written record with nothing heard; that the head's run record in the
description is such an R at a request that can be served is not said. No text of ForInG reads tokv.
X is publicOf's, not the description's own public part (at that part: ServedLive.lean). Not covered:
the digits of the smallness test; a lookup's counts. It does not say that any block says yes: no
completeness. Hid is Row.lean's name for the type of the lists w.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.ServedMeans
import Johnson.Goal.Meaning.WeighedScope
import Johnson.Road.Lane5KeysIffG
import Johnson.Goal.Meaning.AttForInScope
import Johnson.Goal.Meaning.HeadForInScope
import Johnson.Road.Ends.HeadWit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5 OnBytes.Ends OnBytes.Road.Rows.Norms
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks)
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (Mat AcceptancePolicy Instance ppref)
open Inst.Model.All (DF nGr)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- **The layers' lookup's own clause is the lookup clause of the group**, at all public files in
the goals' scope. -/
theorem forInG_iff_keys_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ)
    {g : ℕ} (hg : g < 12) (Mz : Mats ℤ) (Wi : Mat) :
    Alg.ForInG (pubAt X tokv) g Mz Wi ↔ LayerKeys (layerShape X.P) X.layers.sc X.y g Mz Wi := by
  obtain ⟨mats, r, hl⟩ := hl_in_scope hZ hR h g
  obtain ⟨hy, S, hs, hrd, Zd, -, hN, hfl, Zw, -, hlw, h4⟩ := pub34_public hZ hR h
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  have hsh := shape_in_scope hZ hR h
  have hLam : X.y.Lam = 4 := by
    rw [(laid_of_layout hy S.p3).2.Lam, shape_of_public h, hsh]
    rfl
  have h8 : X.y.calls.size = 8 := by
    have := congrArg List.length hN
    simpa using this
  exact Alg.forInG_iff_keys (P := pubAt X tokv) (rd := X.layers.rd) hy S hs
    (by show g < X.y.NGr; rw [B.groups]; exact hg) hrd hl Zd h4
    (by rw [show (layerShape X.P).dh = 128 from A.num 7]) (hmats_of_layout hy S.p3)
    (by
      show X.y.T = DF.T
      rw [(laid2_of_layout hy).T, shape_of_public h, hsh]
      rfl)
    Zw hlw
    (fun l hl4 => by
      show g * X.y.Lam + l < 48
      have : l < 4 := hl4
      rw [hLam]
      omega)
    (Rope.ropeOK_in_scope hZ hR h hg) h8
    (fun cc cd hcd => by
      have e := line_at hN cc
      have eg : X.y.calls.getD cc.val default = cd := by
        have hq : cc.val < X.y.calls.size := by rw [h8]; exact cc.isLt
        have hcd' : X.y.calls[cc.val]? = some cd := hcd
        rw [Array.getElem?_eq_getElem hq] at hcd'
        simp [Array.getD, hq, Option.some.inj hcd']
      rw [eg] at e
      exact e)
    hfl (fun cd hcd => weighed_in_scope hZ hR h cd hcd) (hL_in_scope hZ hR h) Mz Wi

/-- From Means: every call's keys of group g lie in the table of the layers' own record. -/
theorem forInG_of_means (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12) {i : Cm.Idx}
    {x : Instance ppref} {w : Hid} (M : Means X pp i x w) :
    Alg.ForInG (pubAt X tokv) g (w.MG g) i.mat :=
  (forInG_iff_keys_in_scope hZ hR h tokv hg _ _).2 (M.layers g hg).key

end Meaning.P34

namespace Meaning.Att

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (Instance ppref)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- From Means: attention's part without the lookup clause, and the lookup's own clause. -/
theorem forInA_of_means (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {i : Cm.Idx}
    {x : Instance ppref} {w : Hid} (M : Means X pp i x w) :
    AttR0 (Hd.shapeA X g) (w.MA g) ∧ ForInA (Hd.shapeA X g) (fsA X g) (cellZ (w.MA g)) :=
  (attOrd_iff_forIn_in_scope hZ hR h hg (w.MA g)).1 (M.attention g hg).ord

end Meaning.Att

namespace Meaning.HeadS

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf Public borderOf)
open Inst.Model (Mat ppref AcceptancePolicy Instance)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- From the head's record: the lookup's own clause. -/
theorem forInH_of_ord (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {R : Head.Run} (e1 : R.h = X.hS) (e2 : R.L = X.HLy)
    {pl : AcceptancePolicy} {x : Instance ppref}
    (Rq : Hd.ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pl x)) {Wz : Mat} {Mh : Mats ℤ}
    (O : Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) pl Wz x Mh) :
    Hd.ForInH R (Hd.callsH R (borderOf X.y) X.layers.wsLay Mh Wz).K :=
  ((headOrd_iff_in_scope hZ hR h e1 e2 Rq Wz Mh).1 O).2

/-- The three premises on the head's run record are met together, at every request: X's shape,
layout and plan, nothing heard, with the request's positions and checked tokens laid in. -/
theorem head_record_met (X : Public) (pl : AcceptancePolicy) (x : Instance ppref) :
    ∃ R : Head.Run, R.h = X.hS ∧ R.L = X.HLy ∧
      Hd.ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pl x) :=
  ⟨Hd.runReq (Hd.blankRun X) x, rfl, rfl, Hd.reqFits_runReq _ pl x⟩

end Meaning.HeadS

namespace Meaning

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf Public borderOf)
open OnBytes.Model.Layer (matIx)
open Inst.Model (Mat ppref AcceptancePolicy Instance)
open VerifiableInference

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- **At a request that can be served: ONE x, w, Mh with the whole end of means_of_served, and at
them the library's key vectors of the lookups on the calls lie in the tables read off the verifier's
own records**: of the 12 groups of layers and the 12 attention sub-proofs; of the head at every run
record that fits the request. The lookups on the smallness test's digits are not meant. -/
theorem forIn_of_served (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X)
    (weights : ModelWeights (VerifierAndGoals.settingsOfRead pp)) (prompt output : List Token)
    (served : CanServe (VerifierAndGoals.settingsOfRead pp) weights prompt output)
    (own : VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) weights prompt output) :
    ∃ (x : Instance ppref) (w : Hid) (Mh : Mats ℤ),
      requestOfTokens (prompt, output) [] = some x ∧ w.tok = x.y ∧
      Means X pp (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights) x w ∧
      Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS)
        (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights).mat x Mh ∧
      (∀ row col, Mh (X.hS.NHf + 3) row col = w.MG 11 (matIx X.y).iXO row col) ∧
      (∀ (tokv : Array ℕ), ∀ g < 12, Alg.ForInG (P34.pubAt X tokv) g (w.MG g)
        (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights).mat) ∧
      (∀ g < 12, ForInA (Hd.shapeA X g) (Att.fsA X g) (cellZ (w.MA g))) ∧
      ∀ R : Head.Run, R.h = X.hS → R.L = X.HLy →
        Hd.ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) →
        Hd.ForInH R (Hd.callsH R (borderOf X.y) X.layers.wsLay Mh
          (indexOfWeights (VerifierAndGoals.valid_of_read hR) weights).mat).K := by
  obtain ⟨x, w, Mh, built, tok, M, OH, copy⟩ :=
    means_of_served hZ hR h weights prompt output served own
  exact ⟨x, w, Mh, built, tok, M, OH, copy,
    fun tokv g hg => P34.forInG_of_means hZ hR h tokv hg M,
    fun g hg => (Att.forInA_of_means hZ hR h hg M).2,
    fun R e1 e2 Rq => HeadS.forInH_of_ord hZ hR h e1 e2 Rq OH⟩

end Meaning

#print axioms Meaning.P34.forInG_iff_keys_in_scope
#print axioms Meaning.P34.forInG_of_means
#print axioms Meaning.Att.forInA_of_means
#print axioms Meaning.HeadS.forInH_of_ord
#print axioms Meaning.HeadS.head_record_met
#print axioms Meaning.forIn_of_served
