-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/RightGated.lean: CONDITIONAL.

Not shown here. THAT THE CHALLENGES WHICH THE HONEST SIDE HAS HEARD ARE THE POINTS THAT THE VERIFIER
HOLDS, that the honest side's functions return and that the cubes' sizes fit: GatedAt and EmbAt are
hypotheses. TensorIs, and in right_emb EmbCube (a hypothesis on the witness) and the library's own
sizes: hypotheses. That they can hold together: no example is known. By a walk of import lines the
closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs),
through Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/; under
Johnson/RecCompile/ none of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness
or on any other property. No property is claimed.

Five fields of `OpenedRight` (Law/W/Halves.lean), each as a copy of that field's text: lv1L, lv1R,
lv2L, lv2R from `lv1_read` and `lv2_read` (Johnson/Road/K4/C/Gated.lean), and emb from `emb_right`
(Law/W/EmbRight.lean). No term of the structure is built here: that the copies are the fields is
held where one is built from them (Law/W/RightAll.lean).

  `GatedAt Q w h ds o tb1 tb2`   at the prefixes of the challenges at which the two product layers'
      jobs are made: the tables are there; the layers' own challenges are as many as their
      variables; the cubes' sizes fit; the challenges laid as points are the verifier's o.hd.r and
      o2.r.
  `EmbAt Q w h ds o ce cl`   at the prefix at which the embedding's value is made: the claim is
      there; the layout, the group and the two points are the verifier's.
  `right_gated`   the four fields.
  `right_emb`   the field emb.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.Halves
import Johnson.Desc.ProofFile.Honest.K4.Law.W.EmbRight
import Johnson.Road.K4.C.Gated

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open Finset
open OnBytes (E zeroE)
open OnBytes.Model (Reading WsClaim WsUnit WsShape wsLayOf wsClaimShape eqTab orderRange)
open OnBytes.Model.Layer (Own Ten ClaimEnv downFrom)
open OnBytes.Road (pt SizedW)
open OnBytes.Road.K4.W (uEOf EmbCube)
open OnBytes.Road.K4.C (TensorIs GatedNums lv1_read lv2_read)
open OnBytes.Desc.First.K4.Honest
open Inst.Model (Scl ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Cell xS embR lF lFe slV upV slV' upV')
open Meaning.Emb (EmbNums)
open Blocks (ext)

/-- The sampled values as the first product layer's job finds them. -/
def pts5 (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) : Pts :=
  ptsOf Q w (h ++ ds.take (rJ5 Q.P Q.hp Q.g))

/-- The sampled values as the second product layer's job finds them. -/
def pts6 (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) : Pts :=
  ptsOf Q w (h ++ ds.take (rJ6 Q.P Q.hp Q.g))

/-- The sampled values as the embedding's value finds them. -/
def ptsE (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) : Pts :=
  ptsOf Q w (h ++ ds.take (rE Q.P Q.hp Q.g))

/-- **The two product layers' jobs against what the verifier holds.** This defines a hypothesis; the
definition claims nothing. -/
structure GatedAt (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) (o : Own) (tb1 tb2 : Tab × Tab) :
    Prop where
  t1 : gatedTabs Q w = some tb1
  t2 : gatedTabs2 Q w = some tb2
  len1 : (ownE ds (rJ5 Q.P Q.hp Q.g + 1) Q.P.rd.muH).length = Q.P.rd.muH
  len2 : (ownE ds (rJ6 Q.P Q.hp Q.g + 1) Q.P.rd.muH2).length = Q.P.rd.muH2
  fit1 : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
    (downFrom (pts5 Q w h ds).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (pts5 Q w h ds))
    tb1).cube.fits = true
  fit2 : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
    ((pts6 Q w h ds).rhoM ++ downFrom (pts6 Q w h ds).rs Q.P.y.lfe ++ (pts6 Q w h ds).rt)
    tb2).cube.fits = true
  r1 : o.hd.r = (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
    (downFrom (pts5 Q w h ds).rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q (pts5 Q w h ds))
    tb1).cube.pointOf (ownE ds (rJ5 Q.P Q.hp Q.g + 1) Q.P.rd.muH)
  r2 : ∀ o2, o.hd2 = some o2 → o2.r = (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
    ((pts6 Q w h ds).rhoM ++ downFrom (pts6 Q w h ds).rs Q.P.y.lfe ++ (pts6 Q w h ds).rt)
    tb2).cube.pointOf (ownE ds (rJ6 Q.P Q.hp Q.g + 1) Q.P.rd.muH2)

/-- **The embedding's claim against what the verifier holds.** This defines a hypothesis; the
definition claims nothing. -/
structure EmbAt (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) (o : Own) (ce : ClaimEnv)
    (cl : WsClaim) : Prop where
  env : claimEnvOf Q (ptsE Q w h ds) = some ce
  claim : ce.claimE (ptsE Q w h ds).ZE (ptsE Q w h ds).tkh Q.P.V w.tokv = some cl
  g : o.v.g = Q.g
  y : ce.v.y = o.v.y
  ZE : (ptsE Q w h ds).ZE = o.H.ZE
  tkh : (ptsE Q w h ds).tkh = o.H.tkh

variable {Q : K4Pub} {w : K4In} {h ds : List Fmt.Drawn} {o : Own} {D : Dim} {t : Cell → Cb.Gl.E}

/-- **THE FOUR FIELDS lv1L, lv1R, lv2L, lv2R OF OpenedRight.** CONDITIONAL: on every hypothesis
named. -/
theorem right_gated {tb1 tb2 : Tab × Tab} (A : GatedAt Q w h ds o tb1 tb2) {ts tu : Ten}
    (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu) (Ss : TensorIs Q w t .sl ts)
    (Su : TensorIs Q w t .up tu) (N : GatedNums Q D) :
    (Reading.gl.val (wLv1 Q w h ds 0) =
      ext (D.lL + lF D + D.lT) (slV D t) (pt Reading.gl o.hd.r)) ∧
    (Reading.gl.val (wLv1 Q w h ds 1) =
      ext (D.lL + lF D + D.lT) (upV D t) (pt Reading.gl o.hd.r)) ∧
    (∀ o2, o.hd2 = some o2 → Reading.gl.val (wLv2 Q w h ds 0) =
      ext (D.lL - 1 + lFe D + D.lT) (slV' D t) (pt Reading.gl o2.r)) ∧
    (∀ o2, o.hd2 = some o2 → Reading.gl.val (wLv2 Q w h ds 1) =
      ext (D.lL - 1 + lFe D + D.lT) (upV' D t) (pt Reading.gl o2.r)) := by
  have a := lv1_read hts htu Ss Su N (pts5 Q w h ds) _ A.len1 A.t1 A.fit1 A.r1
  exact ⟨a.1, a.2,
    fun o2 h2 => (lv2_read hts htu Ss Su N (pts6 Q w h ds) _ A.len2 A.t2 A.fit2 (A.r2 o2 h2)).1,
    fun o2 h2 => (lv2_read hts htu Ss Su N (pts6 Q w h ds) _ A.len2 A.t2 A.fit2 (A.r2 o2 h2)).2⟩

/-- **THE FIELD emb OF OpenedRight**, where the stream that comes in is the embedding of the tokens,
at the library's own sizes. CONDITIONAL: on every hypothesis named. -/
theorem right_emb [scl : Scl] {ce : ClaimEnv} {cl : WsClaim} (A : EmbAt Q w h ds o ce cl)
    {u : WsUnit} (hu : Q.P.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape Q.P.wsLay cl = .ok ())
    (s : WsShape) (Z : SizedW s ppref) (hl : wsLayOf s true kRef = .ok Q.P.wsLay)
    (hV : Q.P.V = ppref.V) (N : EmbNums o.v.y) (hZ : o.H.ZE.size = o.v.y.ls + o.v.y.h.lt)
    (hk : o.H.tkh.size = o.v.y.lPd - o.v.y.ls) (hlT : D.lT = o.v.y.h.lt)
    (hJ : EmbCube D t (embR ppref kRef (wmOf w.w)) (fun i => w.tokv.getD i 0) o.v.y.h.d) :
    o.v.g = 0 → Reading.gl.val (wEmb Q w h ds) =
      ∑ kh ∈ range (o.v.y.h.d / o.v.y.S2), Reading.gl.val ((eqTab o.H.tkh).getD kh zeroE) *
        ∑ r ∈ range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt Reading.gl o.H.ZE) r *
          ext D.lT (fun p => xS D t 0 (kh * 2 ^ o.v.y.ls + r) p) (uEOf Reading.gl o.v o.H) := by
  intro h0
  have hg : (Q.g == 0) = true := beq_iff_eq.mpr (A.g.symm.trans h0)
  have e := emb_right (D := D) (t := t) hg A.env A.claim hu hs s Z hl hV (by rw [A.y]; exact N)
    (by rw [A.y, A.ZE]; exact hZ) (by rw [A.y, A.tkh]; exact hk) (by rw [A.y]; exact hlT)
    (by rw [A.y]; exact hJ)
  rw [A.y, A.ZE, A.tkh] at e
  exact e

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.right_gated
#print axioms ProofFile.Honest.K4.W.right_emb
