-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/RightAll.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the structure
`OpenedRight` (Law/W/Halves.lean) whole, AS A TERM OF THAT STRUCTURE: six fields from right_norms
(Law/W/RightNorms.lean), four from right_gated and one from right_emb (Law/W/RightGated.lean),
three as hypotheses. Definition of a hypothesis; statements and proofs.

  `RightTerms`    the three fields rt, sc, sel, with OpenedRight's own texts.
  `right_join`    OpenedRight from what the three statements end in, and RightTerms.
  **`right_all`**   OpenedRight from the three statements' premises, and RightTerms.

Not shown here. That the hypotheses hold anywhere: no example is known. THREE FIELDS OF OpenedRight,
rt, sc, sel, ARE HYPOTHESES HERE (RightTerms); Law/W/RightTermsOf.lean has RightTerms under
hypotheses of its own (right_terms, right_terms_of). Every premise of the three statements that are
called is a premise here, but one: right_emb's hlT (D.lT = o.v.y.h.lt) is drawn from F. No file of
this tree calls right_all; right_join is what is called (Law/W/ItemRightOf.lean). IN THE FIRST GROUP
right_all CAN BE MET AT THE LIBRARY's OWN SIZES ALONE (Em holds SizedW s ppref, kRef and Q.P.V =
ppref.V): at another plan it says nothing there. The import closure holds, with Law/W/Halves.lean's
own imports, seven modules under Johnson/RecCompile/. Nothing on soundness, on completeness or on
any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightNorms
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightGated

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open Finset
open OnBytes (E zeroE)
open OnBytes.Model (Reading World WsClaim WsUnit WsShape wsLayOf wsClaimShape eqTab)
open OnBytes.Model.Layer (Own Ten ClaimEnv)
open OnBytes.Road (pt SizedW Fits Mats cellsAt)
open OnBytes.Road.K4.W (uEOf EmbCube)
open OnBytes.Road.K4.C (TensorIs GatedNums CellsAre NormsPlan RowFields)
open OnBytes.Desc.First.K4.Honest
open Inst.Model (Scl ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Cell xS embR lF lFe slV upV slV' upV')
open Meaning.Emb (EmbNums)
open Blocks (ext)

/-- **The three fields rt, sc, sel of OpenedRight**, in its own texts. This defines a hypothesis;
the definition claims nothing. -/
structure RightTerms (Wd : World Cb.Gl.E) (Q : K4Pub) (o : Own) (w : K4In)
    (h ds : List Fmt.Drawn) : Prop where
  rt : ∀ i, i < o.v.y.NN * o.v.y.Lam → ∀ x, o.v.rowR "rt" i = some x →
    Reading.gl.val (wTerm Q w h ds i) = x.value Reading.gl Wd
  sc : ∀ lm, lm < o.v.y.LamM → ∀ x, o.v.shA "sc" "rt" lm 0 = some x →
    Reading.gl.val (wTerm Q w h ds (o.v.y.NN * o.v.y.Lam + lm)) = x.value Reading.gl Wd
  sel : ∀ i, i < o.v.y.LamM * o.v.y.h.NE → ∀ x,
    o.v.shA "sel" "rt" (i / o.v.y.h.NE) (i % o.v.y.h.NE) = some x →
    Reading.gl.val (wTerm Q w h ds (o.v.y.NN * o.v.y.Lam + o.v.y.LamM + i)) =
      x.value Reading.gl Wd

variable [scl : Scl] {W Wd : World Cb.Gl.E} {Q : K4Pub} {o : Own} {w : K4In}
  {h ds : List Fmt.Drawn} {D : Dim} {t : Cell → Cb.Gl.E} {low u : ℕ → Cb.Gl.E}
  {Mm : Mats Cb.Gl.E}

/-- **OpenedRight from what the three statements end in.** CONDITIONAL: on all four. -/
theorem right_join (X : RightNorms Q o w h ds D t)
    (Y : (Reading.gl.val (wLv1 Q w h ds 0) =
        ext (D.lL + lF D + D.lT) (slV D t) (pt Reading.gl o.hd.r)) ∧
      (Reading.gl.val (wLv1 Q w h ds 1) =
        ext (D.lL + lF D + D.lT) (upV D t) (pt Reading.gl o.hd.r)) ∧
      (∀ o2, o.hd2 = some o2 → Reading.gl.val (wLv2 Q w h ds 0) =
        ext (D.lL - 1 + lFe D + D.lT) (slV' D t) (pt Reading.gl o2.r)) ∧
      (∀ o2, o.hd2 = some o2 → Reading.gl.val (wLv2 Q w h ds 1) =
        ext (D.lL - 1 + lFe D + D.lT) (upV' D t) (pt Reading.gl o2.r)))
    (Z : o.v.g = 0 → Reading.gl.val (wEmb Q w h ds) =
      ∑ kh ∈ range (o.v.y.h.d / o.v.y.S2), Reading.gl.val ((eqTab o.H.tkh).getD kh zeroE) *
        ∑ r ∈ range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt Reading.gl o.H.ZE) r *
          ext D.lT (fun p => xS D t 0 (kh * 2 ^ o.v.y.ls + r) p) (uEOf Reading.gl o.v o.H))
    (T : RightTerms Wd Q o w h ds) : OpenedRight Wd Q o w h ds D t :=
  right_whole X
    { rt := T.rt, sc := T.sc, sel := T.sel, lv1L := Y.1, lv1R := Y.2.1, lv2L := Y.2.2.1
      lv2R := Y.2.2.2, emb := Z }

/-- **OpenedRight WHOLE**, from the premises of right_norms, right_gated and right_emb, and the
three fields rt, sc, sel. right_emb's premises (Em) are asked in the first group alone, where alone
the field emb says something. CONDITIONAL: on every hypothesis named. -/
theorem right_all (A : PtsAre Q w h ds o) (K : MakersNorms Q w h ds o D)
    (F : Fits Reading.gl W o.v D (cellsAt o.v.y Mm) t low u) (hy : Q.P.y = o.v.y)
    (C : CellsAre Q w Mm) (N : NormsPlan Q D)
    (R : RowFields Q w (ptsOf Q w (h ++ ds.take (rowsRound Q.P Q.g))) D t)
    {tb1 tb2 : Tab × Tab} (Ag : GatedAt Q w h ds o tb1 tb2) {ts tu : Ten}
    (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu) (Ss : TensorIs Q w t .sl ts)
    (Su : TensorIs Q w t .up tu) (Ng : GatedNums Q D)
    (Em : o.v.g = 0 → ∃ (ce : ClaimEnv) (cl : WsClaim) (un : WsUnit) (s : WsShape),
      EmbAt Q w h ds o ce cl ∧ Q.P.wsLay.U[cl.ui]? = some un ∧
      wsClaimShape Q.P.wsLay cl = .ok () ∧ SizedW s ppref ∧
      wsLayOf s true kRef = .ok Q.P.wsLay ∧ Q.P.V = ppref.V ∧ EmbNums o.v.y ∧
      o.H.ZE.size = o.v.y.ls + o.v.y.h.lt ∧ o.H.tkh.size = o.v.y.lPd - o.v.y.ls ∧
      EmbCube D t (embR ppref kRef (wmOf w.w)) (fun i => w.tokv.getD i 0) o.v.y.h.d)
    (T : RightTerms Wd Q o w h ds) : OpenedRight Wd Q o w h ds D t :=
  right_join (right_norms A K F hy C N R) (right_gated Ag hts htu Ss Su Ng)
    (fun h0 => by
      obtain ⟨ce, cl, un, s, Ae, hu, hs, Zs, hl, hV, Ne, hZ, hk, hJ⟩ := Em h0
      exact right_emb Ae hu hs s Zs hl hV Ne hZ hk F.lT.symm hJ h0) T

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.right_join
#print axioms ProofFile.Honest.K4.W.right_all
