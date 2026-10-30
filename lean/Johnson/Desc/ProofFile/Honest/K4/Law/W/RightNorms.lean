-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/RightNorms.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: six fields of the
structure `OpenedRight` (Law/W/Halves.lean): sums, prods, cl8, ends8, sqL, sqR, from the laws on
the norms' makers (Johnson/Road/K4/C/Norms.lean), each honest word at its own list of sampled
values. Definitions of hypotheses; statements and proofs.

  `PtsAre`        the sampled values that the norms' makers read are those that the verifier has
                  heard: one field for each equation, each at its own round.
  `MakersNorms`   the norms' makers return, and the point and the challenges have their lengths.
  `RightNorms`    the six fields, with OpenedRight's own texts.
  `RightRest`     the eight other fields, with OpenedRight's own texts.
  **`right_norms`**   the six fields.
  `right_whole`   the six and the eight give OpenedRight.

Not shown here. That the hypotheses hold anywhere: no example is known. THAT THE SAMPLED VALUES ARE
THE VERIFIER's (PtsAre), that the makers return and the lengths fit (MakersNorms), the rows' fields
(RowFields), the cells (CellsAre) and the plan's facts (NormsPlan) are hypotheses. Eight fields of
OpenedRight are hypotheses here (RightRest). The import closure holds, with Law/W/Halves.lean's own
imports, seven modules under Johnson/RecCompile/. Nothing on soundness, on completeness or on any
other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.Halves
import Johnson.Road.K4.C.Norms
import Johnson.Desc.ProofFile.Honest.K4.Law.SumRowsStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open Finset
open OnBytes (zeroE)
open OnBytes.Model (Reading World ledNS ledNP ledNO eqTab)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.Road (pt wHat pHat Fits Mats cellsAt)
open OnBytes.Road.K4.W (uEOf)
open OnBytes.Road.K4.C (CellsAre NormsPlan RowFields sums_read sq_read prods_read ends8_read
  rowMaps_congr rowFields_congr)
open OnBytes.Desc.First.K4 (k0)
open OnBytes.Desc.First.K4.Honest
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell bS xS led lF lFe slV upV slV' upV')
open Blocks (ext)

/-- **THE SAMPLED VALUES THAT THE NORMS' MAKERS READ ARE THOSE THAT THE VERIFIER HAS HEARD**, each
at the list of challenges at which its maker is called. h: the challenges heard in front of the
member. ds: the member's own. This defines a hypothesis; the definition claims nothing. -/
structure PtsAre (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) (o : Own) : Prop where
  /-- the norms' token point, where the sums are made -/
  PV0 : (ptsOf Q w (h ++ ds.take (k0 Q.g))).PV = o.H.PV
  /-- the powers under which the limbs are batched -/
  gp : (ptsOf Q w (h ++ ds.take (rJ1 Q.g))).gp = o.H.gp
  /-- the squares' product layer's point -/
  r6 : ∀ J, jobSquares Q w (ptsOf Q w (h ++ ds.take (rJ1 Q.g))) = some J →
    J.cube.pointOf (ownE ds (rJ1 Q.g + 1) Q.P.rd.muV) = o.H.wpl.r
  /-- the norms' token point, where the row products are made -/
  PV1 : (ptsOf Q w (h ++ ds.take (rowsRound Q.P Q.g))).PV = o.H.PV
  /-- the end point of the row products' token sumcheck -/
  rtV : ∀ J, jobRows Q w (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g))) = some J →
    J.cube.pointOf (ownE ds (rJ2 Q.P Q.g + 1) Q.P.y.h.lt) = o.H.tV.r
  /-- the norms' token point, where that sumcheck's job is made -/
  PV2 : (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g))).PV = o.H.PV
  /-- the powers under which the row products are batched -/
  omV : (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g))).omV = o.H.omV
  /-- what the lookup has sampled is one at the two lists -/
  fo : (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g))).fo =
    (ptsOf Q w (h ++ ds.take (rowsRound Q.P Q.g))).fo

/-- **The norms' makers return, and the point and the challenges have their lengths.** This defines
a hypothesis; the definition claims nothing. -/
structure MakersNorms (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) (o : Own) (D : Dim) :
    Prop where
  sq : (jobSquares Q w (ptsOf Q w (h ++ ds.take (rJ1 Q.g)))).isSome = true
  rows : (jobRows Q w (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g)))).isSome = true
  PV : o.H.PV.size = D.lT
  rs6 : (ownE ds (rJ1 Q.g + 1) Q.P.rd.muV).length = Q.P.rd.muV
  rs8 : (ownE ds (rJ2 Q.P Q.g + 1) Q.P.y.h.lt).length = D.lT

/-- **Six fields of OpenedRight**, in its own texts. This defines a hypothesis; the definition
claims nothing. -/
structure RightNorms [scl : Scl] (Q : K4Pub) (o : Own) (w : K4In) (h ds : List Fmt.Drawn)
    (D : Dim) (t : Cell → Cb.Gl.E) : Prop where
  sums : ∀ ν, ν < D.nNu → ∀ s, s < 9 →
    Reading.gl.val (wSum Q w h ds (9 * ν + s)) = wHat D t ν (pt Reading.gl o.H.PV) s
  prods : ∀ ν, ν < D.nNu → ∀ j, j < 7 →
    Reading.gl.val (wProd Q w h ds (7 * ν + j)) = pHat D t ν (pt Reading.gl o.H.PV) j
  cl8 : Reading.gl.val (wLead8 Q w h ds) = ∑ i ∈ range (ledNP o.v.y.h.xl * o.v.y.NI),
    Reading.gl.val (o.H.omV.getD i zeroE) * Reading.gl.val (wProd Q w h ds i)
  ends8 : ∀ ν, ν < D.nNu →
    Reading.gl.val (wEnd8 Q w h ds (4 * ν + 0)) =
      ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) (pt Reading.gl o.H.tV.r) ∧
    Reading.gl.val (wEnd8 Q w h ds (4 * ν + 1)) =
      ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) (pt Reading.gl o.H.tV.r) ∧
    Reading.gl.val (wEnd8 Q w h ds (4 * ν + 2)) =
      ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) (pt Reading.gl o.H.tV.r) ∧
    Reading.gl.val (wEnd8 Q w h ds (4 * ν + 3)) =
      ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) (pt Reading.gl o.H.tV.r)
  sqL : Reading.gl.val (wSq Q w h ds 0) =
    ext (Q.P.rd.lNI + o.v.y.lPd - o.v.y.ls + o.v.y.ls + D.lT)
      (OnBytes.Road.K4.sqV o.v.y.NI (o.v.y.h.d / o.v.y.S2 * 2 ^ o.v.y.ls) o.v.y.lPd o.v.y.xb.nl
        D.lT (fun l => Reading.gl.val (o.H.gp.getD l zeroE)) (fun ν l j p => bS D t ν l j p))
      (pt Reading.gl o.H.wpl.r)
  sqR : Reading.gl.val (wSq Q w h ds 1) = Reading.gl.val (wSq Q w h ds 0)

/-- **The eight other fields of OpenedRight**, in its own texts. This defines a hypothesis; the
definition claims nothing. -/
structure RightRest [scl : Scl] (Wd : World Cb.Gl.E) (Q : K4Pub) (o : Own) (w : K4In)
    (h ds : List Fmt.Drawn) (D : Dim) (t : Cell → Cb.Gl.E) : Prop where
  rt : ∀ i, i < o.v.y.NN * o.v.y.Lam → ∀ x, o.v.rowR "rt" i = some x →
    Reading.gl.val (wTerm Q w h ds i) = x.value Reading.gl Wd
  sc : ∀ lm, lm < o.v.y.LamM → ∀ x, o.v.shA "sc" "rt" lm 0 = some x →
    Reading.gl.val (wTerm Q w h ds (o.v.y.NN * o.v.y.Lam + lm)) = x.value Reading.gl Wd
  sel : ∀ i, i < o.v.y.LamM * o.v.y.h.NE → ∀ x,
    o.v.shA "sel" "rt" (i / o.v.y.h.NE) (i % o.v.y.h.NE) = some x →
    Reading.gl.val (wTerm Q w h ds (o.v.y.NN * o.v.y.Lam + o.v.y.LamM + i)) =
      x.value Reading.gl Wd
  lv1L : Reading.gl.val (wLv1 Q w h ds 0) =
    ext (D.lL + lF D + D.lT) (slV D t) (pt Reading.gl o.hd.r)
  lv1R : Reading.gl.val (wLv1 Q w h ds 1) =
    ext (D.lL + lF D + D.lT) (upV D t) (pt Reading.gl o.hd.r)
  lv2L : ∀ o2, o.hd2 = some o2 → Reading.gl.val (wLv2 Q w h ds 0) =
    ext (D.lL - 1 + lFe D + D.lT) (slV' D t) (pt Reading.gl o2.r)
  lv2R : ∀ o2, o.hd2 = some o2 → Reading.gl.val (wLv2 Q w h ds 1) =
    ext (D.lL - 1 + lFe D + D.lT) (upV' D t) (pt Reading.gl o2.r)
  emb : o.v.g = 0 → Reading.gl.val (wEmb Q w h ds) =
    ∑ kh ∈ range (o.v.y.h.d / o.v.y.S2), Reading.gl.val ((eqTab o.H.tkh).getD kh zeroE) *
      ∑ r ∈ range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt Reading.gl o.H.ZE) r *
        ext D.lT (fun p => xS D t 0 (kh * 2 ^ o.v.y.ls + r) p) (uEOf Reading.gl o.v o.H)

variable [scl : Scl] {W Wd : World Cb.Gl.E} {Q : K4Pub} {o : Own} {w : K4In}
  {h ds : List Fmt.Drawn} {D : Dim} {t : Cell → Cb.Gl.E} {low u : ℕ → Cb.Gl.E}
  {Mm : Mats Cb.Gl.E}

/-- **THE SIX FIELDS.** CONDITIONAL: on every hypothesis named. R: the rows' fields at the list of
sampled values at which the row products are made. -/
theorem right_norms (A : PtsAre Q w h ds o) (K : MakersNorms Q w h ds o D)
    (F : Fits Reading.gl W o.v D (cellsAt o.v.y Mm) t low u) (hy : Q.P.y = o.v.y)
    (C : CellsAre Q w Mm) (N : NormsPlan Q D)
    (R : RowFields Q w (ptsOf Q w (h ++ ds.take (rowsRound Q.P Q.g))) D t) :
    RightNorms Q o w h ds D t := by
  have hlt : Q.P.y.h.lt = D.lT := by rw [hy]; exact F.lT
  obtain ⟨J6, hJ6⟩ := Option.isSome_iff_exists.mp K.sq
  obtain ⟨J8, hJ8⟩ := Option.isSome_iff_exists.mp K.rows
  have w6 : ∀ e, wSq Q w h ds e = (J6.ends (ownE ds (rJ1 Q.g + 1) Q.P.rd.muV)).getD e zeroE := by
    intro e
    unfold wSq endWord
    rw [hJ6]
    rfl
  have w8 : ∀ e, wEnd8 Q w h ds e =
      (J8.ends (ownE ds (rJ2 Q.P Q.g + 1) Q.P.y.h.lt)).getD e zeroE := by
    intro e
    unfold wEnd8 endWord
    rw [hJ8]
    rfl
  have hxl : Q.P.y.h.xl = 5 := by rw [hy]; exact F.xl
  have hJ := hJ8
  rw [jobRows_eq] at hJ
  obtain ⟨ms, hms, hJ⟩ := Option.bind_eq_some_iff.mp hJ
  have hmaps : (rowMaps Q w (ptsOf Q w (h ++ ds.take (rowsRound Q.P Q.g)))).isSome = true := by
    rw [← rowMaps_congr Q w A.fo, hms]
    rfl
  have c8 : Reading.gl.val (wLead8 Q w h ds) = ∑ n ∈ range (7 * Q.P.y.NI),
      Reading.gl.val (o.H.omV.getD n zeroE) * Reading.gl.val (wProd Q w h ds n) := by
    split at hJ
    · obtain rfl := Option.some.inj hJ
      have e : wLead8 Q w h ds =
          (rowsJobOf Q (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g))) ms).cube.total := by
        unfold wLead8 leadWord
        rw [hJ8]
        rfl
      rw [e, rows_total Q w _ ms hms (by rw [N.T, hlt]) (by rw [A.PV2, hlt]; exact K.PV), A.omV,
        rowProducts_congr Q w _ _ A.fo (A.PV2.trans A.PV1.symm)]
      rfl
    · cases hJ
  have q := sq_read F hy C N hJ6 (ownE ds (rJ1 Q.g + 1) Q.P.rd.muV) K.rs6
  rw [A.gp, A.r6 J6 hJ6] at q
  exact
    { sums := fun ν hν s hs => by
        have e := sums_read (p := ptsOf Q w (h ++ ds.take (k0 Q.g))) F hy C N
          (by rw [A.PV0]; exact K.PV) ν hν s hs
        rw [A.PV0] at e
        exact e
      prods := fun ν hν j hj => by
        have e := prods_read R N.T N.NI (by rw [A.PV1]; exact K.PV) hmaps ν hν j hj
        rw [A.PV1] at e
        exact e
      cl8 := by
        rw [← hy, hxl]
        exact c8
      ends8 := fun ν hν => by
        have e := ends8_read (rowFields_congr A.fo.symm R) hlt hJ8
          (ownE ds (rJ2 Q.P Q.g + 1) Q.P.y.h.lt) K.rs8 ν hν
        rw [A.rtV J8 hJ8] at e
        rw [w8, w8, w8, w8]
        exact e
      sqL := by
        rw [w6]
        exact q.1
      sqR := by
        rw [w6, w6, q.2] }

/-- **OpenedRight from the six and the eight.** CONDITIONAL: on both. -/
theorem right_whole (X : RightNorms Q o w h ds D t) (Y : RightRest Wd Q o w h ds D t) :
    OpenedRight Wd Q o w h ds D t :=
  { sums := X.sums, prods := X.prods, cl8 := X.cl8, ends8 := X.ends8, sqL := X.sqL, sqR := X.sqR
    rt := Y.rt, sc := Y.sc, sel := Y.sel, lv1L := Y.lv1L, lv1R := Y.lv1R, lv2L := Y.lv2L
    lv2R := Y.lv2R, emb := Y.emb }

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.right_norms
#print axioms ProofFile.Honest.K4.W.right_whole
