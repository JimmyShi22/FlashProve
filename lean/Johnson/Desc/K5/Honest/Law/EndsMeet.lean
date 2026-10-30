-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/EndsMeet.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: THE READER's FORM UNDER AN END VALUE OF A SUMCHECK OF PRODUCTS IS WORTH THE
PROVER's END VALUE AT THE SUMCHECK's CHALLENGES, READ: for the softmax-table units, the division,
and the two halves of the value product. Statements with their proofs.

The verifier's claims on end values say "the slot is worth a written reader's form"
(Johnson/Desc/First/Att/Claims/Say.lean: `endsU`; Say58.lean: `endsE`, `endsV`). In a world in which
every table is true of some matrices the tree has each reader's worth as a read of the matrices'
cells at the reader's own points (Claims/EndsE.lean, Claims/MeanRd.lean, Claims/EndsVA.lean,
EndsVB.lean). The prover's end value is the same read of the prover's cells at the same points
(Johnson/Desc/K5/Honest/Law/TilesKit.lean, Cells.lean). Here the two are joined directly: no
statement of this file names one of the library's steps of the sum (`Step`,
Inst/Model/Att/Sums.lean). So a clause "the slot is worth the reader's form" follows from "the slot
is worth the prover's end value, read" by one rewrite.

Main names:
  `pwBack_getD`, `mem_getD`   piece number b of the list, in the two types of pieces
  `cells_qry`, `cells_out`, `cells_key`, `cells_val`, `cells_den`   the values of the cells agree
  `endsU_meets`      a softmax-table unit, below the diagonal or on it
  `endsE_meets`      the division
  `weight_meets_below`, `weight_meets_on`   the softmax weight's form: plane 3 + 128 + 256 plane 4
  `endsV_below_meets`, `endsV_on_meets`   the value product below the diagonal, on it

EVERY STATEMENT ON A FORM IS CONDITIONAL. The premises are those of
Johnson/Desc/K5/Honest/Law/AloneMeets.lean, whose head says who is meant to show each: `AttAt`
(among its clauses: every table of the list is true of the matrices in the world), `CellsAre`,
`PiecesFit`, that the tables lie in the list with the named weights, that the indices read lie in
the tables, lengths of points, and, for the division and the value product: what was heard of the
division is d carried back (hd), and its list has a piece for each pair (hn). The tables' weights
are named in the letters of the verifier's own function for the tables
(Johnson/Desc/First/Att/TablesP.lean).
Limits. Nothing here says that a premise holds at any place.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.AloneMeets
import Johnson.Desc.K5.Honest.Law.ReadVM
import Johnson.Desc.K5.Honest.Law.ReadVD
import Johnson.Desc.K5.Honest.Law.ReadSE

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP DivP geoOf)
open Inst.Model.AttSeg (Raw Dim rd2 rd3 denV qryV outV keyV valV)
open K5Law (pwBack scoreBack divBack sum3Back InLong)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-! ## Pieces by number -/

/-- Piece number b, in the type of pieces of the written claims. -/
theorem pwBack_getD (pw : Array W1) {b : ℕ} (hb : b < pw.size) :
    (pwBack pw).getD b default =
      { lam := (pw.getD b ⟨0, 0, zeroE⟩).lam, a := (pw.getD b ⟨0, 0, zeroE⟩).a,
        wp := (pw.getD b ⟨0, 0, zeroE⟩).wp } := by
  unfold K5Law.pwBack
  simp [Array.getD_eq_getD_getElem?, hb]

/-- Piece number b is a member of the list. -/
theorem mem_getD (pw : Array W1) {b : ℕ} (hb : b < pw.size) :
    pw.getD b ⟨0, 0, zeroE⟩ ∈ pw.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb]
  exact Array.getElem_mem_toList hb

/-! ## The values of the cells agree -/

section Cells
variable {S : Attention.Shape} {w : K5In} (hc : CellsAre ρ S M w)
include hc

theorem cells_den {b g i : ℕ} (hb : b < (L5.dimOf S).nb) (hg : g < (L5.dimOf S).nG)
    (hi : i < (L5.dimOf S).T) : denV (cellsK S M) b g i = denV (tOf ρ w) b g i := by
  unfold denV
  exact sum_congr rfl fun l hl => by rw [hc (.den l b g i) ⟨mem_range.mp hl, hb, hg, hi⟩]

theorem cells_qry {b g i n : ℕ} (hb : b < (L5.dimOf S).nb) (hg : g < (L5.dimOf S).nG)
    (hi : i < (L5.dimOf S).T) (hn : n < (L5.dimOf S).ch) :
    qryV (cellsK S M) b g i n = qryV (tOf ρ w) b g i n := by
  unfold qryV
  exact sum_congr rfl fun l hl => by rw [hc (.qry l b g i n) ⟨mem_range.mp hl, hb, hg, hi, hn⟩]

theorem cells_out {b g i n : ℕ} (hb : b < (L5.dimOf S).nb) (hg : g < (L5.dimOf S).nG)
    (hi : i < (L5.dimOf S).T) (hn : n < (L5.dimOf S).ch) :
    outV (cellsK S M) b g i n = outV (tOf ρ w) b g i n := by
  unfold outV
  exact sum_congr rfl fun l hl => by rw [hc (.out l b g i n) ⟨mem_range.mp hl, hb, hg, hi, hn⟩]

theorem cells_key {lam g j n : ℕ} (hl : lam < (L5.dimOf S).nl) (hg : g < (L5.dimOf S).nG)
    (hj : j < (L5.dimOf S).T) (hn : n < (L5.dimOf S).ch) :
    keyV (cellsK S M) lam g j n = keyV (tOf ρ w) lam g j n := by
  unfold keyV
  exact sum_congr rfl fun l hl' => by
    rw [hc (.key l lam g j n) ⟨mem_range.mp hl', hl, hg, hj, hn⟩]

theorem cells_val {lam g j n : ℕ} (hl : lam < (L5.dimOf S).nl) (hg : g < (L5.dimOf S).nG)
    (hj : j < (L5.dimOf S).T) (hn : n < (L5.dimOf S).ch) :
    valV (cellsK S M) lam g j n = valV (tOf ρ w) lam g j n := by
  unfold valV
  exact sum_congr rfl fun l hl' => by
    rw [hc (.val l lam g j n) ⟨mem_range.mp hl', hl, hg, hj, hn⟩]

end Cells

/-! ## The meetings -/

variable (A : AttAt ρ W tl K3 M h lid cf fs) (w : K5In) (hc : CellsAre ρ h.S M w)
include A hc

/-- **A softmax-table unit**, below the diagonal or on it. k.sc.r: the sumcheck's challenges.
CONDITIONAL on what the head lists. -/
theorem endsU_meets {k : ScoreP} {tb : ScoreTables} (hr : h.S.cf.lgk + h.S.cf.ldh ≤ k.sc.r.size)
    (TbQ : TabAt tl h tb.tQ (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh))
        (P.tok (geoOf h.S) (P.scoreTiles (geoOf h.S) k).1 k.zi)))
    (TbK : TabAt tl h tb.tK (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh))
        (P.tok (geoOf h.S) (P.scoreTiles (geoOf h.S) k).2 k.zj)))
    (Pf : PiecesFit h.S k.pw)
    (IQ : ∀ p ∈ k.pw.toList, InLong h tb.tQ h.S.atQ p.lam (fun g => g * h.S.HA + p.a)
      (lastCoords k.sc.r h.S.cf.ldh))
    (IK : ∀ p ∈ k.pw.toList, InLong h tb.tK h.S.atK p.lam (fun g => g)
      (lastCoords k.sc.r h.S.cf.ldh)) {j : ℕ} (hj : j < 2 * k.pw.size) :
    (K5Law.endsU h K3 (scoreBack k) tb j).value ρ W =
      ρ.val (if j % 2 = 0 then unitA (geoOf h.S) w k k.sc.r (j / 2)
        else unitB (geoOf h.S) w k k.sc.r (j / 2)) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have hb : j / 2 < k.pw.size := by omega
  have hm := mem_getD k.pw hb
  have hlg : h.S.cf.lgk ≤ k.sc.r.size := by omega
  have hzc : (lastCoords k.sc.r h.S.cf.ldh).size = h.S.cf.ldh := last_size k.sc.r (by omega)
  have sT : ∀ hi lo : Array E, (P.tok (geoOf h.S) hi lo).size = h.S.T :=
    fun hi lo => OnBytes.Road.Rows.tok_size h.S hi lo
  unfold K5Law.endsU
  show (if j % 2 = 0 then
      Fo.readHeadT h K3 tb.tQ h.S.atQ k.sc.r (lastCoords k.sc.r h.S.cf.ldh)
        ((pwBack k.pw).getD (j / 2) default).lam ((pwBack k.pw).getD (j / 2) default).a
    else Fo.readGroupT h K3 tb.tK h.S.atK k.sc.r (lastCoords k.sc.r h.S.cf.ldh)
        ((pwBack k.pw).getD (j / 2) default).lam).value ρ W = _
  rw [pwBack_getD k.pw hb]
  by_cases e : j % 2 = 0
  · rw [if_pos e, if_pos e, K5Law.readHeadT_qry A TbQ (sT _ _) hlg hzc (Pf _ hm).2 (IQ _ hm)]
    refine (rd3_on _ _ _ _ fun g hg i hi n hn => cells_qry hc (Pf.pair hm) hg hi hn).trans ?_
    exact (read_rd3 ρ (P := ⟨h.S, default⟩) H (r := k.sc.r) (zc := lastCoords k.sc.r h.S.cf.ldh)
      (by show h.S.cf.lgk ≤ _; omega) (fun _ _ => rfl) ((sT _ _).trans H.T) (fun _ _ => rfl) hzc
      (fun _ _ => rfl) fun g _ i _ n _ => read_q ρ w _ g i n).symm
  · rw [if_neg e, if_neg e, K5Law.readGroupT_key A TbK (sT _ _) hlg hzc (IK _ hm)]
    refine (rd3_on _ _ _ _ fun g hg i hi n hn => cells_key hc (Pf _ hm).1 hg hi hn).trans ?_
    exact (read_rd3 ρ (P := ⟨h.S, default⟩) H (r := k.sc.r) (zc := lastCoords k.sc.r h.S.cf.ldh)
      (by show h.S.cf.lgk ≤ _; omega) (fun _ _ => rfl) ((sT _ _).trans H.T) (fun _ _ => rfl) hzc
      (fun _ _ => rfl) fun g _ i _ n _ => read_kx ρ w _ g i n).symm

/-- **The division.** d.scE.r: the sumcheck's challenges. CONDITIONAL on what the head lists. -/
theorem endsE_meets {d : DivP} (hd : h.d = divBack d)
    (hr : h.S.cf.lgk + h.S.cf.lt ≤ d.scE.r.size) (hzc : d.zcW.size = h.S.cf.ldh)
    (TbE : TabAt tl h h.t.hE h.S.cf.NAs h.S.T
      (eqTab (d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))))
    (TbO : TabAt tl h h.t.qO (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S d.zcW)
      (eqTab (d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt)))))
    (Pf : PiecesFit h.S d.pwW) (hn : d.pwW.size = h.S.NP)
    (hinE : ∀ p ∈ d.pwW.toList, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4,
      h.S.oZr + (l * h.S.Lam + p.lam) * h.S.cf.H + (g * h.S.HA + p.a) <
        (h.t.tabLen.lookup h.t.hE).getD 0)
    (IO : ∀ p ∈ d.pwW.toList, InLong h h.t.qO h.S.atO p.lam (fun g => g * h.S.HA + p.a) d.zcW)
    {j : ℕ} (hj : j < 2 * h.S.NP) :
    (K5Law.endsE h K3 j).value ρ W =
      ρ.val (if j % 2 = 0 then seA (geoOf h.S) w d.pwW d.scE.r (j / 2)
        else seB (geoOf h.S) w d.pwW (P.eqTab d.zcW) d.scE.r (j / 2)) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have hb : j / 2 < d.pwW.size := by omega
  have hlg : h.S.cf.lgk ≤ d.scE.r.size := by omega
  have hm := mem_getD d.pwW hb
  have sz : (d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt)).size = h.S.cf.lt := by
    rw [size_extract_le _ hr]
    omega
  have sT := size_eqTab_tok (P := ⟨h.S, default⟩) (sz.trans H.lt)
  unfold K5Law.endsE
  rw [hd]
  show (if j % 2 = 0 then
      Fo.readDenominatorF h K3 h.t.hE d.scE.r ((pwBack d.pwW).getD (j / 2) default).lam
        ((pwBack d.pwW).getD (j / 2) default).a
    else Fo.readHeadT h K3 h.t.qO h.S.atO d.scE.r d.zcW ((pwBack d.pwW).getD (j / 2) default).lam
        ((pwBack d.pwW).getD (j / 2) default).a).value ρ W = _
  rw [pwBack_getD d.pwW hb]
  by_cases e : j % 2 = 0
  · rw [if_pos e, if_pos e, K5Law.readDenominatorF_rd2 A TbE hlg (Pf _ hm).2 (hinE _ hm)]
    refine (rd2_on _ _ _ fun g hg i hi => cells_den hc (Pf.pair hm) hg hi).trans ?_
    exact (read_rd2 ρ (P := ⟨h.S, default⟩) H (r := d.scE.r) (by show h.S.cf.lgk ≤ _; omega)
      (fun _ _ => rfl) sT (fun _ _ => rfl) fun g _ i _ => read_zd ρ w _ g i).symm
  · rw [if_neg e, if_neg e,
      K5Law.readHeadT_out A TbO (sT.trans H.T.symm) hlg hzc (Pf _ hm).2 (IO _ hm)]
    refine (rd3_on _ _ _ _ fun g hg i hi n hn => cells_out hc (Pf.pair hm) hg hi hn).trans ?_
    exact (read_rd3 ρ (P := ⟨h.S, default⟩) H (r := d.scE.r) (zc := d.zcW)
      (by show h.S.cf.lgk ≤ _; omega) (fun _ _ => rfl) sT (fun _ _ => rfl) hzc
      (fun _ _ => rfl) fun g _ i _ n _ => read_o ρ w _ g i n).symm

/-- The softmax weight's form, below the diagonal: plane 3 plus 128 plus 256 times plane 4, at a
point z of the region's length. -/
theorem weight_meets_below {t : ℕ} {z : Array E} (Tb : AsAt h t (lastN z h.S.cf.lmS))
    (hz : z.size = h.S.nM) {p : W1} (ha : p.a < h.S.HA)
    (hp : p.lam * h.S.HA + p.a < (L5.dimOf h.S).nb)
    (hin : ∀ x, x = 3 ∨ x = 4 →
      ∀ hi < (eqTab (z.extract 0 ((if false then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S x p.lam p.a false >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup t).getD 0) :
    (Fo.planeF h K3 t 3 p.lam p.a z false + Aff.ofConst (ofNat 128) +
      Aff.scale (Fo.planeF h K3 t 4 p.lam p.a z false) (ofNat 256)).value ρ W =
      ρ.val (weightAt w false z (p.lam * h.S.HA + p.a)) := by
  have N := norm_of_hid A.shape
  have c : ∀ x < 5, Blocks.ext h.S.nM
      (fun y => cellsK h.S M (.c .M x (p.lam * h.S.HA + p.a) y)) (pt ρ z) =
      Blocks.ext z.size (fun n => tOf ρ w (.c (regOf false) x (p.lam * h.S.HA + p.a) n))
        (pt ρ z) := fun x hx => by
    rw [hz]
    refine Blocks.ext_congr (fun X hX => ?_) _
    rw [N.nM] at hX
    exact hc (.c .M x (p.lam * h.S.HA + p.a) X) ⟨hx, hp, hX⟩
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale,
    K5Law.planeF_below A Tb hz ha (hin 3 (.inl rfl)),
    K5Law.planeF_below A Tb hz ha (hin 4 (.inr rfl)),
    c 3 (by norm_num), c 4 (by norm_num), Fo.ofNat_val, Fo.ofNat_val]
  unfold weightAt
  dsimp only
  rw [ρ.add, ρ.add, ρ.mul, read_planeAt, read_planeAt, read_ofNat, read_ofNat]
  ring

/-- The same on the diagonal. -/
theorem weight_meets_on {t : ℕ} {z : Array E} (Tb : AsAt h t (lastN z h.S.cf.lmS))
    (hz : z.size = h.S.nD) {p : W1} (ha : p.a < h.S.HA)
    (hp : p.lam * h.S.HA + p.a < (L5.dimOf h.S).nb)
    (hin : ∀ x, x = 3 ∨ x = 4 →
      ∀ hi < (eqTab (z.extract 0 ((if true then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S x p.lam p.a true >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup t).getD 0) :
    (Fo.planeF h K3 t 3 p.lam p.a z true + Aff.ofConst (ofNat 128) +
      Aff.scale (Fo.planeF h K3 t 4 p.lam p.a z true) (ofNat 256)).value ρ W =
      ρ.val (weightAt w true z (p.lam * h.S.HA + p.a)) := by
  have N := norm_of_hid A.shape
  have c : ∀ x < 5, Blocks.ext h.S.nD
      (fun y => cellsK h.S M (.c .D x (p.lam * h.S.HA + p.a) y)) (pt ρ z) =
      Blocks.ext z.size (fun n => tOf ρ w (.c (regOf true) x (p.lam * h.S.HA + p.a) n))
        (pt ρ z) := fun x hx => by
    rw [hz]
    refine Blocks.ext_congr (fun X hX => ?_) _
    rw [N.nD] at hX
    exact hc (.c .D x (p.lam * h.S.HA + p.a) X) ⟨hx, hp, hX⟩
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale,
    K5Law.planeF_on A Tb hz ha (hin 3 (.inl rfl)), K5Law.planeF_on A Tb hz ha (hin 4 (.inr rfl)),
    c 3 (by norm_num), c 4 (by norm_num), Fo.ofNat_val, Fo.ofNat_val]
  unfold weightAt
  dsimp only
  rw [ρ.add, ρ.add, ρ.mul, read_planeAt, read_planeAt, read_ofNat, read_ofNat]
  ring

/-- **The value product below the diagonal.** d.vpm.r: the sumcheck's challenges. CONDITIONAL on
what the head lists, and on: the tables' stored point is the verifier's point of the region, of the
region's length; the stored weights of the tile columns are those made of the challenges. -/
theorem endsV_below_meets {d : DivP} (hd : h.d = divBack d)
    (hpt : h.t.ptM = P.pointM (geoOf h.S) d) (hps : (P.pointM (geoOf h.S) d).size = h.S.nM)
    (hwJ : d.wJv = (belowAt (geoOf h.S) d d.vpm.r).wJv)
    (hr : h.S.cf.lgk ≤ d.vpm.r.size) (hzc : d.zcW.size = h.S.cf.ldh)
    (TbS : AsAt h h.t.tVM (lastN h.t.ptM h.S.cf.lmS))
    (TbV : TabAt tl h h.t.qVM (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S d.zcW)
      (P.tok (geoOf h.S) d.wJv (lastCoords d.vpm.r h.S.cf.lB))))
    (Pf : PiecesFit h.S d.pwW) (hn : d.pwW.size = h.S.NP)
    (hinS : ∀ p ∈ d.pwW.toList, ∀ x, x = 3 ∨ x = 4 →
      ∀ hi < (eqTab (h.t.ptM.extract 0 ((if false then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S x p.lam p.a false >>> h.S.cf.lmS + hi <
          (h.t.tabLen.lookup h.t.tVM).getD 0)
    (IV : ∀ p ∈ d.pwW.toList, InLong h h.t.qVM h.S.atV p.lam (fun g => g) d.zcW)
    {j : ℕ} (hj : j < 2 * h.S.NP) :
    (K5Law.endsV h K3 (sum3Back d.vpm) h.t.tVM h.t.ptM false h.t.qVM j).value ρ W =
      ρ.val (if j % 2 = 0 then vmA (geoOf h.S) w d d.vpm.r (j / 2)
        else vmB (geoOf h.S) w d (P.eqTab d.zcW) d.vpm.r (j / 2)) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have hb : j / 2 < d.pwW.size := by omega
  have hm := mem_getD d.pwW hb
  have sT : ∀ hi lo : Array E, (P.tok (geoOf h.S) hi lo).size = h.S.T :=
    fun hi lo => OnBytes.Road.Rows.tok_size h.S hi lo
  unfold K5Law.endsV
  rw [hd]
  show (if j % 2 = 0 then
      Fo.planeF h K3 h.t.tVM 3 ((pwBack d.pwW).getD (j / 2) default).lam
          ((pwBack d.pwW).getD (j / 2) default).a h.t.ptM false + Aff.ofConst (ofNat 128) +
        Aff.scale (Fo.planeF h K3 h.t.tVM 4 ((pwBack d.pwW).getD (j / 2) default).lam
          ((pwBack d.pwW).getD (j / 2) default).a h.t.ptM false) (ofNat 256)
    else Aff.ofConst d.gam + Fo.readGroupT h K3 h.t.qVM h.S.atV d.vpm.r d.zcW
        ((pwBack d.pwW).getD (j / 2) default).lam).value ρ W = _
  rw [pwBack_getD d.pwW hb]
  by_cases e : j % 2 = 0
  · rw [if_pos e, if_pos e]
    rw [hpt] at TbS hinS ⊢
    exact weight_meets_below A w hc TbS hps (Pf _ hm).2 (Pf.pair hm) (hinS _ hm)
  · rw [if_neg e, if_neg e, Aff.value_add, Aff.value_ofConst,
      K5Law.readGroupT_val A TbV (sT _ _) hr hzc (IV _ hm)]
    unfold vmB
    rw [ρ.add]
    refine congrArg₂ HAdd.hAdd rfl ?_
    refine (rd3_on _ _ _ _ fun g hg i hi n hn => cells_val hc (Pf _ hm).1 hg hi hn).trans ?_
    rw [hwJ]
    exact (read_rd3 ρ (P := ⟨h.S, default⟩) H (r := d.vpm.r) (zc := d.zcW) hr (fun _ _ => rfl)
      ((sT _ _).trans H.T) (fun _ _ => rfl) hzc (fun _ _ => rfl)
      fun g _ i _ n _ => read_v ρ w _ g i n).symm

/-- **The value product on the diagonal.** d.vpd.r: the sumcheck's challenges. CONDITIONAL on what
the head lists, and on: the tables' stored point is the verifier's point of the region, of the
region's length. -/
theorem endsV_on_meets {d : DivP} (hd : h.d = divBack d)
    (hpt : h.t.ptD = P.pointD (geoOf h.S) d) (hps : (P.pointD (geoOf h.S) d).size = h.S.nD)
    (hr : h.S.cf.lgk ≤ d.vpd.r.size) (hzc : d.zcW.size = h.S.cf.ldh)
    (TbS : AsAt h h.t.tVD (lastN h.t.ptD h.S.cf.lmS))
    (TbV : TabAt tl h h.t.qVD (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S d.zcW)
      (P.tok (geoOf h.S) (P.eqTab (d.vpd.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT)))
        (lastCoords d.vpd.r h.S.cf.lB))))
    (Pf : PiecesFit h.S d.pwW) (hn : d.pwW.size = h.S.NP)
    (hinS : ∀ p ∈ d.pwW.toList, ∀ x, x = 3 ∨ x = 4 →
      ∀ hi < (eqTab (h.t.ptD.extract 0 ((if true then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S x p.lam p.a true >>> h.S.cf.lmS + hi <
          (h.t.tabLen.lookup h.t.tVD).getD 0)
    (IV : ∀ p ∈ d.pwW.toList, InLong h h.t.qVD h.S.atV p.lam (fun g => g) d.zcW)
    {j : ℕ} (hj : j < 2 * h.S.NP) :
    (K5Law.endsV h K3 (sum3Back d.vpd) h.t.tVD h.t.ptD true h.t.qVD j).value ρ W =
      ρ.val (if j % 2 = 0 then vdA (geoOf h.S) w d d.vpd.r (j / 2)
        else vdB (geoOf h.S) w d (P.eqTab d.zcW) d.vpd.r (j / 2)) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have hb : j / 2 < d.pwW.size := by omega
  have hm := mem_getD d.pwW hb
  have sT : ∀ hi lo : Array E, (P.tok (geoOf h.S) hi lo).size = h.S.T :=
    fun hi lo => OnBytes.Road.Rows.tok_size h.S hi lo
  unfold K5Law.endsV
  rw [hd]
  show (if j % 2 = 0 then
      Fo.planeF h K3 h.t.tVD 3 ((pwBack d.pwW).getD (j / 2) default).lam
          ((pwBack d.pwW).getD (j / 2) default).a h.t.ptD true + Aff.ofConst (ofNat 128) +
        Aff.scale (Fo.planeF h K3 h.t.tVD 4 ((pwBack d.pwW).getD (j / 2) default).lam
          ((pwBack d.pwW).getD (j / 2) default).a h.t.ptD true) (ofNat 256)
    else Aff.ofConst d.gam + Fo.readGroupT h K3 h.t.qVD h.S.atV d.vpd.r d.zcW
        ((pwBack d.pwW).getD (j / 2) default).lam).value ρ W = _
  rw [pwBack_getD d.pwW hb]
  by_cases e : j % 2 = 0
  · rw [if_pos e, if_pos e]
    rw [hpt] at TbS hinS ⊢
    exact weight_meets_on A w hc TbS hps (Pf _ hm).2 (Pf.pair hm) (hinS _ hm)
  · rw [if_neg e, if_neg e, Aff.value_add, Aff.value_ofConst,
      K5Law.readGroupT_val A TbV (sT _ _) hr hzc (IV _ hm)]
    unfold vdB
    rw [ρ.add]
    refine congrArg₂ HAdd.hAdd rfl ?_
    refine (rd3_on _ _ _ _ fun g hg i hi n hn => cells_val hc (Pf _ hm).1 hg hi hn).trans ?_
    exact (read_rd3 ρ (P := ⟨h.S, default⟩) H (r := d.vpd.r) (zc := d.zcW) hr (fun _ _ => rfl)
      ((sT _ _).trans H.T) (fun _ _ => rfl) hzc (fun _ _ => rfl)
      fun g _ i _ n _ => read_v ρ w _ g i n).symm

end H2K5.Honest

#print axioms H2K5.Honest.pwBack_getD
#print axioms H2K5.Honest.mem_getD
#print axioms H2K5.Honest.cells_den
#print axioms H2K5.Honest.cells_qry
#print axioms H2K5.Honest.cells_out
#print axioms H2K5.Honest.cells_key
#print axioms H2K5.Honest.cells_val
#print axioms H2K5.Honest.endsU_meets
#print axioms H2K5.Honest.endsE_meets
#print axioms H2K5.Honest.weight_meets_below
#print axioms H2K5.Honest.weight_meets_on
#print axioms H2K5.Honest.endsV_below_meets
#print axioms H2K5.Honest.endsV_on_meets
