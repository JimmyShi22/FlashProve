-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeysLin.lean: kind K5: the named scalars of the key forms that one
claim ties to a table are their rule values on the cells: twins, for the written forms, of linIb,
linCellM (Johnson/Road/Rows/AttLin.lean) and of readHead_qh, readHead_qh', linRh, linRh',
linMsM, linMsD, linCellD (Johnson/Road/Rows/AttLinMore.lean), which speak of a run of a routine in a
context ("the form has been made"). Here the written forms stand in the run's place; the proofs'
pure parts follow those proofs line for line.

Main names:
  `linIbF`: a bit of the index. (The denominator's twin, linZcF, and the twin of less_rule,
    lessF_rule, stand in Johnson/Desc/First/Att/Claims/LinZc.lean: imported and called.)
  `linCellMF`, `linCellDF`: a scalar on a plane below, on the diagonal.
  `readHeadT_qh`, `readHeadT_qh'`; `linRhF`, `linRhF'`: the high parts of the two remainders (they
    serve rh, rh' at the pieces of segment wl and rg, rg' at those of segment wh).
  `linMsMF`, `linMsDF`: the scalars on the row maxima of the two units of the scores.
The setting and the premises are those of Johnson/Road/Rows (AttAt: every table of the list is true
of the matrices M in W: a premise: the smallness test is there to show it; piece b is pair b; the
pieces' weights and the verifier's points are the library's; the table lies in the list with its
weights). One premise more, as in Johnson/Desc/First/Att/Claims/MeanRd.lean: the indices read lie in
the table, and the heads' features are lawful: those proofs take both from the run's return.
NOT AMONG THEM, AND RIGHTLY: the two scores (ss), the accumulator (acc), the denominator times the
output (zo): no claim ties them to a table (`Linear`, Johnson/Road/Rows/AttBetween.lean): their rule
values are sums of products of cells, which the sumchecks claim.
Used: less the runs, what those two files use; of this folder: lessF_rule (LinZc.lean),
readIndexBitF_rd2, readMaximumF_rd2 (MeanRd.lean), headF_rd3 (MeanRd3.lean),
InLong (EndsE.lean), planeF_on (EndsVA.lean), planeF_below (EndsVB.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttLinMore
import Johnson.Desc.First.Att.Claims.EndsVB
import Johnson.Desc.First.Att.Claims.LinZc

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Calls Pub rd2 rd3 eqT sh denV ibV mxV rv wp atY KSc psiRow blkRow cat)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ}
  {M : Mats Kf} {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
  {C : Calls} {p : Pub Kf}

/-! ## The bits of the index -/

/-- The scalar IB_k is its rule value. -/
theorem linIbF (A : AttAt ρ W tl K3 M h lid cf fs) (P : PiecesAll h.S h.d.pwX)
    (hw : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp (L5.dimOf h.S) C p.z .x3 b)
    (hzg : h.d.zgX.size = h.S.cf.lgk) (hzi : h.d.ziX.size = h.S.cf.lt)
    (hg : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = Inst.Model.AttSeg.xg (L5.dimOf h.S) C p.z j)
    (hi : ∀ j < h.S.cf.lt, pt ρ h.d.ziX j = Inst.Model.AttSeg.xi (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h h.t.hX h.S.cf.NAs h.S.T (eqTab h.d.ziX)) (k : ℕ)
    (hin : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1,
      h.S.oIb + (l * h.S.Lam + (h.d.pwX.getD b default).lam) * (h.S.cf.lt * h.S.cf.H) +
        (k * h.S.cf.H + g * h.S.HA + (h.d.pwX.getD b default).a) <
          (h.t.tabLen.lookup h.t.hX).getD 0)
    (h0 : (Fo.lessF (Aff.slot (h.d.sIB + k)) h.d.pwX fun w =>
      Fo.readIndexBitF h K3 h.t.hX h.d.zgX w.lam w.a k).value ρ W = 0) :
    W.slot (h.d.sIB + k) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.ib k) := by
  refine lessF_rule (h.d.sIB + k) P _ _
    (fun b => rd2 (L5.dimOf h.S) (Inst.Model.AttSeg.xg (L5.dimOf h.S) C p.z)
      (eqT (L5.dimOf h.S) (Inst.Model.AttSeg.xi (L5.dimOf h.S) C p.z))
      (ibV (cellsK h.S M) k b)) hw (fun b hb => ?_) h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  rw [readIndexBitF_rd2 A Tb (Nat.le_of_eq hzg.symm) ha (hin b hb), e]
  exact rd2_pts A hzi hg hi _

/-! ## The planes -/

/-- A scalar on a plane below the diagonal is its rule value. u: the family (m1 or m2); s0 + jj: the
scalar's slot; z: the unit's inner point. -/
theorem linCellMF (A : AttAt ρ W tl K3 M h lid cf fs)
    (u : Inst.Model.AttSeg.Fam) (hu : u.reg = .M) (hl : u.l (L5.dimOf h.S) = h.S.nM)
    {pw : Array PW} (P : PiecesAll h.S pw)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) C p.z u b)
    {z : Array E} (hz : z.size = h.S.nM)
    (hv : ∀ j < h.S.nM, pt ρ z j = Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u j)
    (Tb : AsAt h h.t.tA (lastN z h.S.cf.lmS)) (s0 jj : ℕ)
    (hin : ∀ b < h.S.NP,
      ∀ hi < (eqTab (z.extract 0 ((if false then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S jj (pw.getD b default).lam (pw.getD b default).a false >>> h.S.cf.lmS +
          hi < (h.t.tabLen.lookup h.t.tA).getD 0)
    (h0 : (Fo.lessF (Aff.slot (s0 + jj)) pw fun w =>
      Fo.planeF h K3 h.t.tA jj w.lam w.a z false).value ρ W = 0) :
    W.slot (s0 + jj) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.cell u jj) := by
  refine lessF_rule (s0 + jj) P _ _
    (fun b => Blocks.ext (u.l (L5.dimOf h.S)) (fun x => cellsK h.S M (.c u.reg jj b x))
      (Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u)) hw (fun b hb => ?_) h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  rw [planeF_below A Tb hz ha (hin b hb), e, hu, hl]
  exact Blocks.ext_congr_point hv _

/-- A scalar on a plane on the diagonal is its rule value. u: the family (d1 or d2). -/
theorem linCellDF (A : AttAt ρ W tl K3 M h lid cf fs)
    (u : Inst.Model.AttSeg.Fam) (hu : u.reg = .D) (hl : u.l (L5.dimOf h.S) = h.S.nD)
    {pw : Array PW} (P : PiecesAll h.S pw)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) C p.z u b)
    {z : Array E} (hz : z.size = h.S.nD)
    (hv : ∀ j < h.S.nD, pt ρ z j = Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u j)
    (Tb : AsAt h h.t.tA (lastN z h.S.cf.lmS)) (s0 jj : ℕ)
    (hin : ∀ b < h.S.NP,
      ∀ hi < (eqTab (z.extract 0 ((if true then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S jj (pw.getD b default).lam (pw.getD b default).a true >>> h.S.cf.lmS +
          hi < (h.t.tabLen.lookup h.t.tA).getD 0)
    (h0 : (Fo.lessF (Aff.slot (s0 + jj)) pw fun w =>
      Fo.planeF h K3 h.t.tA jj w.lam w.a z true).value ρ W = 0) :
    W.slot (s0 + jj) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.cell u jj) := by
  refine lessF_rule (s0 + jj) P _ _
    (fun b => Blocks.ext (u.l (L5.dimOf h.S)) (fun x => cellsK h.S M (.c u.reg jj b x))
      (Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u)) hw (fun b hb => ?_) h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  rw [planeF_on A Tb hz ha (hin b hb), e, hu, hl]
  exact Blocks.ext_congr_point hv _

/-! ## The high parts of the two remainders -/

section Heads
variable {t : ℕ} {zg zc tok : Array E} {lam a : ℕ}

/-- The high part of the first remainder. -/
theorem readHeadT_qh (A : AttAt ρ W tl K3 M h lid cf fs)
    (Tb : TabAt tl h t (h.S.cf.NAs + 1) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (ha : a < h.S.HA) (I : InLong h t (atRh h.S) lam (fun g => g * h.S.HA + a) zc) :
    (Fo.readHeadT h K3 t (atRh h.S) zg zc lam a).value ρ W =
      rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
        (fun g i n => cellsK h.S M (.qh (lam * h.S.HA + a) g i n)) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  unfold Fo.readHeadT
  refine headF_rd3 A (fun g => g * h.S.HA + a) Tb (ao_lt A) A.mats.aoM Z.wcO htok hzg hzc
    (fun g l => (ao_aligned N Z l lam _).1) _ (fun g i n => ?_) I.feat I.inn
  show mAt M (L5.featCell h.S (h.S.cf.NAs + 1) h.S.cf.wcO
    (tenCell (atRh h.S) 0 ((lam * h.S.HA + a) / h.S.HA)
      ((g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) * h.S.dh) + n) i) =
    ∑ l ∈ range 1, _
  rw [hb.1, hb.2, sum_range_one, pow_zero, one_mul]

/-- The high part of the second remainder. -/
theorem readHeadT_qh' (A : AttAt ρ W tl K3 M h lid cf fs)
    (Tb : TabAt tl h t (h.S.cf.NAs + 1) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (ha : a < h.S.HA) (I : InLong h t (atRhp h.S) lam (fun g => g * h.S.HA + a) zc) :
    (Fo.readHeadT h K3 t (atRhp h.S) zg zc lam a).value ρ W =
      rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
        (fun g i n => cellsK h.S M (.qh' (lam * h.S.HA + a) g i n)) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  unfold Fo.readHeadT
  refine headF_rd3 A (fun g => g * h.S.HA + a) Tb (ao_lt A) A.mats.aoM Z.wcO htok hzg hzc
    (fun g l => (ao_aligned N Z l lam _).2) _ (fun g i n => ?_) I.feat I.inn
  show mAt M (L5.featCell h.S (h.S.cf.NAs + 1) h.S.cf.wcO
    (tenCell (atRhp h.S) 0 ((lam * h.S.HA + a) / h.S.HA)
      ((g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) * h.S.dh) + n) i) =
    ∑ l ∈ range 1, _
  rw [hb.1, hb.2, sum_range_one, pow_zero, one_mul]

/-- A scalar on the high part of the first remainder: the batch over the pairs, under the weights
om, of the library's extension of that part at the lookup's point. s: the scalar's slot; pw, zg, zi,
zc: the pieces and the points of the scalar's segment. -/
theorem linRhF (A : AttAt ρ W tl K3 M h lid cf fs) (s : ℕ) {pw : Array PW}
    (P : PiecesAll h.S pw) (om : ℕ → Kf)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = om b) {zi : Array E}
    (hzg : zg.size = h.S.cf.lgk) (hzi : zi.size = h.S.cf.lt) (hzc : zc.size = h.S.cf.ldh)
    (hg : ∀ j < h.S.cf.lgk, pt ρ zg j = Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z j)
    (hi : ∀ j < h.S.cf.lt, pt ρ zi j = Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z j)
    (hn : ∀ j < h.S.cf.ldh, pt ρ zc j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h h.t.tO (h.S.cf.NAs + 1) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S zc) (eqTab zi)))
    (I : ∀ b < h.S.NP, InLong h h.t.tO (atRh h.S) (pw.getD b default).lam
      (fun g => g * h.S.HA + (pw.getD b default).a) zc)
    (h0 : (Fo.lessF (Aff.slot s) pw fun w =>
      Fo.readHeadT h K3 h.t.tO (atRh h.S) zg zc w.lam w.a).value ρ W = 0) :
    W.slot s = ∑ b ∈ range h.S.NP, om b *
      atY (L5.dimOf h.S) C p fun g i n => cellsK h.S M (.qh b g i n) := by
  have es : (eqTab zi).size = h.S.T := by
    rw [OnBytes.Road.eqTab_size, (sizes_of_hid A.shape).T, hzi]
  refine lessF_rule s P _ om _ hw (fun b hb => ?_) h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  rw [readHeadT_qh A Tb es (Nat.le_of_eq hzg.symm) hzc ha (I b hb), e, ← rd3_atY]
  exact rd3_congr _ hg (fun i hi' => eqTab_vecT A hzi hi hi') hn _

/-- The same for the high part of the second remainder. -/
theorem linRhF' (A : AttAt ρ W tl K3 M h lid cf fs) (s : ℕ) {pw : Array PW}
    (P : PiecesAll h.S pw) (om : ℕ → Kf)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = om b) {zi : Array E}
    (hzg : zg.size = h.S.cf.lgk) (hzi : zi.size = h.S.cf.lt) (hzc : zc.size = h.S.cf.ldh)
    (hg : ∀ j < h.S.cf.lgk, pt ρ zg j = Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z j)
    (hi : ∀ j < h.S.cf.lt, pt ρ zi j = Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z j)
    (hn : ∀ j < h.S.cf.ldh, pt ρ zc j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h h.t.tO (h.S.cf.NAs + 1) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S zc) (eqTab zi)))
    (I : ∀ b < h.S.NP, InLong h h.t.tO (atRhp h.S) (pw.getD b default).lam
      (fun g => g * h.S.HA + (pw.getD b default).a) zc)
    (h0 : (Fo.lessF (Aff.slot s) pw fun w =>
      Fo.readHeadT h K3 h.t.tO (atRhp h.S) zg zc w.lam w.a).value ρ W = 0) :
    W.slot s = ∑ b ∈ range h.S.NP, om b *
      atY (L5.dimOf h.S) C p fun g i n => cellsK h.S M (.qh' b g i n) := by
  have es : (eqTab zi).size = h.S.T := by
    rw [OnBytes.Road.eqTab_size, (sizes_of_hid A.shape).T, hzi]
  refine lessF_rule s P _ om _ hw (fun b hb => ?_) h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  rw [readHeadT_qh' A Tb es (Nat.le_of_eq hzg.symm) hzc ha (I b hb), e, ← rd3_atY]
  exact rd3_congr _ hg (fun i hi' => eqTab_vecT A hzi hi hi') hn _

end Heads

/-! ## The row maxima -/

/-- The scalar on the row maxima of the unit below the diagonal is its rule value. -/
theorem linMsMF (A : AttAt ρ W tl K3 M h lid cf fs) {k : Score} {tM : ℕ}
    (P : PiecesAll h.S k.pw)
    (hw : ∀ b < h.S.NP, ρ.val (k.pw.getD b default).wp = wp (L5.dimOf h.S) C p.z .m2 b)
    (hzg : k.zg.size = h.S.cf.lgk) (hzi : k.zi.size = h.S.cf.lB)
    (hg : ∀ j < h.S.cf.lgk, pt ρ k.zg j = Inst.Model.AttSeg.zg (L5.dimOf h.S) C p.z j)
    (hI : ∀ I < h.S.nT, ρ.val (k.wI.getD I zeroE) =
      blkRow (L5.dimOf h.S) (Inst.Model.AttSeg.zP (L5.dimOf h.S) C p.z)
        (Inst.Model.AttSeg.zs (L5.dimOf h.S) C p.z) I)
    (hi : ∀ j < h.S.cf.lB, pt ρ k.zi j = Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h tM h.S.cf.NAs h.S.T (Attention.tok h.S k.wI k.zi))
    (hin : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4,
      h.S.oMr + (l * h.S.Lam + (k.pw.getD b default).lam) * h.S.cf.H +
        (g * h.S.HA + (k.pw.getD b default).a) < (h.t.tabLen.lookup tM).getD 0)
    (h0 : (Fo.lessF (Aff.slot (k.s0 + 5)) k.pw fun w =>
      Fo.readMaximumF h K3 tM k.zg w.lam w.a).value ρ W = 0) :
    W.slot (k.s0 + 5) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.ms .M) := by
  have Z := sizes_of_hid A.shape
  refine lessF_rule (k.s0 + 5) P _ _
    (fun b => rd2 (L5.dimOf h.S) (Inst.Model.AttSeg.zg (L5.dimOf h.S) C p.z)
      (psiRow (L5.dimOf h.S) (Inst.Model.AttSeg.zP (L5.dimOf h.S) C p.z)
        (Inst.Model.AttSeg.zs (L5.dimOf h.S) C p.z) (Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z))
      (mxV (cellsK h.S M) b)) hw (fun b hb => ?_) h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  rw [readMaximumF_rd2 A Tb (Nat.le_of_eq hzg.symm) ha (hin b hb), e]
  exact rd2_reads _ hg (fun i hi' => tok_psi ρ Z (dim_T A) hI hzi hi hi') _

/-- The scalar on the row maxima of the unit on the diagonal is its rule value. -/
theorem linMsDF (A : AttAt ρ W tl K3 M h lid cf fs) {k : Score} {tM : ℕ}
    (P : PiecesAll h.S k.pw)
    (hw : ∀ b < h.S.NP, ρ.val (k.pw.getD b default).wp = wp (L5.dimOf h.S) C p.z .d2 b)
    (hzg : k.zg.size = h.S.cf.lgk) (hzi : k.zi.size = h.S.cf.lB)
    (hg : ∀ j < h.S.cf.lgk, pt ρ k.zg j = Inst.Model.AttSeg.zgD (L5.dimOf h.S) C p.z j)
    (hI : ∀ I < h.S.nT, ρ.val (k.wI.getD I zeroE) =
      Blocks.eqN ((L5.dimOf h.S).lP + 1) 0 (Inst.Model.AttSeg.zID (L5.dimOf h.S) C p.z) I)
    (hi : ∀ j < h.S.cf.lB, pt ρ k.zi j = Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h tM h.S.cf.NAs h.S.T (Attention.tok h.S k.wI k.zi))
    (hin : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4,
      h.S.oMr + (l * h.S.Lam + (k.pw.getD b default).lam) * h.S.cf.H +
        (g * h.S.HA + (k.pw.getD b default).a) < (h.t.tabLen.lookup tM).getD 0)
    (h0 : (Fo.lessF (Aff.slot (k.s0 + 5)) k.pw fun w =>
      Fo.readMaximumF h K3 tM k.zg w.lam w.a).value ρ W = 0) :
    W.slot (k.s0 + 5) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.ms .D) := by
  have Z := sizes_of_hid A.shape
  refine lessF_rule (k.s0 + 5) P _ _
    (fun b => rd2 (L5.dimOf h.S) (Inst.Model.AttSeg.zgD (L5.dimOf h.S) C p.z)
      (eqT (L5.dimOf h.S) (cat ((L5.dimOf h.S).lP + 1)
        (Inst.Model.AttSeg.zID (L5.dimOf h.S) C p.z) (Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z)))
      (mxV (cellsK h.S M) b)) hw (fun b hb => ?_) h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  rw [readMaximumF_rd2 A Tb (Nat.le_of_eq hzg.symm) ha (hin b hb), e]
  refine rd2_reads _ hg (fun i hi' => ?_) _
  rw [tok_psi ρ Z (dim_T A) hI hzi hi hi']
  show _ = Blocks.eqN ((L5.dimOf h.S).lP + 1 + (L5.dimOf h.S).lB) 0 _ i
  have hpos : 0 < 2 ^ (L5.dimOf h.S).lB := Nat.two_pow_pos _
  have hsplit : i = i / 2 ^ (L5.dimOf h.S).lB * 2 ^ (L5.dimOf h.S).lB +
      i % 2 ^ (L5.dimOf h.S).lB := (Nat.div_add_mod' i _).symm
  rw [eqN_cat]
  conv_rhs => rw [hsplit, eqN_low _ _ _ (Nat.mod_lt _ hpos)]
  rw [← hsplit]
  exact mul_comm _ _

end K5Law

#print axioms K5Law.linIbF
#print axioms K5Law.linCellMF
#print axioms K5Law.linCellDF
#print axioms K5Law.linRhF
#print axioms K5Law.linRhF'
#print axioms K5Law.linMsMF
#print axioms K5Law.linMsDF
