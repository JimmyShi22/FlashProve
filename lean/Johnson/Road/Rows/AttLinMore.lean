-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttLinMore.lean: the claims of the attention sub-proof on the high parts of the
two remainders and on the row maxima, said on cells.

It goes on from Johnson/Road/Rows/AttLin.lean, with the same setting and the same kind of premises.

Main theorems.
 - head_keep: a form overG of xl leaves state and context.
 - ao_aligned; readHead_qh, readHead_qh': the two tensors of the matrix ao as the library's reads.
 - linRh, linRh': a scalar on a high part of a remainder is the batch, over the pairs, of the
   library's extension atY of that part. They serve the scalars rh, rh' (pieces of segment wl) and
   rg, rg' (pieces of segment wh).
 - rd2_reads: a read depends on its point and weights only as far as it reads them.
 - linMsM, linMsD: the scalars on the row maxima of the two units of the scores.
 - linCellD: a scalar on a plane on the diagonal.

What this file does not claim. Nothing is said about probabilities or about hiding. The program
does not import this file.


-/
import Johnson.Road.Rows.AttLin
import Johnson.Road.Rows.AttEnds58ProofsP
import Cb.Pv.Att.Mean.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HFun HTailF2 TenAt tenCell eqTab blockRows)
open OnBytes.Attention (Shape Heard PW Score lessPieces atRh atRhp lastN)
open OnBytes.Road.Hd (Ok)
open Inst.Model.AttSeg (Calls Pub rd2 rd3 eqT sh mxV rv wp atY psiRow blkRow cat)

variable {K : Type} [Field K]

/-- Two reads agree if their points agree on the coordinates that are read and their weights on the
positions. -/
theorem rd2_reads (D : Inst.Model.AttSeg.Dim) {vg vg' Ψ Ψ' : ℕ → K}
    (hg : ∀ j < D.lg, vg j = vg' j) (hΨ : ∀ i < D.T, Ψ i = Ψ' i) (a : ℕ → ℕ → K) :
    rd2 D vg Ψ a = rd2 D vg' Ψ' a := by
  unfold rd2
  refine sum_congr rfl fun g _ => sum_congr rfl fun i hi => ?_
  rw [hΨ i (mem_range.mp hi),
    eqN_agree (a := vg) (a' := vg') (off := 0) (off' := 0)
      (fun k hk => by rw [Nat.zero_add]; exact hg k hk) g]

section Forms

variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls} {p : Pub K}

/-- A form on a table on blocks of features, summed over the heads of keys and values, leaves state
and context. -/
theorem head_keep (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3)
    {t mat wc : ℕ} {X : TenAt} {zg zc tok : Array E} {lam : ℕ} (hdOf : ℕ → ℕ)
    (Tb : TabAt tl h t mat (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (hm : mat < tl.NM) (hM : (tl.mats.getD mat {}).m = wc * h.S.T) (hwc : wc % 2 ^ h.S.ls = 0)
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (hX : ∀ g l, 2 ^ h.S.ls ∣ tenCell X l lam (hdOf g * h.S.dh))
    {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}
    (hq : Ok (Attention.overG h zg fun g => Attention.xl h t X lam (hdOf g) zc) F C q G D) :
    G = F ∧ D = C := by
  have Z := sizes_of_hid A.shape
  obtain ⟨e1, e2, -⟩ := rowOverG_value A hzg _ _
    (fun g _ x G1 D1 hx =>
      xl_value A Z hc Tb hm hM hwc (lowOf_size h.S hzc Z.ls) htok (hX g) hx) hq
  exact ⟨e1, e2⟩

/-- The two tensors of ao begin at a block's first feature, and so does each of their layers and
heads. -/
theorem ao_aligned {S : Shape} (N : L5.Norm S) (Z : Sizes S) (l lam hd : ℕ) :
    2 ^ S.ls ∣ tenCell (atRh S) l lam (hd * S.dh) ∧
      2 ^ S.ls ∣ tenCell (atRhp S) l lam (hd * S.dh) := by
  have hp : 2 ^ S.ls ∣ 2 ^ S.cf.ldh := pow_dvd_pow 2 Z.ls
  have hd' : 2 ^ S.ls ∣ hd * S.dh := by
    rw [N.dh]
    exact Dvd.dvd.mul_left hp _
  have hJ : 2 ^ S.ls ∣ S.dq := by
    rw [N.dq]
    exact Dvd.dvd.mul_left hp _
  refine ⟨ten_dvd ?_ hJ hd' l lam, ten_dvd ?_ hJ hd' l lam⟩
  · show 2 ^ S.ls ∣ S.oRh
    rw [N.oRh]
    exact Nat.dvd_zero _
  · show 2 ^ S.ls ∣ S.oRhp
    rw [N.oRhp]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hp _) _

/-- The matrix ao is in the list. -/
theorem ao_lt (A : AttAt ρ W tl K3 M h lid cf fs) : h.S.cf.NAs + 1 < tl.NM := by
  rw [A.mats.nm]
  omega

variable {F : Fork} {t : ℕ} {zg zc tok : Array E} {lam a : ℕ} {c : Ctx} {q : Aff} {G : Fork}
  {c1 : Ctx}

/-- The high part of the first remainder. -/
theorem readHead_qh (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (Tb : TabAt tl h t (h.S.cf.NAs + 1) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (ha : a < h.S.HA) (hq : Ok (Attention.readHead h t (atRh h.S) zg zc lam a) F c q G c1) :
    G = F ∧ c1 = c ∧
      q.value ρ W = rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
        (fun g i n => cellsK h.S M (.qh (lam * h.S.HA + a) g i n)) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  obtain ⟨k1, k2⟩ := head_keep A hc (fun g => g * h.S.HA + a) Tb (ao_lt A) A.mats.aoM Z.wcO htok
    hzg hzc (fun g l => (ao_aligned N Z l lam _).1) hq
  refine ⟨k1, k2, head_rd3 A hc (fun g => g * h.S.HA + a) Tb (ao_lt A) A.mats.aoM Z.wcO htok hzg
    hzc (fun g l => (ao_aligned N Z l lam _).1) _ (fun g i n => ?_) hq⟩
  show mAt M (L5.featCell h.S (h.S.cf.NAs + 1) h.S.cf.wcO
    (tenCell (atRh h.S) 0 ((lam * h.S.HA + a) / h.S.HA)
      ((g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) * h.S.dh) + n) i) =
    ∑ l ∈ range 1, _
  rw [hb.1, hb.2, sum_range_one, pow_zero, one_mul]

/-- The high part of the second remainder. -/
theorem readHead_qh' (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (Tb : TabAt tl h t (h.S.cf.NAs + 1) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) tok))
    (htok : tok.size = h.S.T) (hzg : h.S.cf.lgk ≤ zg.size) (hzc : zc.size = h.S.cf.ldh)
    (ha : a < h.S.HA) (hq : Ok (Attention.readHead h t (atRhp h.S) zg zc lam a) F c q G c1) :
    G = F ∧ c1 = c ∧
      q.value ρ W = rd3 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (tok.getD i zeroE)) (pt ρ zc)
        (fun g i n => cellsK h.S M (.qh' (lam * h.S.HA + a) g i n)) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hb := pair_parts (lam := lam) ha
  obtain ⟨k1, k2⟩ := head_keep A hc (fun g => g * h.S.HA + a) Tb (ao_lt A) A.mats.aoM Z.wcO htok
    hzg hzc (fun g l => (ao_aligned N Z l lam _).2) hq
  refine ⟨k1, k2, head_rd3 A hc (fun g => g * h.S.HA + a) Tb (ao_lt A) A.mats.aoM Z.wcO htok hzg
    hzc (fun g l => (ao_aligned N Z l lam _).2) _ (fun g i n => ?_) hq⟩
  show mAt M (L5.featCell h.S (h.S.cf.NAs + 1) h.S.cf.wcO
    (tenCell (atRhp h.S) 0 ((lam * h.S.HA + a) / h.S.HA)
      ((g * h.S.HA + (lam * h.S.HA + a) % h.S.HA) * h.S.dh) + n) i) =
    ∑ l ∈ range 1, _
  rw [hb.1, hb.2, sum_range_one, pow_zero, one_mul]

/-- The equality weights of a point of lt coordinates that agrees with v are the library's equality
vector of v over the positions. -/
theorem eqTab_vecT (A : AttAt ρ W tl K3 M h lid cf fs) {zi : Array E} {v : ℕ → K}
    (hzi : zi.size = h.S.cf.lt) (hv : ∀ j < h.S.cf.lt, pt ρ zi j = v j) {i : ℕ}
    (hi : i < (L5.dimOf h.S).T) :
    ρ.val ((eqTab zi).getD i zeroE) = eqT (L5.dimOf h.S) v i := by
  have hlT := dimLT A
  unfold eqT
  rw [hlT]
  refine eqTab_at ρ hzi hv ?_
  rw [← hlT, ← Inst.Model.AttSeg.Dim.T_eq]
  exact hi

/-- A scalar on the high part of the first remainder: the batch over the pairs, under the weights
om, of the library's extension of that part at the lookup's point. s: the scalar's slot; pw, zg, zi,
zc: the pieces and the points of the scalar's segment. -/
theorem linRh (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3) (s : ℕ) {pw : Array PW}
    (P : PiecesAll h.S pw) (om : ℕ → K)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = om b) {zi : Array E}
    (hzg : zg.size = h.S.cf.lgk) (hzi : zi.size = h.S.cf.lt) (hzc : zc.size = h.S.cf.ldh)
    (hg : ∀ j < h.S.cf.lgk, pt ρ zg j = Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z j)
    (hi : ∀ j < h.S.cf.lt, pt ρ zi j = Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z j)
    (hn : ∀ j < h.S.cf.ldh, pt ρ zc j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h h.t.tO (h.S.cf.NAs + 1) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S zc) (eqTab zi)))
    (hq : Ok (lessPieces (Aff.slot s) pw fun w =>
      Attention.readHead h h.t.tO (atRh h.S) zg zc w.lam w.a) F c q G c1)
    (h0 : q.value ρ W = 0) :
    W.slot s = ∑ b ∈ range h.S.NP, om b *
      atY (L5.dimOf h.S) C p fun g i n => cellsK h.S M (.qh b g i n) := by
  have es : (eqTab zi).size = h.S.T := by
    rw [eqTab_size, (sizes_of_hid A.shape).T, hzi]
  refine less_rule ρ W s P _ om _ hw (fun b hb x G1 D1 hx => ?_) hq h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  obtain ⟨a1, a2, a3⟩ := readHead_qh A hc Tb es (Nat.le_of_eq hzg.symm) hzc ha hx
  refine ⟨a1, a2, ?_⟩
  rw [a3, e, ← rd3_atY]
  exact rd3_congr _ hg (fun i hi' => eqTab_vecT A hzi hi hi') hn _

/-- The same for the high part of the second remainder. -/
theorem linRh' (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3) (s : ℕ) {pw : Array PW}
    (P : PiecesAll h.S pw) (om : ℕ → K)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = om b) {zi : Array E}
    (hzg : zg.size = h.S.cf.lgk) (hzi : zi.size = h.S.cf.lt) (hzc : zc.size = h.S.cf.ldh)
    (hg : ∀ j < h.S.cf.lgk, pt ρ zg j = Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z j)
    (hi : ∀ j < h.S.cf.lt, pt ρ zi j = Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z j)
    (hn : ∀ j < h.S.cf.ldh, pt ρ zc j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h h.t.tO (h.S.cf.NAs + 1) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S zc) (eqTab zi)))
    (hq : Ok (lessPieces (Aff.slot s) pw fun w =>
      Attention.readHead h h.t.tO (atRhp h.S) zg zc w.lam w.a) F c q G c1)
    (h0 : q.value ρ W = 0) :
    W.slot s = ∑ b ∈ range h.S.NP, om b *
      atY (L5.dimOf h.S) C p fun g i n => cellsK h.S M (.qh' b g i n) := by
  have es : (eqTab zi).size = h.S.T := by
    rw [eqTab_size, (sizes_of_hid A.shape).T, hzi]
  refine less_rule ρ W s P _ om _ hw (fun b hb x G1 D1 hx => ?_) hq h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  obtain ⟨a1, a2, a3⟩ := readHead_qh' A hc Tb es (Nat.le_of_eq hzg.symm) hzc ha hx
  refine ⟨a1, a2, ?_⟩
  rw [a3, e, ← rd3_atY]
  exact rd3_congr _ hg (fun i hi' => eqTab_vecT A hzi hi hi') hn _

/-! ## The row maxima -/

/-- The scalar on the row maxima of the unit below the diagonal is its rule value. The weights of
the tile rows that the unit stores are asked to be the library's. -/
theorem linMsM (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3) {k : Score} {tM : ℕ}
    (P : PiecesAll h.S k.pw)
    (hw : ∀ b < h.S.NP, ρ.val (k.pw.getD b default).wp = wp (L5.dimOf h.S) C p.z .m2 b)
    (hzg : k.zg.size = h.S.cf.lgk) (hzi : k.zi.size = h.S.cf.lB)
    (hg : ∀ j < h.S.cf.lgk, pt ρ k.zg j = Inst.Model.AttSeg.zg (L5.dimOf h.S) C p.z j)
    (hI : ∀ I < h.S.nT, ρ.val (k.wI.getD I zeroE) =
      blkRow (L5.dimOf h.S) (Inst.Model.AttSeg.zP (L5.dimOf h.S) C p.z)
        (Inst.Model.AttSeg.zs (L5.dimOf h.S) C p.z) I)
    (hi : ∀ j < h.S.cf.lB, pt ρ k.zi j = Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h tM h.S.cf.NAs h.S.T (Attention.tok h.S k.wI k.zi))
    (hq : Ok (lessPieces (Aff.slot (k.s0 + 5)) k.pw fun w =>
      Attention.readMaximum h tM k.zg w.lam w.a) F c q G c1)
    (h0 : q.value ρ W = 0) :
    W.slot (k.s0 + 5) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.ms .M) := by
  have Z := sizes_of_hid A.shape
  refine less_rule ρ W (k.s0 + 5) P _ _
    (fun b => rd2 (L5.dimOf h.S) (Inst.Model.AttSeg.zg (L5.dimOf h.S) C p.z)
      (psiRow (L5.dimOf h.S) (Inst.Model.AttSeg.zP (L5.dimOf h.S) C p.z)
        (Inst.Model.AttSeg.zs (L5.dimOf h.S) C p.z) (Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z))
      (mxV (cellsK h.S M) b)) hw (fun b hb x G1 D1 hx => ?_) hq h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  obtain ⟨a1, a2, a3⟩ := readMaximum_rd2 A hc Tb (Nat.le_of_eq hzg.symm) ha hx
  refine ⟨a1, a2, ?_⟩
  rw [a3, e]
  exact rd2_reads _ hg (fun i hi' => tok_psi ρ Z (dim_T A) hI hzi hi hi') _

/-- The scalar on the row maxima of the unit on the diagonal is its rule value. -/
theorem linMsD (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3) {k : Score} {tM : ℕ}
    (P : PiecesAll h.S k.pw)
    (hw : ∀ b < h.S.NP, ρ.val (k.pw.getD b default).wp = wp (L5.dimOf h.S) C p.z .d2 b)
    (hzg : k.zg.size = h.S.cf.lgk) (hzi : k.zi.size = h.S.cf.lB)
    (hg : ∀ j < h.S.cf.lgk, pt ρ k.zg j = Inst.Model.AttSeg.zgD (L5.dimOf h.S) C p.z j)
    (hI : ∀ I < h.S.nT, ρ.val (k.wI.getD I zeroE) =
      Blocks.eqN ((L5.dimOf h.S).lP + 1) 0 (Inst.Model.AttSeg.zID (L5.dimOf h.S) C p.z) I)
    (hi : ∀ j < h.S.cf.lB, pt ρ k.zi j = Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z j)
    (Tb : TabAt tl h tM h.S.cf.NAs h.S.T (Attention.tok h.S k.wI k.zi))
    (hq : Ok (lessPieces (Aff.slot (k.s0 + 5)) k.pw fun w =>
      Attention.readMaximum h tM k.zg w.lam w.a) F c q G c1)
    (h0 : q.value ρ W = 0) :
    W.slot (k.s0 + 5) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.ms .D) := by
  have Z := sizes_of_hid A.shape
  refine less_rule ρ W (k.s0 + 5) P _ _
    (fun b => rd2 (L5.dimOf h.S) (Inst.Model.AttSeg.zgD (L5.dimOf h.S) C p.z)
      (eqT (L5.dimOf h.S) (cat ((L5.dimOf h.S).lP + 1)
        (Inst.Model.AttSeg.zID (L5.dimOf h.S) C p.z) (Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z)))
      (mxV (cellsK h.S M) b)) hw (fun b hb x G1 D1 hx => ?_) hq h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  obtain ⟨a1, a2, a3⟩ := readMaximum_rd2 A hc Tb (Nat.le_of_eq hzg.symm) ha hx
  refine ⟨a1, a2, ?_⟩
  rw [a3, e]
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

/-! ## A plane on the diagonal -/

/-- A scalar on a plane on the diagonal is its rule value. u: the family (d1 or d2), with its region
D; s0 + jj: the scalar's slot; z: the unit's inner point. -/
theorem linCellD (A : AttAt ρ W tl K3 M h lid cf fs) (hc : Cols F h K3)
    (u : Inst.Model.AttSeg.Fam) (hu : u.reg = .D) (hl : u.l (L5.dimOf h.S) = h.S.nD)
    {pw : Array PW} (P : PiecesAll h.S pw)
    (hw : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) C p.z u b)
    {z : Array E} (hz : z.size = h.S.nD)
    (hv : ∀ j < h.S.nD, pt ρ z j = Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u j)
    (Tb : AsAt h h.t.tA (lastN z h.S.cf.lmS)) (s0 jj : ℕ)
    (hq : Ok (lessPieces (Aff.slot (s0 + jj)) pw fun w =>
      Attention.plane h h.t.tA jj w.lam w.a z true) F c q G c1)
    (h0 : q.value ρ W = 0) :
    W.slot (s0 + jj) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.cell u jj) := by
  refine less_rule ρ W (s0 + jj) P _ _
    (fun b => Blocks.ext (u.l (L5.dimOf h.S)) (fun x => cellsK h.S M (.c u.reg jj b x))
      (Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u)) hw (fun b hb x G1 D1 hx => ?_) hq h0
  obtain ⟨-, ha, e⟩ := piece_at P hb
  obtain ⟨a1, a2, -⟩ := plane_value A hc Tb hx
  refine ⟨a1, a2, ?_⟩
  rw [plane_on A hc Tb hz ha hx, e, hu, hl]
  exact Blocks.ext_congr_point hv _

end Forms

end OnBytes.Road.Rows
