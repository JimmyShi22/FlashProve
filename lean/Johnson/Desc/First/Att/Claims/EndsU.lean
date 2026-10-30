-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsU.lean: kind K5: the end values of a softmax-table unit's sumcheck
(query · key): twins, for the written forms, of ScoreFdEnd and ScoreFmEnd
(Johnson/Road/Rows/AttEnds14.lean; proved in Johnson/Road/Rows/AttEnds14Tiles.lean of runs of
routines in a context).

Main names:
  `score_fd`: a unit on the diagonal: W.slot (sc.sEnd + 2 b) = Aext … .s6d (w.lam HA + w.a) (pt ρ
    sc.r) ∧ W.slot (sc.sEnd + (2 b + 1)) = Bext … .s6d ….
  `score_fm`: a unit below the diagonal: the same at .s6b.
The two proofs' texts are those of Johnson/Road/Rows/AttEnds14Tiles.lean, turned in five places
each: the run's lemma to the written form's (readHead_qry → readHeadT_qry, readGroup_key →
readGroupT_key) and the claims "slot − form is worth 0" to the equations "slot = form's worth" that
Johnson/Desc/First/Att/Claims/Say.lean gives.
lastCoords k.sc.r ldh is the cut in endsU (k.sc.r.extract (size − ldh) size) by definition.
What these reach, and what not: as the head of Johnson/Desc/First/Att/Claims/EndsQ.lean says.
Premises beyond those of Johnson/Road/Rows: InLong at the two tables.
Used: as Johnson/Desc/First/Att/Claims/EndsE.lean, and scoreTiles_fd, scoreTiles_fm, tok_psi,
tiles_row, tiles_col, tok_size, aext6d, bext6d, aext6b, bext6b, sizeCut, ptCut, eqTab_at,
Attention.scoreTiles, tok, lastCoords; the library's zi', zj'.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds14Tiles
import Johnson.Desc.First.Att.Claims.EndsE

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Calls Pub rd2 rd3 eqT sh qryV outV keyV valV denV wtV Aext Bext blkRow blkCol psiRow
  psiCol)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- **The twin of ScoreFdEnd**: a unit on the diagonal. -/
theorem score_fd (A : AttAt ρ W tl K3 M h lid cf fs) (C : Calls) (p : Pub Kf) {k : Score}
    {tb : ScoreTables} {b : ℕ} {w : PW} (hseg : k.seg = Attention.Seg.fd) (hr : k.sc.r.size = h.S.nvKF Attention.Seg.fd)
    (hzi : k.zi.size = h.S.cf.lB) (hzj : k.zj.size = h.S.cf.lB) (ha : w.a < h.S.HA)
    (hvi : ∀ j < h.S.cf.lB, pt ρ k.zi j = Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z j)
    (hvj : ∀ j < h.S.cf.lB, pt ρ k.zj j = Inst.Model.AttSeg.zj' (L5.dimOf h.S) C p.z j)
    (TbQ : TabAt tl h tb.tQ (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).1 k.zi)))
    (TbK : TabAt tl h tb.tK (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).2 k.zj)))
    (IQ : InLong h tb.tQ h.S.atQ w.lam (fun g => g * h.S.HA + w.a) (lastCoords k.sc.r h.S.cf.ldh))
    (IK : InLong h tb.tK h.S.atK w.lam (fun g => g) (lastCoords k.sc.r h.S.cf.ldh))
    (vq : W.slot (k.sc.sEnd + 2 * b) = (Fo.readHeadT h K3 tb.tQ h.S.atQ k.sc.r
      (lastCoords k.sc.r h.S.cf.ldh) w.lam w.a).value ρ W)
    (vk : W.slot (k.sc.sEnd + (2 * b + 1)) = (Fo.readGroupT h K3 tb.tK h.S.atK k.sc.r
      (lastCoords k.sc.r h.S.cf.ldh) w.lam).value ρ W) :
    W.slot (k.sc.sEnd + 2 * b) =
        Aext (L5.dimOf h.S) C p (cellsK h.S M) .s6d (w.lam * h.S.HA + w.a) (pt ρ k.sc.r) ∧
      W.slot (k.sc.sEnd + (2 * b + 1)) =
        Bext (L5.dimOf h.S) C p (cellsK h.S M) .s6d (w.lam * h.S.HA + w.a) (pt ρ k.sc.r) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hT := dim_T A
  have hl := Z.lnT
  have hr' : k.sc.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.ldh := hr
  have hrc : (lastCoords k.sc.r h.S.cf.ldh).size = h.S.cf.ldh := by
    unfold Attention.lastCoords
    rw [sizeCut _ (Nat.le_refl _)]
    omega
  have e1 := readHeadT_qry A (zg := k.sc.r) TbQ (tok_size _ _ _) (by omega) hrc ha IQ
  have e2 := readGroupT_key A (zg := k.sc.r) TbK (tok_size _ _ _) (by omega) hrc IK
  rw [e1] at vq
  rw [e2] at vk
  have hn : ∀ j < (L5.dimOf h.S).ln, pt ρ (lastCoords k.sc.r h.S.cf.ldh) j =
      sh (pt ρ k.sc.r) ((L5.dimOf h.S).lg + ((L5.dimOf h.S).lP + 1)) j := by
    intro j hj
    have hj' : j < h.S.cf.ldh := hj
    unfold Attention.lastCoords
    rw [ptCut ρ _ (Nat.le_refl _) (by omega)]
    show _ = pt ρ k.sc.r (h.S.cf.lgk + (h.S.lnT - 1 + 1) + j)
    congr 1
    omega
  have hI : ∀ I < h.S.nT,
      ρ.val ((eqTab (k.sc.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT))).getD I zeroE) =
        Blocks.eqN ((L5.dimOf h.S).lP + 1) 0 (sh (pt ρ k.sc.r) (L5.dimOf h.S).lg) I := by
    intro I hI'
    have e : (L5.dimOf h.S).lP + 1 = h.S.lnT := by
      show h.S.lnT - 1 + 1 = h.S.lnT
      omega
    rw [e]
    refine eqTab_at ρ (by rw [sizeCut _ (by omega)]; omega) (fun j hj => ?_)
      (by rw [← Z.nT]; exact hI')
    exact ptCut ρ _ (by omega) (by omega)
  have hlam : (L5.dimOf h.S).lamOf (w.lam * h.S.HA + w.a) = w.lam := (pair_parts ha).1
  rw [scoreTiles_fd h.S hseg] at vq vk
  refine ⟨?_, ?_⟩
  · rw [vq, aext6d]
    exact rd3_congr _ (fun _ _ => rfl) (fun i hi => tok_psi ρ Z hT hI hzi hvi hi) hn _
  · rw [vk, bext6d, hlam]
    exact rd3_congr _ (fun _ _ => rfl) (fun i hi => tok_psi ρ Z hT hI hzj hvj hi) hn _

/-- **The twin of ScoreFmEnd**: a unit below the diagonal. -/
theorem score_fm (A : AttAt ρ W tl K3 M h lid cf fs) (C : Calls) (p : Pub Kf) {k : Score}
    {tb : ScoreTables} {b : ℕ} {w : PW} (hseg : k.seg = Attention.Seg.fm) (hr : k.sc.r.size = h.S.nvKF Attention.Seg.fm)
    (hzi : k.zi.size = h.S.cf.lB) (hzj : k.zj.size = h.S.cf.lB) (ha : w.a < h.S.HA)
    (hvi : ∀ j < h.S.cf.lB, pt ρ k.zi j = Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z j)
    (hvj : ∀ j < h.S.cf.lB, pt ρ k.zj j = Inst.Model.AttSeg.zj' (L5.dimOf h.S) C p.z j)
    (TbQ : TabAt tl h tb.tQ (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).1 k.zi)))
    (TbK : TabAt tl h tb.tK (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).2 k.zj)))
    (IQ : InLong h tb.tQ h.S.atQ w.lam (fun g => g * h.S.HA + w.a) (lastCoords k.sc.r h.S.cf.ldh))
    (IK : InLong h tb.tK h.S.atK w.lam (fun g => g) (lastCoords k.sc.r h.S.cf.ldh))
    (vq : W.slot (k.sc.sEnd + 2 * b) = (Fo.readHeadT h K3 tb.tQ h.S.atQ k.sc.r
      (lastCoords k.sc.r h.S.cf.ldh) w.lam w.a).value ρ W)
    (vk : W.slot (k.sc.sEnd + (2 * b + 1)) = (Fo.readGroupT h K3 tb.tK h.S.atK k.sc.r
      (lastCoords k.sc.r h.S.cf.ldh) w.lam).value ρ W) :
    W.slot (k.sc.sEnd + 2 * b) =
        Aext (L5.dimOf h.S) C p (cellsK h.S M) .s6b (w.lam * h.S.HA + w.a) (pt ρ k.sc.r) ∧
      W.slot (k.sc.sEnd + (2 * b + 1)) =
        Bext (L5.dimOf h.S) C p (cellsK h.S M) .s6b (w.lam * h.S.HA + w.a) (pt ρ k.sc.r) := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hT := dim_T A
  have hl := Z.lnT
  have hr' : k.sc.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.ldh := hr
  have hrc : (lastCoords k.sc.r h.S.cf.ldh).size = h.S.cf.ldh := by
    unfold Attention.lastCoords
    rw [sizeCut _ (Nat.le_refl _)]
    omega
  have e1 := readHeadT_qry A (zg := k.sc.r) TbQ (tok_size _ _ _) (by omega) hrc ha IQ
  have e2 := readGroupT_key A (zg := k.sc.r) TbK (tok_size _ _ _) (by omega) hrc IK
  rw [e1] at vq
  rw [e2] at vk
  have hn : ∀ j < (L5.dimOf h.S).ln, pt ρ (lastCoords k.sc.r h.S.cf.ldh) j =
      sh (pt ρ k.sc.r)
        ((L5.dimOf h.S).lg + (L5.dimOf h.S).lP + ((L5.dimOf h.S).lP + 1)) j := by
    intro j hj
    have hj' : j < h.S.cf.ldh := hj
    unfold Attention.lastCoords
    rw [ptCut ρ _ (Nat.le_refl _) (by omega)]
    show _ = pt ρ k.sc.r (h.S.cf.lgk + (h.S.lnT - 1) + (h.S.lnT - 1 + 1) + j)
    congr 1
    omega
  have sP : (k.sc.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT - 1)).size = h.S.lnT - 1 := by
    rw [sizeCut _ (by omega)]
    omega
  have sS : (k.sc.r.extract (h.S.cf.lgk + h.S.lnT - 1) (h.S.cf.lgk + 2 * h.S.lnT - 1)).size =
      h.S.lnT := by
    rw [sizeCut _ (by omega)]
    omega
  have vP : ∀ j < h.S.lnT - 1, pt ρ (k.sc.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT - 1)) j =
      sh (pt ρ k.sc.r) (L5.dimOf h.S).lg j := fun j hj => ptCut ρ _ (by omega) (by omega)
  have vS : ∀ j < h.S.lnT,
      pt ρ (k.sc.r.extract (h.S.cf.lgk + h.S.lnT - 1) (h.S.cf.lgk + 2 * h.S.lnT - 1)) j =
        sh (pt ρ k.sc.r) ((L5.dimOf h.S).lg + (L5.dimOf h.S).lP) j := by
    intro j hj
    rw [ptCut ρ _ (by omega) (by omega)]
    show _ = pt ρ k.sc.r (h.S.cf.lgk + (h.S.lnT - 1) + j)
    congr 1
    omega
  have hlam : (L5.dimOf h.S).lamOf (w.lam * h.S.HA + w.a) = w.lam := (pair_parts ha).1
  rw [scoreTiles_fm h.S hseg] at vq vk
  refine ⟨?_, ?_⟩
  · rw [vq, aext6b]
    exact rd3_congr _ (fun _ _ => rfl)
      (fun i hi => tok_psi ρ Z hT (fun I hI => tiles_row ρ Z sP sS vP vS hI) hzi hvi hi) hn _
  · rw [vk, bext6b, hlam]
    exact rd3_congr _ (fun _ _ => rfl)
      (fun i hi => tok_psi ρ Z hT (fun I hI => tiles_col ρ Z sP sS vP vS hI) hzj hvj hi) hn _

end K5Law
