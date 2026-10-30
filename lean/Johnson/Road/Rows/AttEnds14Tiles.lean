-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEnds14Tiles.lean: proofs of the two statements of
Johnson/Road/Rows/AttEnds14.lean on the scores.

Beside what Johnson/Road/Rows/AttEnds14Proofs.lean uses, these proofs need that the verifier's
weights on tiles and tokens are the library's (blkRow, blkCol, psiRow, psiCol, and the weights of a
diagonal block).

Main theorems: dim_hP, dim_nBlk, dim_B, cover_blk; eqTab_at, tiles_row, tiles_col, tok_psi;
scoreTiles_fm, scoreTiles_fd; ptCut, sizeCut; scoreFdEnd, scoreFmEnd. The value product below the
diagonal is in Johnson/Road/Rows/AttEnds14Below.lean.

Nothing is said about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttEnds14Proofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HFun HTailF2 TenAt tenCell eqTab blockRows)
open OnBytes.Attention (Shape Heard Score sc3A sc3B lastCoords)
open OnBytes.Road.Hd (Ok)
open Inst.Model.AttSeg (rd2 rd3 eqT sh qryV outV keyV valV denV wtV Aext Bext blkRow blkCol psiRow
  psiCol)

variable {K : Type} [Field K]

/-! ## The sizes of the tiles -/

section Sizes
variable {S : Shape} (Z : Sizes S)
include Z

/-- The slot rows. -/
theorem dim_hP : S.hP = (L5.dimOf S).hP := by
  show S.hP = 2 ^ (S.lnT - 1)
  have e : S.lnT = S.lnT - 1 + 1 := by have := Z.lnT; omega
  rw [Z.hP, e, pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]

/-- The tiles along a side. -/
theorem dim_nBlk : S.nT = (L5.dimOf S).nBlk := by
  show S.nT = 2 * 2 ^ (S.lnT - 1)
  have e : S.lnT = S.lnT - 1 + 1 := by have := Z.lnT; omega
  rw [Z.nT]
  conv_lhs => rw [e, pow_succ]
  ring

/-- The side of a tile. -/
theorem dim_B : S.B = (L5.dimOf S).B := Z.B

/-- The tile of a tile slot is the library's pair of blocks. -/
theorem cover_blk (P s : ℕ) :
    (S.cover P s).1 = (L5.dimOf S).rowBlk P s ∧ (S.cover P s).2 = (L5.dimOf S).colBlk P s := by
  unfold Attention.Shape.cover Inst.Model.AttSeg.Dim.rowBlk Inst.Model.AttSeg.Dim.colBlk
  by_cases c : s < P
  · rw [if_pos c, if_pos c, if_pos c]
    exact ⟨rfl, rfl⟩
  · rw [if_neg c, if_neg c, if_neg c, dim_nBlk Z]
    exact ⟨rfl, rfl⟩

end Sizes

/-! ## The weights on tiles and tokens -/

section Weights
variable (ρ : Reading K)

/-- An entry of a table of equality weights, at a point that agrees with v. -/
theorem eqTab_at {z : Array E} {n : ℕ} (hz : z.size = n) {v : ℕ → K}
    (hv : ∀ j < n, pt ρ z j = v j) {c : ℕ} (hc : c < 2 ^ n) :
    ρ.val ((eqTab z).getD c zeroE) = Blocks.eqN n 0 v c := by
  rw [eqTab_value ρ z c (by rw [hz]; exact hc), hz]
  exact eqN_agree (fun k hk => by rw [Nat.zero_add]; exact hv k hk) c

variable {S : Shape} (Z : Sizes S)
include Z

/-- The verifier's weight of a tile row is the library's weight of the row block. -/
theorem tiles_row {zP zs : Array E} {vP vs : ℕ → K} (hP : zP.size = S.lnT - 1)
    (hs : zs.size = S.lnT) (hvP : ∀ j < S.lnT - 1, pt ρ zP j = vP j)
    (hvs : ∀ j < S.lnT, pt ρ zs j = vs j) {I : ℕ} (hI : I < S.nT) :
    ρ.val ((Attention.tileSums S (eqTab zP) (eqTab zs)).1.getD I zeroE) =
      blkRow (L5.dimOf S) vP vs I := by
  have e : S.lnT = S.lnT - 1 + 1 := by have := Z.lnT; omega
  rw [tileSums_fst ρ S _ _ hI, dim_hP Z, dim_nBlk Z]
  unfold blkRow
  refine sum_congr rfl fun P hP' => sum_congr rfl fun s hs' => ?_
  have h1 : P < 2 ^ (S.lnT - 1) := mem_range.mp hP'
  have h2 : s < 2 ^ S.lnT := by
    have h3 : s < (L5.dimOf S).nBlk - 1 := mem_range.mp hs'
    rw [← dim_nBlk Z, Z.nT] at h3
    omega
  rw [(cover_blk Z P s).1, eqTab_at ρ hP hvP h1, eqTab_at ρ hs hvs h2]
  show _ = if _ then Blocks.eqN (S.lnT - 1) 0 vP P * Blocks.eqN (S.lnT - 1 + 1) 0 vs s else 0
  rw [← e]

/-- The same for a tile column. -/
theorem tiles_col {zP zs : Array E} {vP vs : ℕ → K} (hP : zP.size = S.lnT - 1)
    (hs : zs.size = S.lnT) (hvP : ∀ j < S.lnT - 1, pt ρ zP j = vP j)
    (hvs : ∀ j < S.lnT, pt ρ zs j = vs j) {J : ℕ} (hJ : J < S.nT) :
    ρ.val ((Attention.tileSums S (eqTab zP) (eqTab zs)).2.getD J zeroE) =
      blkCol (L5.dimOf S) vP vs J := by
  have e : S.lnT = S.lnT - 1 + 1 := by have := Z.lnT; omega
  rw [tileSums_snd ρ S _ _ hJ, dim_hP Z, dim_nBlk Z]
  unfold blkCol
  refine sum_congr rfl fun P hP' => sum_congr rfl fun s hs' => ?_
  have h1 : P < 2 ^ (S.lnT - 1) := mem_range.mp hP'
  have h2 : s < 2 ^ S.lnT := by
    have h3 : s < (L5.dimOf S).nBlk - 1 := mem_range.mp hs'
    rw [← dim_nBlk Z, Z.nT] at h3
    omega
  rw [(cover_blk Z P s).2, eqTab_at ρ hP hvP h1, eqTab_at ρ hs hvs h2]
  show _ = if _ then Blocks.eqN (S.lnT - 1) 0 vP P * Blocks.eqN (S.lnT - 1 + 1) 0 vs s else 0
  rw [← e]

/-- The verifier's weight of a token, from the weights w of the tiles and a point v in the tile. -/
theorem tok_psi {hi lo : Array E} {w v : ℕ → K} (hT : (L5.dimOf S).T = S.T)
    (hhi : ∀ I < S.nT, ρ.val (hi.getD I zeroE) = w I) (hlo : lo.size = S.cf.lB)
    (hv : ∀ j < S.cf.lB, pt ρ lo j = v j) {i : ℕ} (h : i < (L5.dimOf S).T) :
    ρ.val ((Attention.tok S hi lo).getD i zeroE) =
      Blocks.eqN (L5.dimOf S).lB 0 v (i % (L5.dimOf S).B) * w (i / (L5.dimOf S).B) := by
  have hB := dim_B Z
  have hpos : 0 < (L5.dimOf S).B := (L5.dimOf S).B_pos
  have h1 : i / (L5.dimOf S).B < S.nT := by
    rw [dim_nBlk Z]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
  have h2 : i % (L5.dimOf S).B < 2 ^ S.cf.lB := Nat.mod_lt _ hpos
  rw [tok_value ρ S hi lo (by rw [← hT]; exact h), hB, hhi _ h1, eqTab_at ρ hlo hv h2]
  exact mul_comm _ _

end Weights

/-- The tile weights of a unit below the diagonal. -/
theorem scoreTiles_fm (S : Shape) {k : Score} (h : k.seg = .fm) :
    Attention.scoreTiles S k = Attention.tileSums S
      (eqTab (k.sc.r.extract S.cf.lgk (S.cf.lgk + S.lnT - 1)))
      (eqTab (k.sc.r.extract (S.cf.lgk + S.lnT - 1) (S.cf.lgk + 2 * S.lnT - 1))) := by
  unfold Attention.scoreTiles
  dsimp only
  rw [h]
  rfl

/-- The tile weights of a unit on the diagonal. -/
theorem scoreTiles_fd (S : Shape) {k : Score} (h : k.seg = .fd) :
    Attention.scoreTiles S k =
      (eqTab (k.sc.r.extract S.cf.lgk (S.cf.lgk + S.lnT)),
        eqTab (k.sc.r.extract S.cf.lgk (S.cf.lgk + S.lnT))) := by
  unfold Attention.scoreTiles
  dsimp only
  rw [h]
  rfl

/-- A coordinate of a stretch of a point. -/
theorem ptCut (ρ : Reading K) (z : Array E) {a b j : ℕ} (hb : b ≤ z.size) (hj : a + j < b) :
    pt ρ (z.extract a b) j = pt ρ z (a + j) := by
  unfold pt
  rw [getD_extract z hb hj]

/-- The length of a stretch of a point. -/
theorem sizeCut (z : Array E) {a b : ℕ} (hb : b ≤ z.size) : (z.extract a b).size = b - a := by
  rw [Array.size_extract]
  omega

/-! ## The scores -/

/-- The score of a unit on the diagonal. -/
theorem scoreFdEnd : ScoreFdEnd := by
  intro K _ ρ W tl K3 M h lid cf fs C p k tb b w q kx F F' G G' c c1 c' c1' A hc hc' hseg hr hzi
    hzj ha hvi hvj TbQ TbK hq hk vq vk
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hT := dim_T A
  have hl := Z.lnT
  have hr' : k.sc.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.ldh := hr
  have hrc : (lastCoords k.sc.r h.S.cf.ldh).size = h.S.cf.ldh := by
    unfold Attention.lastCoords
    rw [sizeCut _ (Nat.le_refl _)]
    omega
  have e1 := readHead_qry A hc TbQ (tok_size _ _ _) (by omega) hrc ha (ok_of_yields hq)
  have e2 := readGroup_key A hc' TbK (tok_size _ _ _) (by omega) hrc (ok_of_yields hk)
  have s1 : (sc3A k.sc b).value ρ W = W.slot (k.sc.sEnd + 2 * b) := Aff.value_slot ρ W _
  have s2 : (sc3B k.sc b).value ρ W = W.slot (k.sc.sEnd + (2 * b + 1)) := Aff.value_slot ρ W _
  rw [Aff.value_sub, s1, e1, sub_eq_zero] at vq
  rw [Aff.value_sub, s2, e2, sub_eq_zero] at vk
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

/-- The score of a unit below the diagonal. -/
theorem scoreFmEnd : ScoreFmEnd := by
  intro K _ ρ W tl K3 M h lid cf fs C p k tb b w q kx F F' G G' c c1 c' c1' A hc hc' hseg hr hzi
    hzj ha hvi hvj TbQ TbK hq hk vq vk
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  have hT := dim_T A
  have hl := Z.lnT
  have hr' : k.sc.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.ldh := hr
  have hrc : (lastCoords k.sc.r h.S.cf.ldh).size = h.S.cf.ldh := by
    unfold Attention.lastCoords
    rw [sizeCut _ (Nat.le_refl _)]
    omega
  have e1 := readHead_qry A hc TbQ (tok_size _ _ _) (by omega) hrc ha (ok_of_yields hq)
  have e2 := readGroup_key A hc' TbK (tok_size _ _ _) (by omega) hrc (ok_of_yields hk)
  have s1 : (sc3A k.sc b).value ρ W = W.slot (k.sc.sEnd + 2 * b) := Aff.value_slot ρ W _
  have s2 : (sc3B k.sc b).value ρ W = W.slot (k.sc.sEnd + (2 * b + 1)) := Aff.value_slot ρ W _
  rw [Aff.value_sub, s1, e1, sub_eq_zero] at vq
  rw [Aff.value_sub, s2, e2, sub_eq_zero] at vk
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

end OnBytes.Road.Rows
