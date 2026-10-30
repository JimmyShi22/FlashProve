-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/HeadSeg.lean: the key of a segment of the output head's lookup, spelled from cells
(segH, OnBytes/Tie/Pv/Lookup/Ends/H.lean), is the family's key of Johnson/Road/HeadSizes.lean,
family by family; under "HD0" the inverse of 2^(sh + 15) times it.

One record of hypotheses and one main theorem.
  TiesH P cell z np t Hm y: the reading "cell" of names has the library's cells t at the features of
    hf, hd, hr and of the stream; offsets and sizes of the layout; numbers of the shape and of the
    stream's matrix; the weight from its digits is Hm; the covered positions and the positions with
    a cost are the request y's, and so is the checked token at a covered position.
  key_segH: under TiesH, for each of the nine families s, each entry x below the family's length and
    each position i below the number of positions: segH P cell (nameOf s) x i = keyC (iw P) z np t
    Hm y s x i.

Limits: no value of TiesH is given here. Nothing on a table, a call, a form or a protocol.

-/
import Johnson.Road.HeadCallLib
import OnBytes.Tie.Pv.Lookup.Ends.H

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Ends
open Inst.Model (NormPar)
open HeadSizes (Sizes)

variable {K : Type} [Field K]

/-- A left fold that adds is a sum. -/
theorem foldl_sum (f : ℕ → K) : ∀ n : ℕ,
    (List.range n).foldl (fun s l => s + f l) 0 = ∑ l ∈ range n, f l
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_sum f n, sum_range_succ]
    rfl

/-- What ties a reading of names to the library's cells, weights and request. -/
structure TiesH (P : H.PubH) (cell : H.NameH → K) (z : Sizes) (np : NormPar)
    (t : Inst.Model.Head.Cells K) (Hm : ℕ → ℕ → K) (y : Inst.Model.Head.Req) : Prop where
  hf : ∀ φ i, H.hfC P cell φ i = t.hf φ i
  hd : ∀ φ i, H.hdC P cell φ i = t.hd φ i
  hr : ∀ φ i, H.hrC P cell φ i = t.hr φ i
  x : ∀ l k i, l < 5 → k < z.d → H.xbC P cell (P.b.cell l k) i = t.x (HeadSizes.fX z l k) i
  d : P.h.d = z.d
  JV : P.L.JV = z.V
  JVa : P.L.JVa = z.Va
  Va : z.Va ≤ z.V
  oAw : P.L.oAw = 0
  oRa : P.L.oRa = 2 * z.d
  oD1 : P.L.oD1 = 4 * z.d
  oD2 : P.L.oD2 = 4 * z.d + 2 * z.V
  oE : P.L.oE = 4 * z.d + 3 * z.V
  nl : P.b.nl = 5
  XL : P.h.XL = 5
  KF : P.h.KF = np.K
  sh : P.h.digSh = 8
  w : ∀ k v, k < z.d → v < z.V → H.wH P cell k v = Hm k v
  rho : ∀ v i, v < z.V → i < z.T → H.real P v i = ((y.rho i : ℤ) : K)
  cnt : ∀ v i, v < z.V → i < z.T →
    (H.ind (decide (v < P.h.V) && P.cov.hOnC.getD i false) : K) = ((HeadSizes.rhoC z y i : ℤ) : K)
  win : ∀ i, i < z.T → P.cov.hOn.getD i false = true → P.win.getD i 0 = y.win i
  winV : ∀ i, y.win i < z.V

namespace TiesH

variable {P : H.PubH} {cell : H.NameH → K} {z : Sizes} {np : NormPar}
  {t : Inst.Model.Head.Cells K} {Hm : ℕ → ℕ → K} {y : Inst.Model.Head.Req}

theorem limbs_eq (T : TiesH P cell z np t Hm y) (n off J x i : ℕ) :
    H.limbs P cell n off J x i = ∑ l ∈ range n, (256 : K) ^ l * t.hf (off + l * J + x) i := by
  have e := foldl_sum (fun l => (256 : K) ^ l * H.hfC P cell (off + l * J + x) i) n
  refine Eq.trans e (sum_congr rfl fun l _ => ?_)
  rw [T.hf]

theorem aw_eq (T : TiesH P cell z np t Hm y) (x i : ℕ) :
    H.aw P cell x i = HeadSizes.nw z t x i := by
  unfold H.aw HeadSizes.nw Inst.Model.Head.rd
  rw [T.limbs_eq, T.oAw, T.d]
  refine sum_congr rfl fun l _ => ?_
  have e : 0 + l * z.d + x = HeadSizes.fNw z l x := by unfold HeadSizes.fNw; ring
  rw [e]

theorem ra_eq (T : TiesH P cell z np t Hm y) (x i : ℕ) :
    32896 + H.ra P cell x i = HeadSizes.rn z t x i := by
  unfold H.ra HeadSizes.rn Inst.Model.Head.rd
  rw [T.limbs_eq, T.oRa, T.d]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  have e : 2 * z.d + l * z.d + x = HeadSizes.fRn z l x := by unfold HeadSizes.fRn; ring
  rw [e]

theorem d1_eq (T : TiesH P cell z np t Hm y) (v i : ℕ) :
    H.d1 P cell v i = HeadSizes.d1 z t v i := by
  unfold H.d1 HeadSizes.d1 Inst.Model.Head.rd
  rw [T.limbs_eq, T.oD1, T.JV]
  refine sum_congr rfl fun l _ => ?_
  have e : 4 * z.d + l * z.V + v = HeadSizes.fD1 z l v := by unfold HeadSizes.fD1; ring
  rw [e]

theorem d2_eq (T : TiesH P cell z np t Hm y) (v i : ℕ) :
    H.d2 P cell v i = HeadSizes.d2 z t v i := by
  unfold H.d2 HeadSizes.d2
  rw [T.limbs_eq, T.oD2, T.JV, sum_range_one, pow_zero, one_mul]
  have e : 4 * z.d + 2 * z.V + 0 * z.V + v = HeadSizes.fD2 z v := by unfold HeadSizes.fD2; ring
  rw [e]

theorem ex_eq (T : TiesH P cell z np t Hm y) (v i : ℕ) :
    ((Model.Head.offE : ℕ) : K) + H.ex P cell v i = HeadSizes.ex z t v i := by
  have e0 : Model.Head.offE = 8421505 := by decide
  have e1 : Model.exc = 3 := rfl
  unfold H.ex HeadSizes.ex Inst.Model.Head.rd
  have c0 : ((8421505 : ℕ) : K) = 8421505 := by norm_num
  rw [T.limbs_eq, T.oE, T.JV, e0, e1, c0]
  refine congrArg (fun a => (8421505 : K) + a) (sum_congr rfl fun l _ => ?_)
  have e : 4 * z.d + 3 * z.V + l * z.V + v = HeadSizes.fEx z l v := by
    unfold HeadSizes.fEx; ring
  rw [e]

theorem nrm_eq (T : TiesH P cell z np t Hm y) (k i : ℕ) :
    H.nrm P cell k i = HeadSizes.nrm z t k i := by
  unfold H.nrm HeadSizes.nrm Inst.Model.Head.rd HeadSizes.fNrm
  rw [T.hd, T.hd, T.d, sum_range_succ, sum_range_one]
  simp only [pow_zero, pow_one, one_mul, mul_zero, mul_one, zero_add]

theorem xs_eq (T : TiesH P cell z np t Hm y) {k : ℕ} (hk : k < z.d) (i : ℕ) :
    H.xs P cell k i = HeadSizes.xv z t k i := by
  have e := foldl_sum (fun l => (256 : K) ^ l * H.xbC P cell (P.b.cell l k) i) P.b.nl
  unfold HeadSizes.xv Inst.Model.Head.rd HeadSizes.bl
  refine Eq.trans e ?_
  rw [T.nl]
  exact sum_congr rfl fun l hl => by rw [T.x l k i (mem_range.mp hl) hk]

theorem dig_eq (T : TiesH P cell z np t Hm y) (n i : ℕ) :
    H.dig P cell n i = Inst.Model.Head.Dv t n i := by
  unfold H.dig Inst.Model.Head.Dv
  rw [T.hr, add_comm]

theorem digs_eq (T : TiesH P cell z np t Hm y) (a n i : ℕ) :
    H.digs P cell a n i = Inst.Model.Ledger.b256 (fun m => Inst.Model.Head.Dv t m i) a n := by
  have e := foldl_sum (fun j => (256 : K) ^ j * H.dig P cell (a + j) i) n
  unfold Inst.Model.Ledger.b256
  refine Eq.trans e (sum_congr rfl fun l _ => ?_)
  rw [T.dig_eq]

theorem recip_eq (T : TiesH P cell z np t Hm y) (i : ℕ) :
    H.recip P cell i = Inst.Model.Ledger.R (fun m => Inst.Model.Head.Dv t m i) := by
  have e : H.recip P cell i = H.digs P cell (if P.h.XL == 5 then 80 else 57) 6 i := rfl
  rw [e, T.XL]
  have e2 : (if (5 : ℕ) == 5 then 80 else 57) = 80 := rfl
  rw [e2, T.digs_eq]
  unfold Inst.Model.Ledger.R Inst.Model.Ledger.Rlo Inst.Model.Ledger.Rhi Inst.Model.Ledger.b256
  simp only [sum_range_succ, sum_range_zero]
  norm_num
  ring

theorem costC_eq (T : TiesH P cell z np t Hm y) (i : ℕ) :
    H.costC P cell i = Inst.Model.Head.hidC t i := by
  have e : H.costC P cell i = H.digs P cell (Model.ledNR P.h.XL) 5 i := rfl
  rw [e, T.XL, T.digs_eq]
  rfl

theorem costB_eq (T : TiesH P cell z np t Hm y) (i : ℕ) :
    H.costB P cell i = Inst.Model.Head.hidB t i := by
  have e : H.costB P cell i = H.dig P cell (Model.ledNR P.h.XL + 5) i := rfl
  rw [e, T.XL, T.dig_eq]
  unfold Inst.Model.Head.hidB Inst.Model.Ledger.b256
  rw [sum_range_one, pow_zero, one_mul]
  rfl

theorem lg_eq (T : TiesH P cell z np t Hm y) {v : ℕ} (hv : v < z.V) (i : ℕ) :
    H.lg P cell v i = HeadSizes.lg z t Hm i v := by
  have e := foldl_sum (fun k => H.nrm P cell k i * H.wH P cell k v) P.h.d
  unfold HeadSizes.lg
  refine Eq.trans e ?_
  rw [T.d]
  exact sum_congr rfl fun k hk => by rw [T.nrm_eq, T.w k v (mem_range.mp hk) hv]

theorem midK_eq (T : TiesH P cell z np t Hm y) {v i : ℕ} (hv : v < z.V) (hi : i < z.T) :
    H.midK P cell v i = HeadSizes.K1 z t y v i := by
  unfold H.midK HeadSizes.K1
  rw [T.d1_eq, T.rho v i hv hi]

theorem lowK_eq (T : TiesH P cell z np t Hm y) {v i : ℕ} (hv : v < z.V) (hi : i < z.T) :
    H.lowK P cell v i = HeadSizes.K2 z t y v i := by
  unfold H.lowK HeadSizes.K2
  rw [T.d2_eq, T.rho v i hv hi]

/-- **A segment's key, spelled from cells, is the family's key.** -/
theorem key_segH (T : TiesH P cell z np t Hm y) (s : Inst.Model.Head.Fam) (x i : ℕ)
    (hx : x < HeadSizes.len z s) (hi : i < z.T) :
    H.segH P cell (nameOf s) x i = keyC (H.iw P) z np t Hm y s x i := by
  cases s with
  | NF =>
    have hR : H.segH P cell "NF" x i =
        (2 ^ (P.h.KF - 1) - 2 ^ P.h.KF * H.aw P cell x i - 2 ^ 16 * (32896 + H.ra P cell x i)) +
          H.recip P cell i * H.xs P cell x i := rfl
    show H.segH P cell "NF" x i = HeadSizes.key z np t Hm y .NF x i
    rw [hR, T.aw_eq, T.ra_eq, T.recip_eq, T.xs_eq hx, T.KF]
    unfold HeadSizes.key
    ring
  | NFH =>
    have hR : H.segH P cell "NFH" x i =
        2 ^ (32 - P.h.KF) * (32896 + H.ra P cell x i) + 0 := rfl
    show H.segH P cell "NFH" x i = HeadSizes.key z np t Hm y .NFH x i
    rw [hR, T.ra_eq, T.KF]
    unfold HeadSizes.key
    push_cast
    ring
  | HD0 =>
    have hv : x < z.V := hx
    have hR : H.segH P cell "HD0" x i =
        H.iw P * (H.ind (decide (x < P.h.V) && P.cov.hOnC.getD i false) *
              (H.costC P cell i + 2 ^ 37 * H.costB P cell i) -
            H.real P x i * H.ind (decide (x < P.win.getD i 0)) -
            2 ^ P.h.digSh * H.midK P cell x i - H.lowK P cell x i) +
          H.iw P * (H.real P x i * (H.lg P cell (P.win.getD i 0) i - H.lg P cell x i)) := rfl
    show H.segH P cell "HD0" x i = H.iw P * HeadSizes.key z np t Hm y .HD0 x i
    have hw : (H.ind (decide (x < y.win i)) : K) = if x < y.win i then 1 else 0 := by
      unfold H.ind
      by_cases h : x < y.win i <;> simp [h]
    rw [hR, T.cnt x i hv hi, T.costC_eq, T.costB_eq, T.sh, T.midK_eq hv hi, T.lowK_eq hv hi]
    by_cases hon : P.cov.hOn.getD i false = true
    · rw [T.rho x i hv hi, T.win i hi hon, hw, T.lg_eq (T.winV i), T.lg_eq hv]
      unfold HeadSizes.key HeadSizes.mg
      ring
    · have r0 : (H.real P x i : K) = 0 := by
        unfold H.real H.ind
        simp [hon]
      have r1 : ((y.rho i : ℤ) : K) = 0 := by rw [← T.rho x i hv hi, r0]
      rw [r0]
      show _ = H.iw P * (HeadSizes.mg z t Hm y x i - 2 ^ 8 * HeadSizes.K1 z t y x i -
        HeadSizes.K2 z t y x i)
      unfold HeadSizes.mg
      rw [r1]
      ring
  | HD1 =>
    have hR : H.segH P cell "HD1" x i = H.midK P cell x i + 0 := rfl
    show H.segH P cell "HD1" x i = HeadSizes.key z np t Hm y .HD1 x i
    rw [hR, T.midK_eq (show x < z.V from hx) hi, add_zero]
    rfl
  | ROW =>
    have hR : H.segH P cell "ROW" x i =
        ((if x < Model.ledNR P.h.XL then Model.ledMu P.h.XL x else 1 : ℕ) : K) *
          H.dig P cell x i + 0 := rfl
    show H.segH P cell "ROW" x i = HeadSizes.key z np t Hm y .ROW x i
    have mK : ((if x < Model.ledNR 5 then Model.ledMu 5 x else 1 : ℕ) : K) =
        ((Inst.Model.Ledger.mu x : ℤ) : K) := by
      rw [← mu_value x, Int.cast_natCast]
    rw [hR, T.XL, mK, T.dig_eq, add_zero]
    rfl
  | HD2 =>
    have hR : H.segH P cell "HD2" x i = H.lowK P cell x i + 0 := rfl
    show H.segH P cell "HD2" x i = HeadSizes.key z np t Hm y .HD2 x i
    rw [hR, T.lowK_eq (show x < z.V from hx) hi, add_zero]
    rfl
  | HE0 =>
    have hv : x < z.V := lt_of_lt_of_le (show x < z.Va from hx) T.Va
    have hR : H.segH P cell "HE0" x i =
        (H.midK P cell (0 + x) i +
          2 ^ 16 * (((Model.Head.offE : ℕ) : K) + H.ex P cell (0 + x) i)) + 0 := rfl
    show H.segH P cell "HE0" x i = HeadSizes.key z np t Hm y .HE0 x i
    rw [hR, zero_add, T.midK_eq hv hi, T.ex_eq, add_zero]
    rfl
  | HE1 =>
    have hx' : x < z.V - z.Va := hx
    have hv : z.Va + x < z.V := by omega
    have hR : H.segH P cell "HE1" x i =
        (H.midK P cell (P.L.JVa + x) i +
          2 ^ 16 * (((Model.Head.offE : ℕ) : K) + H.ex P cell (P.L.JVa + x) i)) + 0 := rfl
    show H.segH P cell "HE1" x i = HeadSizes.key z np t Hm y .HE1 x i
    rw [hR, T.JVa, T.midK_eq hv hi, T.ex_eq, add_zero]
    rfl
  | CNF =>
    have hR : H.segH P cell "CNF" x i =
        (H.aw P cell x i + 2 ^ 28 * H.nrm P cell x i + 2 ^ 15 + 2 ^ 39) + 0 := rfl
    show H.segH P cell "CNF" x i = HeadSizes.key z np t Hm y .CNF x i
    rw [hR, T.aw_eq, T.nrm_eq]
    unfold HeadSizes.key
    ring

end TiesH

end OnBytes.Road.Hd

#print axioms OnBytes.Road.Hd.TiesH.key_segH
