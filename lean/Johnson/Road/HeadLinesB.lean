-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLinesB.lean: what the forms of the output head's lookup keys are worth on cells:
the families HD2, CNF, ROW and NF.

Johnson/Road/HeadLines.lean says in what sense a form of the verifier in OnBytes/ is a key of the
library, and has the tools. This file has four more families: the low digit of a margin (HD2), the
clamp of the final normalisation (CNF), the digits of the normalisation's ledger (ROW) and the low
key of the normalisation's rounding (NF).

Each family has three statements. The first has the sizes as letters
(Johnson/Road/HeadSizes.lean). The second and the third are its corollaries at the library's sizes,
in the library's own names: the key of Policy/Rel/LedgerHead.lean (nine families) and the key of
Cm/TargetPHead.lean (seven families).

Two families need a remark. The key of NF is not affine in the cells: it holds the product of a
value of the stream and the reciprocal. The form of the segment has the rest of the key alone, and
the statement says so: key minus product. The family ROW has 120 entries in the verifier and in
Policy/Rel/LedgerHead.lean, and 99 in Cm/TargetPHead.lean: the third statement on ROW has the 99
keys and, apart, the 21 further digits.

Main theorems: mu_value (the multipliers of the ledger's digits are the library's); line_HD2,
line_CNF, line_ROW, line_NF, line_NF_held; line_HD2_ref, line_CNF_ref, line_ROW_ref, line_NF_ref,
line_NF_held_ref; line_HD2_plain, line_CNF_plain, line_ROW_plain, line_NF_plain,
line_NF_held_plain.

What is not claimed. Nothing is said about when a world is true, about the weights' origin, or about
what a verifier's acceptance shows. Every theorem on a form begins "if the routine succeeds": none
says that it does. That the records SegFit, PosFit, Laid and ReqFits hold of a run of the verifier
is not shown here. Nothing is said about the product in the key of NF. The program does not import
this file.
-/
import Johnson.Road.HeadLines

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)
open Inst.Model (NormPar)
open HeadSizes (Sizes)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-! ## HD2 -/

/-- The family HD2, the low digit of a margin. -/
theorem line_HD2 (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R z y)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "HD2" z.V low) (U : PosFit ρ R "HD2" u)
    (h : Ok (Model.Head.LINE R "HD2") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HD2") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.V
        (fun x i => HeadSizes.key z (npOf R.h) t H y .HD2 x i) := by
  unfold Model.Head.LINE at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨ew, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewOf h1
  replace h2 : Ok (Model.Head.ztSeg R "HD2" >>= fun zt =>
      Model.Head.lowDigit R "HD2"
        (mulE (Model.Head.wxOf R ew) (Model.Head.onSum R zt))) F1 C1 a G D := h2
  rw [ok_bind] at h2
  obtain ⟨zt, F2, C2, h3, h4⟩ := h2
  obtain ⟨rfl, rfl, hzs, hzu⟩ := U.zt h3
  unfold Model.Head.lowDigit at h4
  rw [ok_bind] at h4
  obtain ⟨s, F3, C3, h5, h6⟩ := h4
  obtain ⟨rfl, rfl, wh, hwh, hs⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oD2, Z.JV]
      exact Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left Z.Sd 4) (Dvd.dvd.mul_left Z.SV 2))
        (Dvd.dvd.mul_left Z.SV l)) h5
  rw [ok_pure] at h6
  obtain ⟨rfl, rfl, rfl⟩ := h6
  obtain ⟨b1, b2, b3⟩ := S.blocked h1 hwh
  refine ⟨rfl, rfl, ew, h1, ?_⟩
  rw [Aff.value_add, Aff.value_ofConst, hs ew b3, b2, ρ.mul, ρ.mul, o1_value hρ,
    wxOf_value ρ R ew (by rw [b1, Z.V]), Z.V,
    onSum_value ρ R zt (fun i => ((y.rho i : ℤ) : K)) hzs (Y.rhoK Z), ext_point _ hzu]
  have e : (fun x i => HeadSizes.key z (npOf R.h) t H y .HD2 x i) = fun x i =>
      (∑ l ∈ range 1, (256 : K) ^ l * t.hf (R.L.oD2 + l * R.L.JV + x) i) +
        (128 : K) * ((y.rho i : ℤ) : K) := by
    funext x i
    show t.hf (4 * z.d + 2 * z.V + x) i + (128 : K) * ((y.rho i : ℤ) : K) = _
    rw [Z.oD2, Z.JV, Finset.sum_range_one, pow_zero, one_mul, Nat.zero_mul, Nat.add_zero]
  rw [e, wsum_add, wsum_pos, Blocks.ext_smul]
  ring

/-! ## CNF -/

/-- The family CNF, the key of the clamp of the final normalisation: the quotient is read by blocks
in the long table, the clamped output entry by entry in a short table at the same positions'
point. -/
theorem line_CNF (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (hS : ShortAt W R (colsOf F R.iU3) "hd@zt_FC" R.h.lt u t.hd)
    (S : SegFit ρ R "CNF" z.d low) (h : Ok (Model.Head.LINE R "CNF") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "CNF") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.d
        (fun x i => HeadSizes.key z (npOf R.h) t H y .CNF x i) := by
  unfold Model.Head.LINE at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨ew, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewOf h1
  replace h2 : Ok (Model.Head.tabAt R "hd@zt_FC" >>= fun tb =>
      (forIn [:R.h.d] ({} : Aff) (fun x r =>
        Model.Head.sh2 R tb x >>= fun c =>
          (pure PUnit.unit : SubM PUnit) >>= fun _ =>
            pure (ForInStep.yield (r.addMul c (ew.getD x zeroE)))) : SubM Aff) >>= fun b =>
        Model.Head.Sl R "CNF" R.L.oAw 2 R.h.d >>= fun s =>
          pure (s + b.scale (Model.Head.pw 28) +
            Aff.ofConst (mulE (Model.sumE ew) (Model.ofNat (2 ^ 15 + 2 ^ 39))))) F1 C1 a G D := h2
  rw [ok_bind] at h2
  obtain ⟨tb, F2, C2, h3, h4⟩ := h2
  obtain ⟨rfl, rfl, hst⟩ := ok_tabAt h3
  rw [ok_bind] at h4
  obtain ⟨b, F3, C3, h5, h6⟩ := h4
  obtain ⟨rfl, rfl, _, eb⟩ := loop_value ρ W R.h.d _
    (fun x => ρ.val (ew.getD x zeroE) * (Blocks.ext R.h.lt (fun i => t.hd x i) u +
      256 * Blocks.ext R.h.lt (fun i => t.hd (R.h.d + x) i) u))
    (fun _ => True)
    (by
      intro x s r' F4 C4 _ hr
      try dsimp only at hr
      rw [ok_bind] at hr
      obtain ⟨c, F5, C5, h7, h8⟩ := hr
      obtain ⟨rfl, rfl, v1, v2, hv⟩ := sh2_value ρ W hρ h7
      rw [ok_bind] at h8
      obtain ⟨_, F6, C6, h9, h10⟩ := h8
      rw [ok_pure] at h9 h10
      obtain ⟨_, rfl, rfl⟩ := h9
      obtain ⟨rfl, rfl, rfl⟩ := h10
      refine ⟨rfl, rfl, trivial, _, rfl, ?_⟩
      rw [Aff.value_addMul, hv, hS tb hst _ v1, hS tb hst _ v2])
    h5
  rw [ok_bind] at h6
  obtain ⟨s, F4, C4, h7, h8⟩ := h6
  obtain ⟨rfl, rfl, wh, hwh, hs⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oAw, Z.d, Nat.zero_add]
      exact Dvd.dvd.mul_left Z.Sd l) h7
  rw [ok_pure] at h8
  obtain ⟨rfl, rfl, rfl⟩ := h8
  obtain ⟨b1, b2, b3⟩ := S.blocked h1 hwh
  refine ⟨rfl, rfl, ew, h1, ?_⟩
  rw [Aff.value_add, Aff.value_add, Aff.value_scale, Aff.value_ofConst, hs ew b3, b2, eb,
    Aff.value_empty, zero_add, ρ.mul, sumE_value', b1, pw_value hρ, hρ.ofNat, Nat.cast_add,
    Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Z.d]
  have eb' : ∑ x ∈ range z.d, ρ.val (ew.getD x zeroE) *
        (Blocks.ext R.h.lt (fun i => t.hd x i) u +
          256 * Blocks.ext R.h.lt (fun i => t.hd (z.d + x) i) u) =
      wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.d
        (fun x i => t.hd x i + 256 * t.hd (z.d + x) i) := by
    unfold wsum
    refine sum_congr rfl fun x _ => ?_
    rw [Blocks.ext_add, Blocks.ext_smul]
  have e : (fun x i => HeadSizes.key z (npOf R.h) t H y .CNF x i) = fun x i =>
      (∑ l ∈ range 2, (256 : K) ^ l * t.hf (R.L.oAw + l * z.d + x) i) +
        ((2 : K) ^ 28 * (t.hd x i + 256 * t.hd (z.d + x) i) + ((2 : K) ^ 15 + 2 ^ 39)) := by
    funext x i
    show ((∑ l ∈ range 2, (256 : K) ^ l * t.hf (z.d * l + x) i) + 2 ^ 15) +
      2 ^ 28 * ((∑ l ∈ range 2, (256 : K) ^ l * t.hd (z.d * l + x) i) + 2 ^ 11) = _
    rw [Z.oAw]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_zero, Nat.mul_one,
      Nat.zero_mul, Nat.one_mul, Nat.zero_add, pow_zero, pow_one]
    ring
  have er : wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.d
        (fun x i => HeadSizes.key z (npOf R.h) t H y .CNF x i) =
      wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.d
          (fun x i => ∑ l ∈ range 2, (256 : K) ^ l * t.hf (R.L.oAw + l * z.d + x) i) +
        ((2 : K) ^ 28 * wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.d
            (fun x i => t.hd x i + 256 * t.hd (z.d + x) i) +
          (∑ x ∈ range z.d, ρ.val (ew.getD x zeroE)) * ((2 : K) ^ 15 + 2 ^ 39)) := by
    rw [e, wsum_add, wsum_add, wsum_smul, wsum_const]
  rw [eb', er]
  ring

/-! ## ROW -/

/-- The multiplier of a digit of the ledger with five limbs is the library's. Behind the 99 digits
of the normalisation both are 1. -/
theorem mu_value (idx : ℕ) :
    ((if idx < Model.ledNR 5 then Model.ledMu 5 idx else 1 : ℕ) : ℤ) =
      Inst.Model.Ledger.mu idx := by
  have e1 : Model.ledNR 5 = 99 := rfl
  have e2 : Model.ledMu 5 idx = Model.ledMu5 idx := rfl
  rw [e1, e2]
  unfold Model.ledMu5 Inst.Model.Ledger.mu
  simp only [beq_iff_eq]
  split_ifs <;> first | rfl | omega

/-- The family ROW, the digits of the ledger, each times its multiplier: 120 entries, read one by
one in a short table. The ledger has five limbs. -/
theorem line_ROW (hρ : Numerals ρ) {R : Model.Head.Run} (z : Sizes) (hX : R.h.XL = 5)
    {F G : Fork} {C D : Ctx} {a : Aff} {u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hS : ShortAt W R (colsOf F R.iU3) "hr@zt_ROW" R.h.lt u t.hr)
    (h : Ok (Model.Head.LINE R "ROW") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "ROW") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u 120
        (fun x i => HeadSizes.key z (npOf R.h) t H y .ROW x i) := by
  unfold Model.Head.LINE at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨ew, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewOf h1
  replace h2 : Ok (Model.Head.tabAt R "hr@zt_ROW" >>= fun tb =>
      (forIn [:Model.ledNRH R.h.XL] ({} : Aff) (fun idx r =>
        Model.Head.U3at R tb idx >>= fun c =>
          (pure PUnit.unit : SubM PUnit) >>= fun _ =>
            pure (ForInStep.yield (r.addMul (c + Aff.ofConst (Model.ofNat 128))
              (Model.scaleNat (ew.getD idx zeroE)
                (if idx < Model.ledNR R.h.XL then Model.ledMu R.h.XL idx else 1))))) :
        SubM Aff) >>= fun r => pure r) F1 C1 a G D := h2
  rw [ok_bind] at h2
  obtain ⟨tb, F2, C2, h3, h4⟩ := h2
  obtain ⟨rfl, rfl, hst⟩ := ok_tabAt h3
  rw [ok_bind] at h4
  obtain ⟨b, F3, C3, h5, h6⟩ := h4
  obtain ⟨rfl, rfl, _, eb⟩ := loop_value ρ W (Model.ledNRH R.h.XL) _
    (fun x => ρ.val (ew.getD x zeroE) *
      Blocks.ext R.h.lt (fun i => HeadSizes.key z (npOf R.h) t H y .ROW x i) u)
    (fun _ => True)
    (by
      intro x s r' F4 C4 _ hr
      try dsimp only at hr
      rw [ok_bind] at hr
      obtain ⟨c, F5, C5, h7, h8⟩ := hr
      obtain ⟨rfl, rfl, v1, hv⟩ := U3at_value ρ W h7
      rw [ok_bind] at h8
      obtain ⟨_, F6, C6, h9, h10⟩ := h8
      rw [ok_pure] at h9 h10
      obtain ⟨_, rfl, rfl⟩ := h9
      obtain ⟨rfl, rfl, rfl⟩ := h10
      refine ⟨rfl, rfl, trivial, _, rfl, ?_⟩
      try dsimp only
      have mK : ((if x < Model.ledNR 5 then Model.ledMu 5 x else 1 : ℕ) : K) =
          ((Inst.Model.Ledger.mu x : ℤ) : K) := by
        rw [← mu_value x, Int.cast_natCast]
      have kE : Blocks.ext R.h.lt (fun i => HeadSizes.key z (npOf R.h) t H y .ROW x i) u =
          ((Inst.Model.Ledger.mu x : ℤ) : K) *
            ((128 : K) + Blocks.ext R.h.lt (fun i => t.hr x i) u) := by
        show Blocks.ext R.h.lt
          (fun i => ((Inst.Model.Ledger.mu x : ℤ) : K) * ((128 : K) + t.hr x i)) u = _
        rw [Blocks.ext_smul, Blocks.ext_add, Blocks.ext_const]
      rw [Aff.value_addMul, Aff.value_add, Aff.value_ofConst, hv, hS tb hst _ v1, hρ.scaleNat,
        hρ.ofNat, hX, mK, kE, Nat.cast_ofNat]
      ring)
    h5
  rw [ok_pure] at h6
  obtain ⟨rfl, rfl, rfl⟩ := h6
  refine ⟨rfl, rfl, ew, h1, ?_⟩
  have n120 : Model.ledNRH R.h.XL = 120 := by
    rw [hX]
    rfl
  rw [eb, Aff.value_empty, zero_add, n120]
  rfl

/-! ## NF -/

/-- The family NF, the low key of the final normalisation's rounding. The key holds the product of
a value of the stream and the reciprocal. The form of the segment is worth the key without that
product. -/
theorem line_NF (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "NF" z.d low) (h : Ok (Model.Head.LINE R "NF") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "NF") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.d
        (fun x i => HeadSizes.key z (npOf R.h) t H y .NF x i -
          HeadSizes.xv z t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i)) := by
  unfold Model.Head.LINE at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨ew, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewOf h1
  replace h2 : Ok (Model.Head.Sl R "NF" R.L.oAw 2 R.h.d >>= fun s1 =>
      Model.Head.Sl R "NF" R.L.oRa 2 R.h.d >>= fun s2 =>
        pure (Aff.ofConst (mulE (Model.sumE ew)
            (subE (Model.Head.pw (R.h.KF - 1)) (mulE (Model.Head.pw 16) Model.Head.o2))) -
          s1.scale (Model.Head.pw R.h.KF) - s2.scale (Model.Head.pw 16))) F1 C1 a G D := h2
  rw [ok_bind] at h2
  obtain ⟨s1, F2, C2, h3, h4⟩ := h2
  obtain ⟨rfl, rfl, wh1, hwh1, hs1⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oAw, Z.d, Nat.zero_add]
      exact Dvd.dvd.mul_left Z.Sd l) h3
  rw [ok_bind] at h4
  obtain ⟨s2, F3, C3, h5, h6⟩ := h4
  obtain ⟨rfl, rfl, wh2, hwh2, hs2⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oRa, Z.d]
      exact Nat.dvd_add (Dvd.dvd.mul_left Z.Sd 2) (Dvd.dvd.mul_left Z.Sd l)) h5
  rw [ok_pure] at h6
  obtain ⟨rfl, rfl, rfl⟩ := h6
  obtain ⟨b1, b2, b3⟩ := S.blocked h1 hwh1
  obtain ⟨_, c2, c3⟩ := S.blocked h1 hwh2
  refine ⟨rfl, rfl, ew, h1, ?_⟩
  rw [Aff.value_sub, Aff.value_sub, Aff.value_ofConst, Aff.value_scale, Aff.value_scale,
    hs1 ew b3, hs2 ew c3, b2, c2, ρ.mul, ρ.sub, ρ.mul, sumE_value', b1, pw_value hρ,
    pw_value hρ, pw_value hρ, o2_value hρ]
  have e : (fun x i => HeadSizes.key z (npOf R.h) t H y .NF x i -
        HeadSizes.xv z t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i)) =
      fun x i => ((2 : K) ^ (R.h.KF - 1) - 2 ^ 16 * 32896) -
        (2 : K) ^ R.h.KF * (∑ l ∈ range 2, (256 : K) ^ l * t.hf (R.L.oAw + l * R.h.d + x) i) -
        (2 : K) ^ 16 * (∑ l ∈ range 2, (256 : K) ^ l * t.hf (R.L.oRa + l * R.h.d + x) i) := by
    funext x i
    show HeadSizes.xv z t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i) +
        2 ^ (R.h.KF - 1) - 2 ^ R.h.KF * (∑ l ∈ range 2, (256 : K) ^ l * t.hf (z.d * l + x) i) -
        2 ^ 16 * ((32896 : K) + ∑ l ∈ range 2, (256 : K) ^ l * t.hf (2 * z.d + z.d * l + x) i) -
        HeadSizes.xv z t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i) = _
    rw [Z.oAw, Z.oRa, Z.d]
    simp only [Nat.mul_comm, Nat.zero_add]
    ring
  rw [e, wsum_sub, wsum_sub, wsum_const, wsum_smul, wsum_smul]

/-- NF with the slot that the form of the call adds. If the slot holds the weighted extensions of
the products of stream and reciprocal, slot and form together are worth the weighted extensions of
the whole key. -/
theorem line_NF_held (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "NF" z.d low) (h : Ok (Model.Head.LINE R "NF") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "NF") F C ew F C ∧
      (W.slot R.x.tN.sCl = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.d (fun x i =>
          HeadSizes.xv z t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i)) →
        W.slot R.x.tN.sCl + a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.d
          (fun x i => HeadSizes.key z (npOf R.h) t H y .NF x i)) := by
  obtain ⟨e1, e2, ew, hew, hv⟩ := line_NF hρ Z H y hL S h
  refine ⟨e1, e2, ew, hew, fun hs => ?_⟩
  rw [hs, hv, wsum_sub]
  ring

/-! ## At the library's sizes, in the library's names -/

/-- The family HD2 at the library's sizes, with the key of Policy/Rel/LedgerHead.lean. -/
theorem line_HD2_ref (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "HD2" (Inst.Model.Head.len .HD2) low) (U : PosFit ρ R "HD2" u)
    (h : Ok (Model.Head.LINE R "HD2") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HD2") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .HD2)
        (fun x i => Policy.LedgerHead.key (npOf R.h) t H y .HD2 x i) := by
  obtain ⟨e1, e2, ew, hew, hv⟩ := line_HD2 hρ Z H Y hL S U h
  refine ⟨e1, e2, ew, hew, ?_⟩
  rw [hv]
  exact wsum_congr _ _ _ _ fun x _ i => HeadSizes.key_ref (npOf R.h) t H y .HD2 x i

/-- The family HD2 at the library's sizes, with the key of Cm/TargetPHead.lean. -/
theorem line_HD2_plain (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "HD2" (Cm.Plain.len .HD2) low) (U : PosFit ρ R "HD2" u)
    (h : Ok (Model.Head.LINE R "HD2") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HD2") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Cm.Plain.len .HD2)
        (fun x i => Cm.Plain.TP.key (npOf R.h) t H y .HD2 x i) := by
  obtain ⟨e1, e2, ew, hew, hv⟩ := line_HD2 hρ Z H Y hL S U h
  refine ⟨e1, e2, ew, hew, ?_⟩
  rw [hv]
  exact wsum_congr _ _ _ _ fun x _ i => HeadSizes.plainKey_ref (npOf R.h) t H y .HD2 x i

/-- The family CNF at the library's sizes, with the key of Policy/Rel/LedgerHead.lean. -/
theorem line_CNF_ref (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (hS : ShortAt W R (colsOf F R.iU3) "hd@zt_FC" R.h.lt u t.hd)
    (S : SegFit ρ R "CNF" (Inst.Model.Head.len .CNF) low)
    (h : Ok (Model.Head.LINE R "CNF") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "CNF") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .CNF)
        (fun x i => Policy.LedgerHead.key (npOf R.h) t H y .CNF x i) := by
  obtain ⟨e1, e2, ew, hew, hv⟩ := line_CNF hρ Z H y hL hS S h
  refine ⟨e1, e2, ew, hew, ?_⟩
  rw [hv]
  exact wsum_congr _ _ _ _ fun x _ i => HeadSizes.key_ref (npOf R.h) t H y .CNF x i

/-- The family CNF at the library's sizes, with the key of Cm/TargetPHead.lean. -/
theorem line_CNF_plain (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (hS : ShortAt W R (colsOf F R.iU3) "hd@zt_FC" R.h.lt u t.hd)
    (S : SegFit ρ R "CNF" (Cm.Plain.len .CNF) low)
    (h : Ok (Model.Head.LINE R "CNF") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "CNF") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Cm.Plain.len .CNF)
        (fun x i => Cm.Plain.TP.key (npOf R.h) t H y .CNF x i) := by
  obtain ⟨e1, e2, ew, hew, hv⟩ := line_CNF hρ Z H y hL hS S h
  refine ⟨e1, e2, ew, hew, ?_⟩
  rw [hv]
  exact wsum_congr _ _ _ _ fun x _ i => HeadSizes.plainKey_ref (npOf R.h) t H y .CNF x i

/-- The family NF at the library's sizes, with the key of Policy/Rel/LedgerHead.lean. -/
theorem line_NF_ref (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "NF" (Inst.Model.Head.len .NF) low)
    (h : Ok (Model.Head.LINE R "NF") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "NF") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .NF)
        (fun x i => Policy.LedgerHead.key (npOf R.h) t H y .NF x i -
          Inst.Model.Head.xv t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i)) := by
  obtain ⟨e1, e2, ew, hew, hv⟩ := line_NF hρ Z H y hL S h
  refine ⟨e1, e2, ew, hew, ?_⟩
  rw [hv]
  exact wsum_congr _ _ _ _ fun x _ i =>
    congrArg (fun k => k -
        Inst.Model.Head.xv t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i))
      (HeadSizes.key_ref (npOf R.h) t H y .NF x i)

/-- The family NF at the library's sizes, with the key of Cm/TargetPHead.lean. -/
theorem line_NF_plain (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "NF" (Cm.Plain.len .NF) low)
    (h : Ok (Model.Head.LINE R "NF") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "NF") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Cm.Plain.len .NF)
        (fun x i => Cm.Plain.TP.key (npOf R.h) t H y .NF x i -
          Inst.Model.Head.xv t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i)) := by
  obtain ⟨e1, e2, ew, hew, hv⟩ := line_NF hρ Z H y hL S h
  refine ⟨e1, e2, ew, hew, ?_⟩
  rw [hv]
  exact wsum_congr _ _ _ _ fun x _ i =>
    congrArg (fun k => k -
        Inst.Model.Head.xv t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i))
      (HeadSizes.plainKey_ref (npOf R.h) t H y .NF x i)

/-- NF with the slot, at the library's sizes, with the key of Policy/Rel/LedgerHead.lean. -/
theorem line_NF_held_ref (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "NF" (Inst.Model.Head.len .NF) low)
    (h : Ok (Model.Head.LINE R "NF") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "NF") F C ew F C ∧
      (W.slot R.x.tN.sCl =
        wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .NF)
          (fun x i => Inst.Model.Head.xv t x i *
            Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i)) →
        W.slot R.x.tN.sCl + a.value ρ W =
          wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .NF)
            (fun x i => Policy.LedgerHead.key (npOf R.h) t H y .NF x i)) :=
  line_NF_held hρ Z H y hL S h

/-- NF with the slot, at the library's sizes, with the key of Cm/TargetPHead.lean. -/
theorem line_NF_held_plain (hρ : Numerals ρ) {R : Model.Head.Run} (Z : Laid R HeadSizes.ref)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "NF" (Cm.Plain.len .NF) low)
    (h : Ok (Model.Head.LINE R "NF") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "NF") F C ew F C ∧
      (W.slot R.x.tN.sCl =
        wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Cm.Plain.len .NF)
          (fun x i => Inst.Model.Head.xv t x i *
            Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i)) →
        W.slot R.x.tN.sCl + a.value ρ W =
          wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Cm.Plain.len .NF)
            (fun x i => Cm.Plain.TP.key (npOf R.h) t H y .NF x i)) :=
  line_NF_held hρ Z H y hL S h

/-- The family ROW at the library's sizes, with the key of Policy/Rel/LedgerHead.lean. -/
theorem line_ROW_ref (hρ : Numerals ρ) {R : Model.Head.Run} (hX : R.h.XL = 5)
    {F G : Fork} {C D : Ctx} {a : Aff} {u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hS : ShortAt W R (colsOf F R.iU3) "hr@zt_ROW" R.h.lt u t.hr)
    (h : Ok (Model.Head.LINE R "ROW") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "ROW") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Inst.Model.Head.len .ROW)
        (fun x i => Policy.LedgerHead.key (npOf R.h) t H y .ROW x i) := by
  obtain ⟨e1, e2, ew, hew, hv⟩ := line_ROW hρ HeadSizes.ref hX H y hS h
  refine ⟨e1, e2, ew, hew, ?_⟩
  rw [hv]
  exact wsum_congr _ _ _ _ fun x _ i => HeadSizes.key_ref (npOf R.h) t H y .ROW x i

/-- Behind the 99 digits of the normalisation the library's multiplier is 1. -/
theorem mu_behind (k : ℕ) : Inst.Model.Ledger.mu (99 + k) = 1 := by
  unfold Inst.Model.Ledger.mu
  split_ifs <;> first | rfl | omega

/-- The family ROW at the library's sizes, with the key of Cm/TargetPHead.lean. That family has the
99 digits of the normalisation. The form has 21 more entries: their digits stand apart, each with
the multiplier 1. -/
theorem line_ROW_plain (hρ : Numerals ρ) {R : Model.Head.Run} (hX : R.h.XL = 5)
    {F G : Fork} {C D : Ctx} {a : Aff} {u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hS : ShortAt W R (colsOf F R.iU3) "hr@zt_ROW" R.h.lt u t.hr)
    (h : Ok (Model.Head.LINE R "ROW") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "ROW") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Cm.Plain.len .ROW)
          (fun x i => Cm.Plain.TP.key (npOf R.h) t H y .ROW x i) +
        wsum (fun k => ρ.val (ew.getD (99 + k) zeroE)) R.h.lt u 21
          (fun k i => Inst.Model.Head.Dv t (99 + k) i) := by
  obtain ⟨e1, e2, ew, hew, hv⟩ := line_ROW hρ HeadSizes.ref hX H y hS h
  refine ⟨e1, e2, ew, hew, ?_⟩
  have sp := wsum_split (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u 99 21
    (fun x i => HeadSizes.key HeadSizes.ref (npOf R.h) t H y .ROW x i)
  rw [hv]
  refine sp.trans ?_
  have a1 : wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u 99
        (fun x i => HeadSizes.key HeadSizes.ref (npOf R.h) t H y .ROW x i) =
      wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u (Cm.Plain.len .ROW)
        (fun x i => Cm.Plain.TP.key (npOf R.h) t H y .ROW x i) :=
    wsum_congr _ _ _ _ fun x _ i => HeadSizes.plainKey_ref (npOf R.h) t H y .ROW x i
  rw [a1]
  congr 1
  refine wsum_congr _ _ _ _ fun k _ i => ?_
  show ((Inst.Model.Ledger.mu (99 + k) : ℤ) : K) * Inst.Model.Head.Dv t (99 + k) i = _
  rw [mu_behind, Int.cast_one, one_mul]

#print axioms mu_value
#print axioms mu_behind
#print axioms line_HD2
#print axioms line_CNF
#print axioms line_ROW
#print axioms line_NF
#print axioms line_HD2_ref
#print axioms line_HD2_plain
#print axioms line_CNF_ref
#print axioms line_CNF_plain
#print axioms line_ROW_ref
#print axioms line_ROW_plain
#print axioms line_NF_ref
#print axioms line_NF_plain
#print axioms line_NF_held
#print axioms line_NF_held_ref
#print axioms line_NF_held_plain

end OnBytes.Road.Hd
