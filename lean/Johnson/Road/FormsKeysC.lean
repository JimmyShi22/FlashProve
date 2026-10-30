-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysC.lean: the forms of ten segments of a layer sub-proof's lookup against the
library's keys: CN2, CV, CG, F, OH, DH, N1H, N2H, N1, N2.

Johnson/Road/FormsKeysKit.lean says what is compared and in what sense, and has the record Fits of
all hypotheses. For each segment there are two statements here: what Env.line is at the segment's
name (by unfolding alone), and what that form is worth under Fits. For CN2, CV, CG, F, OH, DH, N1H
and N2H the key is affine in the cells, and the form is worth the weighted sum of the extensions of
the keys themselves. For N1 and N2 the key also holds a product; the form is worth the weighted sum
of the extensions of the key's affine part (FFSeg.lin).

Where the two texts are written differently. For the two norms the verifier multiplies the low key,
except the term of the high digits, by 2^(16 - k), and the high key by 2^(32 - max k 16), with the
natural numbers' subtraction, for every shift k. The library has no such factor in the low key and
multiplies the high key by 2^(32 - k). The two agree for shifts from 16 on. The four theorems on N1,
N2, N1H and N2H use the record's fields K1le and K2le, which say that the norms' shifts are at least
16 on the group's layers. The form of F depends on a switch; the theorem on F uses the record's
field gcl, which says that the switch is on.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysKit

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff tenCell TenAt)
open OnBytes.Model.Layer (Env Ten sumForms aff0 pw sumE)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key lin len)

variable {K : Type} [Field K]

/-! ## What line is at each segment -/

section Eqs

/-- What line is at the segment CN2. -/
theorem line_CN2_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "CN2" lam ew wh = (do
      let a ← v.SA wh "mw" lam "Z"
      let b ← v.shSum ew v.y.h.d "m" "zt" lam
      pure (a + b.scale (pw 28) + Aff.ofConst (mulE (sumE ew) Env.clampKey))) := by
  rfl

/-- What line is at the segment CV. -/
theorem line_CV_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "CV" lam ew wh = (do
      let a ← v.SA wh "vw" lam "Z"
      let b ← v.SA wh "v" lam "Z"
      pure (a + b.scale (pw 28) + Aff.ofConst (mulE (sumE ew) Env.clampKey))) := by
  rfl

/-- What line is at the segment CG. -/
theorem line_CG_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "CG" lam ew wh = (do
      let a ← v.SA wh "gh" lam "Z"
      let b ← v.SA wh "gc" lam "Z"
      pure (a + b.scale (pw 28) +
        Aff.ofConst (mulE (sumE ew) (Model.ofNat (49152 + 2 ^ 35 + 2 ^ 40))))) := by
  rfl

/-- What line is at the segment F. The first term depends on the switch gcl. -/
theorem line_F_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "F" lam ew wh = (do
      let key ← if v.y.h.gcl then
          pure ((← v.SA wh "g0" lam "Z") + (← v.SA wh "gc" lam "Z").scale (Model.ofNat 256))
        else v.SA wh "gi" lam "Z"
      pure (key + (← v.SA wh "s" lam "Z").scale (pw 28) +
        Aff.ofConst (mulE (sumE ew) (Model.ofNat (2 ^ 15 + 2 ^ 40))))) := by
  rfl

/-- What line is at the segment OH. -/
theorem line_OH_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "OH" lam ew wh = (do
      let a ← v.SA wh "ro" lam "Z"
      pure (Env.high (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.Lko) v.y.h.ho)) := by
  rfl

/-- What line is at the segment DH. -/
theorem line_DH_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "DH" lam ew wh = (do
      let a ← v.SA wh "rd" lam "Z"
      pure (Env.high (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.Lkd) v.y.h.hdD)) := by
  rfl

/-- What line is at the segment N1H. The digit form 2 is written out in the verifier. -/
theorem line_N1H_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "N1H" lam ew wh = (do
      let a ← v.SA wh "ra" lam "Z"
      pure (Env.high (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.LK1) 2)) := by
  rfl

/-- What line is at the segment N2H. -/
theorem line_N2H_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "N2H" lam ew wh = (do
      let a ← v.SA wh "rm" lam "Z"
      pure (Env.high (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.LK2) 2)) := by
  rfl

/-- What line is at the segment N1. -/
theorem line_N1_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "N1" lam ew wh = (do
      let a ← v.SA wh "aw" lam "Z"
      Env.site (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.LK1) 2
        fun _ => v.SA wh "ra" lam "Z") := by
  rfl

/-- What line is at the segment N2. -/
theorem line_N2_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "N2" lam ew wh = (do
      let a ← v.SA wh "mw" lam "Z"
      Env.site (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.LK2) 2
        fun _ => v.SA wh "rm" lam "Z") := by
  rfl

end Eqs

/-! ## What the forms are worth -/

section Families

variable {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim} {c : Cells K} {t : Cell → K}
  {low u : ℕ → K} (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
include F

/-- CN2: the clamp after a layer's second norm. -/
theorem Fits.line_CN2 (lam : ℕ) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff}
    (h : v.line "CN2" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .CN2) (fun x i => key D t tb L0 w .CN2 lam x i) := by
  rw [line_CN2_eq, F.d] at h
  cases h1 : v.SA wh "mw" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    cases h2 : v.shSum ew D.d "m" "zt" lam with
    | none => rw [h1, h2] at h; cases h
    | some B =>
      rw [h1, h2] at h
      cases h
      have e : ∀ x, x < D.d → ∀ i, key D t tb L0 w .CN2 lam x i =
          raw t .mw lam x i + (2 : K) ^ 28 * raw t .m lam x i + ((2 : K) ^ 15 + (2 : K) ^ 39) := by
        intro x _ i
        simp only [key, raw, Arr.off, Int.cast_zero, sub_zero]
        ring
      show _ = wsum (wt ρ ew) D.lT u D.d _
      rw [wsum_congr _ _ _ _ e, wsum_add, wsum_add, wsum_smul, wsum_const,
        Aff.value_add, Aff.value_add, Aff.value_scale, Aff.value_ofConst, ρ.mul, F.num.pw,
        hw.sumE, clampKey_value F.num, F.SA .mw rfl hw h1, F.shSum .m rfl h2]

/-- CV: the clamp of the values v. Both tensors are read by blocks. -/
theorem Fits.line_CV (lam : ℕ) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.dkv) {f : Aff}
    (h : v.line "CV" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .CV) (fun x i => key D t tb L0 w .CV lam x i) := by
  rw [line_CV_eq] at h
  cases h1 : v.SA wh "vw" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    cases h2 : v.SA wh "v" lam "Z" with
    | none => rw [h1, h2] at h; cases h
    | some B =>
      rw [h1, h2] at h
      cases h
      have e : ∀ x, x < D.dkv → ∀ i, key D t tb L0 w .CV lam x i =
          raw t .vw lam x i + (2 : K) ^ 28 * raw t .v lam x i + ((2 : K) ^ 15 + (2 : K) ^ 39) := by
        intro x _ i
        simp only [key, raw, Arr.off, Int.cast_zero, sub_zero]
        ring
      show _ = wsum (wt ρ ew) D.lT u D.dkv _
      rw [wsum_congr _ _ _ _ e, wsum_add, wsum_add, wsum_smul, wsum_const,
        Aff.value_add, Aff.value_add, Aff.value_scale, Aff.value_ofConst, ρ.mul, F.num.pw,
        hw.sumE, clampKey_value F.num, F.SA .vw rfl hw h1, F.SA .v rfl hw h2]

/-- CG: the clamp of the gate's high part. The verifier writes one constant, 49152 + 2^35 + 2^40;
the library writes the offsets 49152 and 128 beside their values, and 2^40. -/
theorem Fits.line_CG (lam : ℕ) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff}
    (h : v.line "CG" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .CG) (fun x i => key D t tb L0 w .CG lam x i) := by
  rw [line_CG_eq] at h
  cases h1 : v.SA wh "gh" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    cases h2 : v.SA wh "gc" lam "Z" with
    | none => rw [h1, h2] at h; cases h
    | some B =>
      rw [h1, h2] at h
      cases h
      have e : ∀ x, x < D.f → ∀ i, key D t tb L0 w .CG lam x i =
          raw t .gh lam x i + (2 : K) ^ 28 * raw t .gc lam x i +
            ((49152 : K) + (2 : K) ^ 35 + (2 : K) ^ 40) := by
        intro x _ i
        simp only [key, raw, Arr.off, Int.cast_zero, sub_zero]
        ring
      show _ = wsum (wt ρ ew) D.lT u D.f _
      rw [wsum_congr _ _ _ _ e, wsum_add, wsum_add, wsum_smul, wsum_const,
        Aff.value_add, Aff.value_add, Aff.value_scale, Aff.value_ofConst, ρ.mul, F.num.pw,
        F.num.ofNat, hw.sumE, F.SA .gh rfl hw h1, F.SA .gc rfl hw h2]
      push_cast
      ring

/-- F: the gate's value beside the value of the activation. The library's array sl is the verifier's
tensor s. The verifier writes one constant, 2^15 + 2^40; the library writes the offsets 2^15 and
2^12 beside their values. -/
theorem Fits.line_F (lam : ℕ) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff}
    (h : v.line "F" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .F) (fun x i => key D t tb L0 w .F lam x i) := by
  rw [line_F_eq, F.gcl] at h
  cases h1 : v.SA wh "g0" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    cases h2 : v.SA wh "gc" lam "Z" with
    | none => rw [h1, h2] at h; cases h
    | some B =>
      cases h3 : v.SA wh "s" lam "Z" with
      | none => rw [h1, h2, h3] at h; cases h
      | some S =>
        rw [h1, h2, h3] at h
        cases h
        have e : ∀ x, x < D.f → ∀ i, key D t tb L0 w .F lam x i =
            raw t .g0 lam x i + (256 : K) * raw t .gc lam x i + (2 : K) ^ 28 * raw t .sl lam x i +
              ((2 : K) ^ 15 + (2 : K) ^ 40) := by
          intro x _ i
          simp only [key, raw, Arr.off, Int.cast_zero, sub_zero]
          ring
        show (A + B.scale (Model.ofNat 256) + S.scale (pw 28) +
          Aff.ofConst (mulE (sumE ew) (Model.ofNat (2 ^ 15 + 2 ^ 40)))).value ρ W =
            wsum (wt ρ ew) D.lT u D.f _
        rw [wsum_congr _ _ _ _ e, wsum_add, wsum_add, wsum_add, wsum_smul, wsum_smul, wsum_const,
          Aff.value_add, Aff.value_add, Aff.value_add, Aff.value_scale, Aff.value_scale,
          Aff.value_ofConst, ρ.mul, F.num.pw, F.num.ofNat, F.num.ofNat, hw.sumE,
          F.SA .g0 rfl hw h1, F.SA .gc rfl hw h2, F.SA .sl rfl hw h3]
        push_cast
        ring

/-- OH: the high digit of the rounding that adds the attention output to the stream. -/
theorem Fits.line_OH (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff}
    (h : v.line "OH" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .OH) (fun x i => key D t tb L0 w .OH lam x i) := by
  rw [line_OH_eq, F.ho, F.ko lam hlam] at h
  cases h1 : v.SA wh "ro" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    rw [h1] at h
    cases h
    have e : ∀ x, x < D.d → ∀ i, key D t tb L0 w .OH lam x i =
        (2 : K) ^ (24 - max (D.Pl lam).ko 16) * (raw t .ro lam x i + 128) := by
      intro x _ i
      simp only [key, Inst.Model.Site.shigh_eq, Inst.Model.Site.up, raw, Arr.off]
      push_cast
      ring
    show _ = wsum (wt ρ ew) D.lT u D.d _
    rw [wsum_congr _ _ _ _ e, wsum_smul, wsum_add, wsum_const, high_value F.num, oOf_one F.num,
      hw.sumE, F.SA .ro rfl hw h1]
    show (2 : K) ^ (24 - max (D.Pl lam).ko 16) * _ = _
    ring

/-- DH: the high digit of the rounding that adds the feed-forward output to the stream. -/
theorem Fits.line_DH (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff}
    (h : v.line "DH" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .DH) (fun x i => key D t tb L0 w .DH lam x i) := by
  rw [line_DH_eq, F.hdD, F.kd lam hlam] at h
  cases h1 : v.SA wh "rd" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    rw [h1] at h
    cases h
    have e : ∀ x, x < D.d → ∀ i, key D t tb L0 w .DH lam x i =
        (2 : K) ^ (24 - max (D.Pl lam).kd 16) * (raw t .rd lam x i + 128) := by
      intro x _ i
      simp only [key, Inst.Model.Site.shigh_eq, Inst.Model.Site.up, raw, Arr.off]
      push_cast
      ring
    show _ = wsum (wt ρ ew) D.lT u D.d _
    rw [wsum_congr _ _ _ _ e, wsum_smul, wsum_add, wsum_const, high_value F.num, oOf_one F.num,
      hw.sumE, F.SA .rd rfl hw h1]
    show (2 : K) ^ (24 - max (D.Pl lam).kd 16) * _ = _
    ring

/-- N1H: the high digits of the rounding in a layer's first norm. The verifier's exponent is
32 - max k 16 and the library's is 32 - k; they are equal because the shift is at least 16. -/
theorem Fits.line_N1H (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff} (h : v.line "N1H" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .N1H) (fun x i => key D t tb L0 w .N1H lam x i) := by
  rw [line_N1H_eq, F.K1 lam hlam] at h
  cases h1 : v.SA wh "ra" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    rw [h1] at h
    cases h
    have e : ∀ x, x < D.d → ∀ i, key D t tb L0 w .N1H lam x i =
        (2 : K) ^ (32 - (D.Pl lam).n1.K) * (raw t .ra lam x i + 32896) := by
      intro x _ i
      simp only [key, Inst.Model.Site.high, raw, Arr.off]
      push_cast
      ring
    show _ = wsum (wt ρ ew) D.lT u D.d _
    rw [wsum_congr _ _ _ _ e, wsum_smul, wsum_add, wsum_const, high_value F.num, oOf_two F.num,
      hw.sumE, F.SA .ra rfl hw h1, max_eq_left (F.K1le lam hlam)]
    show (2 : K) ^ (32 - (D.Pl lam).n1.K) * _ = _
    ring

/-- N2H: the high digits of the rounding in a layer's second norm. The exponents are equal for the
same reason as at N1H. -/
theorem Fits.line_N2H (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff} (h : v.line "N2H" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .N2H) (fun x i => key D t tb L0 w .N2H lam x i) := by
  rw [line_N2H_eq, F.K2 lam hlam] at h
  cases h1 : v.SA wh "rm" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    rw [h1] at h
    cases h
    have e : ∀ x, x < D.d → ∀ i, key D t tb L0 w .N2H lam x i =
        (2 : K) ^ (32 - (D.Pl lam).n2.K) * (raw t .rm lam x i + 32896) := by
      intro x _ i
      simp only [key, Inst.Model.Site.high, raw, Arr.off]
      push_cast
      ring
    show _ = wsum (wt ρ ew) D.lT u D.d _
    rw [wsum_congr _ _ _ _ e, wsum_smul, wsum_add, wsum_const, high_value F.num, oOf_two F.num,
      hw.sumE, F.SA .rm rfl hw h1, max_eq_left (F.K2le lam hlam)]
    show (2 : K) ^ (32 - (D.Pl lam).n2.K) * _ = _
    ring

/-- N1: the rounding in a layer's first norm; the affine part of the key. The verifier's factor
2^(16 - k), which the library does not write, is 1 because the shift is at least 16. -/
theorem Fits.line_N1 (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff} (h : v.line "N1" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .N1) (fun x i => lin D t tb L0 w .N1 lam x i) := by
  rw [line_N1_eq, F.K1 lam hlam] at h
  cases h1 : v.SA wh "aw" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    rw [h1] at h
    have h' : Env.site (sumE ew) A (D.Pl lam).n1.K 2 (fun _ => v.SA wh "ra" lam "Z") = some f := h
    obtain ⟨S, h2, h3⟩ := site_value (W := W) F.num rfl h'
    have hK : 16 - (D.Pl lam).n1.K = 0 := by
      have := F.K1le lam hlam
      omega
    have e : ∀ x, x < D.d → ∀ i, lin D t tb L0 w .N1 lam x i =
        ((2 : K) ^ ((D.Pl lam).n1.K - 1) - (2 : K) ^ (D.Pl lam).n1.K * raw t .aw lam x i) -
        (2 : K) ^ 16 * (raw t .ra lam x i + 32896) := by
      intro x _ i
      simp only [lin, Inst.Model.Site.site, raw, Arr.off]
      push_cast
      ring
    show _ = wsum (wt ρ ew) D.lT u D.d _
    rw [wsum_congr _ _ _ _ e, wsum_sub, wsum_sub, wsum_const, wsum_smul, wsum_smul,
      wsum_add, wsum_const, h3, oOf_two F.num, hw.sumE, F.SA .aw rfl hw h1,
      F.SA .ra rfl hw h2, hK, pow_zero, one_mul]
    ring

/-- N2: the rounding in a layer's second norm; the affine part of the key. The verifier's factor
2^(16 - k) is 1 for the same reason as at N1. -/
theorem Fits.line_N2 (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff} (h : v.line "N2" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .N2) (fun x i => lin D t tb L0 w .N2 lam x i) := by
  rw [line_N2_eq, F.K2 lam hlam] at h
  cases h1 : v.SA wh "mw" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    rw [h1] at h
    have h' : Env.site (sumE ew) A (D.Pl lam).n2.K 2 (fun _ => v.SA wh "rm" lam "Z") = some f := h
    obtain ⟨S, h2, h3⟩ := site_value (W := W) F.num rfl h'
    have hK : 16 - (D.Pl lam).n2.K = 0 := by
      have := F.K2le lam hlam
      omega
    have e : ∀ x, x < D.d → ∀ i, lin D t tb L0 w .N2 lam x i =
        ((2 : K) ^ ((D.Pl lam).n2.K - 1) - (2 : K) ^ (D.Pl lam).n2.K * raw t .mw lam x i) -
        (2 : K) ^ 16 * (raw t .rm lam x i + 32896) := by
      intro x _ i
      simp only [lin, Inst.Model.Site.site, raw, Arr.off]
      push_cast
      ring
    show _ = wsum (wt ρ ew) D.lT u D.d _
    rw [wsum_congr _ _ _ _ e, wsum_sub, wsum_sub, wsum_const, wsum_smul, wsum_smul,
      wsum_add, wsum_const, h3, oOf_two F.num, hw.sumE, F.SA .mw rfl hw h1,
      F.SA .rm rfl hw h2, hK, pow_zero, one_mul]
    ring

end Families

#print axioms Fits.line_CN2
#print axioms Fits.line_CV
#print axioms Fits.line_CG
#print axioms Fits.line_F
#print axioms Fits.line_OH
#print axioms Fits.line_DH
#print axioms Fits.line_N1H
#print axioms Fits.line_N2H
#print axioms Fits.line_N1
#print axioms Fits.line_N2

end OnBytes.Road
