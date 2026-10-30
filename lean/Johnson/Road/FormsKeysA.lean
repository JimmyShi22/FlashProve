-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysA.lean: the forms of nine segments of a layer sub-proof's lookup against the
library's keys: SEL, CN1, VH, V, CQK, O, QKH, ROW, DD.

Johnson/Road/FormsKeysKit.lean says what is compared and in what sense, and has the record Fits of
all hypotheses. For each segment there are two statements here: what Env.line is at the segment's
name (by unfolding alone), and what that form is worth under Fits. For SEL, CN1, VH, CQK, QKH and
ROW the key is affine in the cells, and the form is worth the weighted sum of the extensions of the
keys themselves. For V, O and DD the key also holds a product; the form is worth the weighted sum of
the extensions of the key's affine part (FFSeg.lin).

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

/-- What line is at the segment SEL. -/
theorem line_SEL_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "SEL" lam ew wh = sumForms v.y.h.NE (fun x => do
      pure (← v.shA "sel" "zt" (lam / 2) x, Model.scaleNat (ew.getD x zeroE) 128)) := by
  rfl

/-- What line is at the segment CN1. -/
theorem line_CN1_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "CN1" lam ew wh = (do
      let a ← v.SA wh "aw" lam "Z"
      let b ← v.shSum ew v.y.h.d "a" "zt" lam
      pure (a + b.scale (pw 28) + Aff.ofConst (mulE (sumE ew) Env.clampKey))) := by
  rfl

/-- What line is at the segment VH. -/
theorem line_VH_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "VH" lam ew wh = (do
      let a ← v.SA wh "rv" lam "Z"
      pure (Env.high (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.Lkv) v.y.h.hv)) := by
  rfl

/-- What line is at the segment V. -/
theorem line_V_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "V" lam ew wh = (do
      let a ← v.SA wh "vw" lam "Z"
      Env.site (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.Lkv) v.y.h.hv
        fun _ => v.SA wh "rv" lam "Z") := by
  rfl

/-- What line is at the segment CQK. -/
theorem line_CQK_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "CQK" lam ew wh = (do
      let a ← v.SA wh "qkw" lam "Z"
      let q ← v.SBA wh 0 v.y.dq "q" lam "Z" 0
      let k ← v.SBA wh v.y.dq v.y.nqk "kx" lam "Z" v.y.dq
      pure (a + (q + k).scale (pw 28) + Aff.ofConst (mulE (sumE ew) Env.clampKey))) := by
  rfl

/-- What line is at the segment O. -/
theorem line_O_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "O" lam ew wh = (do
      let a ← v.SxsA wh "Z" (2 * lam + 1)
      let b ← v.SxsA wh "Z" (2 * lam)
      Env.site (sumE ew) (a - b) (v.sc.kl (v.lay lam) Model.Layer.Lko) v.y.h.ho
        fun _ => v.SA wh "ro" lam "Z") := by
  rfl

/-- What line is at the segment QKH. -/
theorem line_QKH_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "QKH" lam ew wh = (do
      let p ← (do
        let a ← v.SBA wh 0 v.y.dq "rqk" lam "Z" 0
        pure (Env.high (Model.Layer.sumR ew 0 v.y.dq) a (v.sc.kl (v.lay lam) Model.Layer.Lkq)
          v.y.h.hq))
      let q ← (do
        let b ← v.SBA wh v.y.dq v.y.nqk "rqk" lam "Z" 0
        pure (Env.high (Model.Layer.sumR ew v.y.dq v.y.nqk) b (v.sc.kl (v.lay lam) Model.Layer.Lkk)
          v.y.h.hq))
      pure (p + q)) := by
  rfl

/-- What line is at the segment ROW. -/
theorem line_ROW_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "ROW" lam ew wh = (do
      let b ← v.tabAt "ar@zt"
      let trow ← v.y.T_ "row"
      sumForms ew.size fun x =>
        (v.U3at b (trow.OFF + (v.y.NN * lam + x / Model.ledNR v.y.h.xl) * Model.ledNR v.y.h.xl +
          x % Model.ledNR v.y.h.xl)).map fun a =>
          (a + Aff.ofConst (Model.ofNat 128),
            Model.scaleNat (ew.getD x zeroE)
              (Model.ledMu v.y.h.xl (x % Model.ledNR v.y.h.xl)))) := by
  rfl

/-- One step of the fold that builds the form of the segment DD. -/
def stepDD (v : Env) (lamM : ℕ) (ew : Array E) (s : Aff × Aff) (x : ℕ) : Option (Aff × Aff) := do
  let a := s.1.addMul ((← v.shA "lr" "zt" lamM x) + s.2) (negE (ew.getD x zeroE))
  pure (a, s.2 + (← v.shA "sel" "zt" lamM x))

/-- What line is at the segment DD. -/
theorem line_DD_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "DD" lam ew wh = (do
      let r ← (List.range v.y.h.NE).reverse.foldlM (stepDD v (lam / 2) ew) (aff0, aff0)
      pure r.1) := by
  rfl

end Eqs

/-! ## Two tools of single families -/

/-- The verifier's multiplier of a digit of a row with five limbs is the library's. -/
theorem ledMu_five (n : ℕ) : ((Model.ledMu 5 n : ℕ) : ℤ) = Inst.Model.Ledger.mu n := by
  show ((Model.ledMu5 n : ℕ) : ℤ) = _
  unfold Model.ledMu5 Inst.Model.Ledger.mu
  simp only [beq_iff_eq]
  split_ifs <;> rfl

section Fold

variable {ρ : Reading K} {W : World K}

/-- The fold that builds the form of the segment DD, run over the experts n - 1 down to 0 from any
state s. LR x and SEL x are what the entries of the tensors lr and sel are worth. -/
theorem foldDD_value (hρ : Numerals ρ) {v : Env} {lamM : ℕ} {ew : Array E} (LR SEL : ℕ → K)
    (hLR : ∀ x a, v.shA "lr" "zt" lamM x = some a → a.value ρ W = LR x)
    (hSEL : ∀ x a, v.shA "sel" "zt" lamM x = some a → a.value ρ W = SEL x) :
    ∀ (n : ℕ) (s r : Aff × Aff), (List.range n).reverse.foldlM (stepDD v lamM ew) s = some r →
      r.1.value ρ W = s.1.value ρ W + ∑ x ∈ range n, -ρ.val (ew.getD x zeroE) *
        (LR x + s.2.value ρ W + ∑ e ∈ range n, if x < e then SEL e else 0)
  | 0, s, r, h => by
    have hs : s = r := by simpa using h
    subst hs
    simp
  | n + 1, s, r, h => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldlM_cons] at h
    cases h1 : v.shA "lr" "zt" lamM n with
    | none => simp [stepDD, h1] at h
    | some a =>
      cases h2 : v.shA "sel" "zt" lamM n with
      | none => simp [stepDD, h1, h2] at h
      | some b =>
        have hs : stepDD v lamM ew s n =
            some (s.1.addMul (a + s.2) (negE (ew.getD n zeroE)), s.2 + b) := by
          unfold stepDD
          rw [h1, h2]
          rfl
        rw [hs] at h
        have h' : (List.range n).reverse.foldlM (stepDD v lamM ew)
            (s.1.addMul (a + s.2) (negE (ew.getD n zeroE)), s.2 + b) = some r := h
        rw [foldDD_value hρ LR SEL hLR hSEL n _ r h', Aff.value_addMul, Aff.value_add,
          Aff.value_add, hρ.neg, hLR n a h1, hSEL n b h2, Finset.sum_range_succ]
        have e1 : ∀ x ∈ range n, -ρ.val (ew.getD x zeroE) *
            (LR x + s.2.value ρ W + ∑ e ∈ range (n + 1), if x < e then SEL e else 0) =
            -ρ.val (ew.getD x zeroE) *
              (LR x + (s.2.value ρ W + SEL n) + ∑ e ∈ range n, if x < e then SEL e else 0) := by
          intro x hx
          rw [Finset.sum_range_succ, if_pos (mem_range.mp hx)]
          ring
        have e2 : (∑ e ∈ range (n + 1), if n < e then SEL e else 0) = 0 :=
          sum_eq_zero fun e he => if_neg (by have := mem_range.mp he; omega)
        rw [sum_congr rfl e1, e2]
        ring

end Fold

/-! ## What the forms are worth -/

section Families

variable {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim} {c : Cells K} {t : Cell → K}
  {low u : ℕ → K} (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
include F

/-- SEL: the selector's entries under the factor 128. -/
theorem Fits.line_SEL (lam : ℕ) {ew wh : Array E} {f : Aff} (h : v.line "SEL" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .SEL) (fun x i => key D t tb L0 w .SEL lam x i) := by
  rw [line_SEL_eq, F.NE] at h
  refine sumForms_value ρ W _ _ _ ?_ h
  intro x a k hb
  obtain ⟨h1, h2⟩ := bind_pair_some hb
  subst h2
  have hk : (fun i => key D t tb L0 w .SEL lam x i) =
      fun i => (128 : K) * raw t .sel (lam / 2) x i := by
    funext i
    simp [key, raw, Arr.off]
  show _ = ρ.val (ew.getD x zeroE) * Blocks.ext D.lT (fun i => key D t tb L0 w .SEL lam x i) u
  rw [F.num.scaleNat, F.shA .sel rfl h1, hk, Blocks.ext_smul]
  push_cast
  ring

/-- CN1: the clamp after a layer's first norm. -/
theorem Fits.line_CN1 (lam : ℕ) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff}
    (h : v.line "CN1" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .CN1) (fun x i => key D t tb L0 w .CN1 lam x i) := by
  rw [line_CN1_eq, F.d] at h
  cases h1 : v.SA wh "aw" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    cases h2 : v.shSum ew D.d "a" "zt" lam with
    | none => rw [h1, h2] at h; cases h
    | some B =>
      rw [h1, h2] at h
      cases h
      have e : ∀ x, x < D.d → ∀ i, key D t tb L0 w .CN1 lam x i =
          raw t .aw lam x i + (2 : K) ^ 28 * raw t .a lam x i + ((2 : K) ^ 15 + (2 : K) ^ 39) := by
        intro x _ i
        simp only [key, raw, Arr.off, Int.cast_zero, sub_zero]
        ring
      show _ = wsum (wt ρ ew) D.lT u D.d _
      rw [wsum_congr _ _ _ _ e, wsum_add, wsum_add, wsum_smul, wsum_const,
        Aff.value_add, Aff.value_add, Aff.value_scale, Aff.value_ofConst, ρ.mul, F.num.pw,
        hw.sumE, clampKey_value F.num, F.SA .aw rfl hw h1, F.shSum .a rfl h2]

/-- VH: the high digit of the rounding that gives the values v. -/
theorem Fits.line_VH (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.dkv) {f : Aff}
    (h : v.line "VH" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .VH) (fun x i => key D t tb L0 w .VH lam x i) := by
  rw [line_VH_eq, F.hv, F.kv lam hlam] at h
  cases h1 : v.SA wh "rv" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    rw [h1] at h
    cases h
    have e : ∀ x, x < D.dkv → ∀ i, key D t tb L0 w .VH lam x i =
        (2 : K) ^ (24 - max (D.Pl lam).kv 16) * (raw t .rv lam x i + 128) := by
      intro x _ i
      simp only [key, Inst.Model.Site.shigh_eq, Inst.Model.Site.up, raw, Arr.off]
      push_cast
      ring
    show _ = wsum (wt ρ ew) D.lT u D.dkv _
    rw [wsum_congr _ _ _ _ e, wsum_smul, wsum_add, wsum_const, high_value F.num, oOf_one F.num,
      hw.sumE, F.SA .rv rfl hw h1]
    show (2 : K) ^ (24 - max (D.Pl lam).kv 16) * _ = _
    ring

/-- V: the rounding that gives the values v; the affine part of the key. -/
theorem Fits.line_V (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.dkv) {f : Aff}
    (h : v.line "V" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .V) (fun x i => lin D t tb L0 w .V lam x i) := by
  rw [line_V_eq, F.hv, F.kv lam hlam] at h
  cases h1 : v.SA wh "vw" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    rw [h1] at h
    have h' : Env.site (sumE ew) A (D.Pl lam).kv 1 (fun _ => v.SA wh "rv" lam "Z") = some f := h
    obtain ⟨S, h2, h3⟩ := site_value (W := W) F.num rfl h'
    have e : ∀ x, x < D.dkv → ∀ i, lin D t tb L0 w .V lam x i =
        (2 : K) ^ (16 - (D.Pl lam).kv) *
          ((2 : K) ^ ((D.Pl lam).kv - 1) - (2 : K) ^ (D.Pl lam).kv * raw t .vw lam x i) -
        (2 : K) ^ 16 * (raw t .rv lam x i + 128) := by
      intro x _ i
      simp only [lin, Inst.Model.Site.ssite_eq, Inst.Model.Site.dn, raw, Arr.off]
      push_cast
      ring
    show _ = wsum (wt ρ ew) D.lT u D.dkv _
    rw [wsum_congr _ _ _ _ e, wsum_sub, wsum_smul, wsum_sub, wsum_const, wsum_smul, wsum_smul,
      wsum_add, wsum_const, h3, oOf_one F.num, hw.sumE, F.SA .vw rfl hw h1,
      F.SA .rv rfl hw h2]
    ring

/-- CQK: the clamp of queries and keys: one segment whose first dq entries are clamped to the
tensor q and whose others to the tensor kx. -/
theorem Fits.line_CQK (lam : ℕ) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.dqk) {f : Aff}
    (h : v.line "CQK" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .CQK) (fun x i => key D t tb L0 w .CQK lam x i) := by
  have hsum : D.dqk = D.dq + D.dkv := rfl
  have z0 : ∃ q, 0 = q * 2 ^ v.y.ls := ⟨0, (Nat.zero_mul _).symm⟩
  rw [line_CQK_eq, F.dq, F.nqk] at h
  cases h1 : v.SA wh "qkw" lam "Z" with
  | none => rw [h1] at h; cases h
  | some A =>
    cases h2 : v.SBA wh 0 D.dq "q" lam "Z" 0 with
    | none => rw [h1, h2] at h; cases h
    | some Q =>
      cases h3 : v.SBA wh D.dq D.dqk "kx" lam "Z" D.dq with
      | none => rw [h1, h2, h3] at h; cases h
      | some Kx =>
        rw [h1, h2, h3] at h
        cases h
        have e : ∀ x, x < D.dqk → ∀ i, key D t tb L0 w .CQK lam x i =
            raw t .qkw lam x i + (2 : K) ^ 28 *
              (if x < D.dq then raw t .q lam x i else raw t .kx lam (x - D.dq) i) +
              ((2 : K) ^ 15 + (2 : K) ^ 39) := by
          intro x _ i
          simp only [key, raw, Arr.off, Int.cast_zero, sub_zero]
          ring
        have e1 : ∀ x, x < D.dq → ∀ i,
            (if x < D.dq then raw t .q lam x i else raw t .kx lam (x - D.dq) i) =
              raw t .q lam x i := fun x hx i => if_pos hx
        have e2 : ∀ y, y < D.dkv → ∀ i,
            (if D.dq + y < D.dq then raw t .q lam (D.dq + y) i
              else raw t .kx lam (D.dq + y - D.dq) i) = raw t .kx lam y i := by
          intro y _ i
          rw [if_neg (by omega), Nat.add_sub_cancel_left]
        have h2' : v.SBA wh 0 (0 + D.dq) "q" lam "Z" 0 = some Q := by rw [Nat.zero_add]; exact h2
        have vq := F.SBA .q rfl hw z0 F.bdq z0 (Nat.le_refl 0) h2'
        have vk := F.SBA .kx rfl hw F.bdq F.bdkv F.bdq (Nat.le_refl _) h3
        simp only [Nat.sub_self, Nat.zero_add] at vq vk
        show _ = wsum (wt ρ ew) D.lT u D.dqk _
        rw [wsum_congr _ _ _ _ e, wsum_add, wsum_add, wsum_smul, wsum_const,
          Aff.value_add, Aff.value_add, Aff.value_scale, Aff.value_add, Aff.value_ofConst, ρ.mul,
          F.num.pw, hw.sumE, clampKey_value F.num, F.SA .qkw rfl hw h1, vq, vk]
        congr 2
        rw [hsum, wsum_split, wsum_congr _ _ _ _ e1, wsum_congr _ _ _ _ e2]

/-- O: the rounding that adds the attention output to the stream; the affine part of the key. -/
theorem Fits.line_O (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff}
    (h : v.line "O" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .O) (fun x i => lin D t tb L0 w .O lam x i) := by
  rw [line_O_eq, F.ho, F.ko lam hlam] at h
  cases h1 : v.SxsA wh "Z" (2 * lam + 1) with
  | none => rw [h1] at h; cases h
  | some A =>
    cases h2 : v.SxsA wh "Z" (2 * lam) with
    | none => rw [h1, h2] at h; cases h
    | some B =>
      rw [h1, h2] at h
      have h' : Env.site (sumE ew) (A - B) (D.Pl lam).ko 1 (fun _ => v.SA wh "ro" lam "Z") =
          some f := h
      obtain ⟨S, h3, h4⟩ := site_value (W := W) F.num rfl h'
      have e : ∀ x, x < D.d → ∀ i, lin D t tb L0 w .O lam x i =
          (2 : K) ^ (16 - (D.Pl lam).ko) * ((2 : K) ^ ((D.Pl lam).ko - 1) -
            (2 : K) ^ (D.Pl lam).ko * (Inst.Model.FFSeg.xS D t (2 * lam + 1) x i -
              Inst.Model.FFSeg.xS D t (2 * lam) x i)) -
          (2 : K) ^ 16 * (raw t .ro lam x i + 128) := by
        intro x _ i
        simp only [lin, Inst.Model.Site.ssite_eq, Inst.Model.Site.dn, raw, Arr.off]
        push_cast
        ring
      show _ = wsum (wt ρ ew) D.lT u D.d _
      rw [wsum_congr _ _ _ _ e, wsum_sub, wsum_smul, wsum_sub, wsum_const, wsum_smul, wsum_sub,
        wsum_smul, wsum_add, wsum_const, h4, oOf_one F.num, hw.sumE, Aff.value_sub,
        F.Sxs hw h1, F.Sxs hw h2, F.SA .ro rfl hw h3]
      ring

/-- QKH: the high digits of the roundings that give queries and keys: one segment in two stretches,
each with its own shift. -/
theorem Fits.line_QKH (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.dqk) {f : Aff}
    (h : v.line "QKH" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .QKH) (fun x i => key D t tb L0 w .QKH lam x i) := by
  have hsum : D.dqk = D.dq + D.dkv := rfl
  have z0 : ∃ q, 0 = q * 2 ^ v.y.ls := ⟨0, (Nat.zero_mul _).symm⟩
  rw [line_QKH_eq, F.dq, F.nqk, F.hq, F.kq lam hlam, F.kk lam hlam] at h
  cases h1 : v.SBA wh 0 D.dq "rqk" lam "Z" 0 with
  | none => rw [h1] at h; cases h
  | some A =>
    cases h2 : v.SBA wh D.dq D.dqk "rqk" lam "Z" 0 with
    | none => rw [h1, h2] at h; cases h
    | some B =>
      rw [h1, h2] at h
      cases h
      have e1 : ∀ x, x < D.dq → ∀ i, key D t tb L0 w .QKH lam x i =
          (2 : K) ^ (32 - max (D.Pl lam).kq 16) * (raw t .rqk lam x i + 32896) := by
        intro x hx i
        simp only [key, Inst.Model.FFSeg.kQK, if_pos hx, Inst.Model.Site.shigh_eq,
          Inst.Model.Site.up, raw, Arr.off]
        push_cast
        ring
      have e2 : ∀ y, y < D.dkv → ∀ i, key D t tb L0 w .QKH lam (D.dq + y) i =
          (2 : K) ^ (32 - max (D.Pl lam).kk 16) * (raw t .rqk lam (D.dq + y) i + 32896) := by
        intro y _ i
        have hn : ¬ D.dq + y < D.dq := by omega
        simp only [key, Inst.Model.FFSeg.kQK, if_neg hn, Inst.Model.Site.shigh_eq,
          Inst.Model.Site.up, raw, Arr.off]
        push_cast
        ring
      have h1' : v.SBA wh 0 (0 + D.dq) "rqk" lam "Z" 0 = some A := by rw [Nat.zero_add]; exact h1
      have va := F.SBA .rqk rfl hw z0 F.bdq z0 (Nat.le_refl 0) h1'
      have vb := F.SBA .rqk rfl hw F.bdq F.bdkv z0 (Nat.zero_le _) h2
      have hs := hw.size
      simp only [Nat.sub_zero, Nat.zero_add] at va vb
      show _ = wsum (wt ρ ew) D.lT u D.dqk _
      rw [hsum, wsum_split, wsum_congr _ _ _ _ e1, wsum_congr _ _ _ _ e2, wsum_smul, wsum_add,
        wsum_const, wsum_smul, wsum_add, wsum_const, Aff.value_add, high_value F.num,
        high_value F.num, oOf_two F.num, sumR_value ρ ew 0 D.dq (by omega),
        sumR_value ρ ew D.dq (D.dq + D.dkv) (by omega), va, vb]
      simp only [Nat.sub_zero, Nat.zero_add, Nat.add_sub_cancel_left]
      show (2 : K) ^ (32 - max (D.Pl lam).kq 16) * _ + (2 : K) ^ (32 - max (D.Pl lam).kk 16) * _ = _
      ring

/-- ROW: the digits of the two norms' rows of a layer, each under its multiplier. -/
theorem Fits.line_ROW (lam : ℕ) {ew wh : Array E} (hsz : ew.size = len D .ROW) {f : Aff}
    (h : v.line "ROW" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .ROW) (fun x i => key D t tb L0 w .ROW lam x i) := by
  obtain ⟨trow, b, hb, hrow, _, T, hJ, R⟩ := F.rowTab
  rw [line_ROW_eq, hb, hrow, F.xl, F.NN, hsz] at h
  have h' : sumForms (2 * 99) (fun x =>
      (v.U3at b (trow.OFF + (2 * lam + x / 99) * 99 + x % 99)).map fun a =>
        (a + Aff.ofConst (Model.ofNat 128),
          Model.scaleNat (ew.getD x zeroE) (Model.ledMu 5 (x % 99)))) = some f := h
  refine sumForms_value ρ W _ _ _ ?_ h'
  intro x a k hx
  obtain ⟨a', h1, h2⟩ := map_some hx
  cases h2
  have hc : trow.OFF + (2 * lam + x / 99) * 99 + x % 99 =
      tenCell trow.place 0 (2 * lam + x / 99) (x % 99) := by
    show _ = trow.OFF + (0 * trow.cnt + (2 * lam + x / 99)) * trow.J + x % 99
    rw [hJ, Nat.zero_mul, Nat.zero_add]
  have hk : (fun i => key D t tb L0 w .ROW lam x i) = fun i =>
      ((Inst.Model.Ledger.mu (x % 99) : ℤ) : K) *
        (c trow.mat (tenCell trow.place 0 (2 * lam + x / 99) (x % 99)) i + 128) := by
    funext i
    simp [key, Inst.Model.FFSeg.led, Inst.Model.FFSeg.val, Inst.Model.FFSeg.nLedger, Arr.nCell,
      Arr.off, T.2]
  show _ = ρ.val (ew.getD x zeroE) * Blocks.ext D.lT (fun i => key D t tb L0 w .ROW lam x i) u
  rw [hk, Blocks.ext_smul, Blocks.ext_add, Blocks.ext_const, F.num.scaleNat, Aff.value_add,
    Aff.value_ofConst, F.num.ofNat, R _ _ h1, hc, ← ledMu_five]
  push_cast
  ring

/-- DD: each expert's logit against the chosen one's; the affine part of the key. -/
theorem Fits.line_DD (lam : ℕ) {ew wh : Array E} {f : Aff} (h : v.line "DD" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .DD) (fun x i => lin D t tb L0 w .DD lam x i) := by
  rw [line_DD_eq, F.NE] at h
  cases h1 : (List.range D.nx).reverse.foldlM (stepDD v (lam / 2) ew) (aff0, aff0) with
  | none => rw [h1] at h; cases h
  | some r =>
    rw [h1] at h
    cases h
    rw [foldDD_value F.num (fun x => Blocks.ext D.lT (raw t .lr (lam / 2) x) u)
      (fun x => Blocks.ext D.lT (raw t .sel (lam / 2) x) u)
      (fun x a ha => F.shA .lr rfl ha) (fun x a ha => F.shA .sel rfl ha)
      D.nx _ r h1, aff0_value, zero_add]
    show _ = ∑ x ∈ range D.nx, _
    refine sum_congr rfl fun x _ => ?_
    have hk : (fun i => lin D t tb L0 w .DD lam x i) = fun i =>
        (0 - raw t .lr (lam / 2) x i) -
          ∑ e ∈ range D.nx, (if x < e then raw t .sel (lam / 2) e i else 0) := by
      funext i
      simp only [lin, raw, Arr.off, Int.cast_zero, sub_zero, Finset.sum_filter]
      ring
    have hz : ∀ e, Blocks.ext D.lT (fun i => if x < e then raw t .sel (lam / 2) e i else 0) u =
        if x < e then Blocks.ext D.lT (raw t .sel (lam / 2) e) u else 0 := by
      intro e
      split_ifs
      · rfl
      · exact Blocks.ext_const D.lT 0 u
    show _ = ρ.val (ew.getD x zeroE) * Blocks.ext D.lT (fun i => lin D t tb L0 w .DD lam x i) u
    rw [hk, Blocks.ext_sub, Blocks.ext_sub, Blocks.ext_const, Blocks.ext_sum]
    simp only [hz]
    ring

end Families

#print axioms Fits.line_SEL
#print axioms Fits.line_CN1
#print axioms Fits.line_VH
#print axioms Fits.line_V
#print axioms Fits.line_CQK
#print axioms Fits.line_O
#print axioms Fits.line_QKH
#print axioms Fits.line_ROW
#print axioms Fits.line_DD

end OnBytes.Road
