-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysB.lean: the forms of nine segments of a layer sub-proof's lookup against the
library's keys: L3, LT, CLR, LH, LR, XR, MR, UT, G0.

Johnson/Road/FormsKeysKit.lean says what is compared and in what sense, and has the record Fits of
all hypotheses. For each segment there are two statements here: what Env.line is at the segment's
name (by unfolding alone), and what that form is worth under Fits. For L3, LT, CLR, LH, UT and G0
the key is affine in the cells, and the form is worth the weighted sum of the extensions of the keys
themselves. For LR, XR and MR the key also holds a product; the form is worth the weighted sum of
the extensions of the key's affine part (FFSeg.lin).

The router's shift is read by the forms of LH and LR. The verifier takes it to be 0 on a layer
without routed experts; the library has a shift for every layer. The two statements on LH and LR are
therefore made for the odd layers of a group, the layers on which the library has these families.

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

/-- What line is at the segment L3. -/
theorem line_L3_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "L3" lam ew wh = sumForms v.y.h.NE (fun x => do
      pure (← v.shA "l3" "zt" (lam / 2) x, Model.scaleNat (ew.getD x zeroE) 32)) := by
  rfl

/-- What line is at the segment LT. -/
theorem line_LT_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "LT" lam ew wh = sumForms v.y.h.NE (fun x => do
      pure ((← v.shA "lr" "zt" (lam / 2) x) + Aff.ofConst (pw 14),
        Model.scaleNat (ew.getD x zeroE) 2)) := by
  rfl

/-- What line is at the segment CLR. -/
theorem line_CLR_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "CLR" lam ew wh = (do
      let a ← sumForms v.y.h.NE fun x => do
        pure ((← v.shA "ly" "zt" (lam / 2) x) +
          ((← v.shA "lr" "zt" (lam / 2) x) - (← v.shA "l3" "zt" (lam / 2) x)).scale (pw 25),
          ew.getD x zeroE)
      pure (a + Aff.ofConst (mulE (sumE ew) Env.clampKey))) := by
  rfl

/-- What line is at the segment LH. -/
theorem line_LH_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "LH" lam ew wh = (do
      let a ← v.shSum ew v.y.h.NE "rl" "zt" (lam / 2)
      pure (Env.high (sumE ew) a (if v.isMoe lam then v.sc.klM (v.lay lam) 0 else 0)
        v.y.h.hr)) := by
  rfl

/-- What line is at the segment LR. -/
theorem line_LR_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "LR" lam ew wh = (do
      let q ← if v.y.h.rcl then
          sumForms v.y.h.NE fun x => do
            pure ((← v.shA "ly" "zt" (lam / 2) x).scale (Model.ofNat 8) +
              (← v.shA "l3" "zt" (lam / 2) x), ew.getD x zeroE)
        else v.shSum ew v.y.h.NE "lr" "zt" (lam / 2)
      Env.site (sumE ew) q (if v.isMoe lam then v.sc.klM (v.lay lam) 0 else 0) v.y.h.hr
        fun _ => v.shSum ew v.y.h.NE "rl" "zt" (lam / 2)) := by
  rfl

/-- What line is at the segment XR. -/
theorem line_XR_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "XR" lam ew wh = (do
      let a ← v.shSum ew v.y.h.d "xr" "zt" (lam / 2)
      pure (Aff.ofConst (mulE (sumE ew) (pw 15)) - a.scale (pw 16))) := by
  rfl

/-- What line is at the segment MR. -/
theorem line_MR_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "MR" lam ew wh = (do
      let a ← v.shA "sc" "zt" (lam / 2) 0
      pure ((Aff.ofConst (pw (if v.y.h.gcl then 14 else 15)) + a.scale (pw 17)).scale
        (ew.getD 0 zeroE))) := by
  rfl

/-- What line is at the segment UT. -/
theorem line_UT_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "UT" lam ew wh = (do
      let a ← v.SA wh "u" lam "Z"
      pure (a + Aff.ofConst (mulE (sumE ew) (pw Model.Layer.LBU)))) := by
  rfl

/-- What line is at the segment G0. -/
theorem line_G0_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "G0" lam ew wh = (do
      let a ← v.SA wh "g0" lam "Z"
      pure (a + Aff.ofConst (mulE (sumE ew) (Model.ofNat 128)))) := by
  rfl

end Eqs

/-! ## Tools -/

/-- If a do block that makes a value from one optional value returns a value, the optional value is
there. -/
private theorem pure_some {α β : Type} {o : Option α} {g : α → β} {y : β}
    (h : (do let a ← o; pure (g a)) = some y) : ∃ a, o = some a ∧ g a = y := by
  cases o with
  | none => cases h
  | some a => cases h; exact ⟨a, rfl, rfl⟩

/-- The same for two optional values. -/
private theorem pure_some₂ {α β γ : Type} {o : Option α} {p : Option β} {g : α → β → γ} {y : γ}
    (h : (do let a ← o; let b ← p; pure (g a b)) = some y) :
    ∃ a b, o = some a ∧ p = some b ∧ g a b = y := by
  cases o with
  | none => cases h
  | some a =>
    cases p with
    | none => cases h
    | some b => cases h; exact ⟨a, b, rfl, rfl, rfl⟩

/-- The same for three optional values. -/
private theorem pure_some₃ {α β γ δ : Type} {o : Option α} {p : Option β} {q : Option γ}
    {g : α → β → γ → δ} {y : δ}
    (h : (do let a ← o; let b ← p; let c ← q; pure (g a b c)) = some y) :
    ∃ a b c, o = some a ∧ p = some b ∧ q = some c ∧ g a b c = y := by
  cases o with
  | none => cases h
  | some a =>
    cases p with
    | none => cases h
    | some b =>
      cases q with
      | none => cases h
      | some c => cases h; exact ⟨a, b, c, rfl, rfl, rfl, rfl⟩

/-- The sum of the weights of a segment with n entries that is not read by blocks. -/
private theorem sumE_size {ρ : Reading K} {ew : Array E} {n : ℕ} (hs : ew.size = n) :
    ρ.val (sumE ew) = ∑ x ∈ range n, wt ρ ew x := by
  rw [sumE_value, hs]

/-! ## What the forms are worth -/

section Families

variable {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim} {c : Cells K} {t : Cell → K}
  {low u : ℕ → K} (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
include F

/-- The router's shift, as the forms of LH and LR read it, is the library's on an odd layer. -/
theorem Fits.kr_odd {lam : ℕ} (hlam : lam < D.nl) (hodd : lam % 2 = 1) :
    (if v.isMoe lam then v.sc.klM (v.lay lam) 0 else 0) = (D.Pl lam).kr := by
  have hm : v.isMoe lam = true := by
    rw [F.isMoe]
    simp [Inst.Model.FFSeg.isExpL, hodd]
  rw [hm]
  exact F.kr lam hlam hodd

/-- L3: the low three bits of the router's logits under the factor 32. -/
theorem Fits.line_L3 (lam : ℕ) {ew wh : Array E} {f : Aff} (h : v.line "L3" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .L3) (fun x i => key D t tb L0 w .L3 lam x i) := by
  rw [line_L3_eq, F.NE] at h
  refine sumForms_value ρ W _ _ _ ?_ h
  intro x a k hb
  obtain ⟨h1, h2⟩ := bind_pair_some hb
  subst h2
  have hk : (fun i => key D t tb L0 w .L3 lam x i) =
      fun i => (32 : K) * raw t .l3 (lam / 2) x i := by
    funext i
    simp only [key, raw, Arr.off]
    push_cast
    ring
  show _ = ρ.val (ew.getD x zeroE) * Blocks.ext D.lT (fun i => key D t tb L0 w .L3 lam x i) u
  rw [F.num.scaleNat, F.shA .l3 rfl h1, hk, Blocks.ext_smul]
  push_cast
  ring

/-- LT: the router's clamped logits, moved by 2^14, under the factor 2. -/
theorem Fits.line_LT (lam : ℕ) {ew wh : Array E} {f : Aff} (h : v.line "LT" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .LT) (fun x i => key D t tb L0 w .LT lam x i) := by
  rw [line_LT_eq, F.NE] at h
  refine sumForms_value ρ W _ _ _ ?_ h
  intro x a k hb
  obtain ⟨A, h1, h2⟩ := pure_some hb
  cases h2
  have hk : (fun i => key D t tb L0 w .LT lam x i) =
      fun i => (2 : K) * (raw t .lr (lam / 2) x i + (2 : K) ^ 14) := by
    funext i
    simp only [key, raw, Arr.off]
    push_cast
    ring
  show _ = ρ.val (ew.getD x zeroE) * Blocks.ext D.lT (fun i => key D t tb L0 w .LT lam x i) u
  rw [F.num.scaleNat, Aff.value_add, Aff.value_ofConst, F.num.pw, F.shA .lr rfl h1, hk,
    Blocks.ext_smul, Blocks.ext_add, Blocks.ext_const]
  push_cast
  ring

/-- CLR: the clamp of the router's logits. -/
theorem Fits.line_CLR (lam : ℕ) {ew wh : Array E} (hsz : ew.size = len D .CLR) {f : Aff}
    (h : v.line "CLR" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .CLR) (fun x i => key D t tb L0 w .CLR lam x i) := by
  have hs : ew.size = D.nx := hsz
  rw [line_CLR_eq, F.NE] at h
  obtain ⟨A, h1, h2⟩ := pure_some h
  cases h2
  have hA : A.value ρ W = wsum (wt ρ ew) D.lT u D.nx (fun x i => raw t .ly (lam / 2) x i +
      (2 : K) ^ 25 * (raw t .lr (lam / 2) x i - raw t .l3 (lam / 2) x i)) := by
    refine sumForms_value ρ W _ _ _ ?_ h1
    intro x a k hb
    obtain ⟨a1, a2, a3, g1, g2, g3, g4⟩ := pure_some₃ hb
    cases g4
    show _ = ρ.val (ew.getD x zeroE) * Blocks.ext D.lT (fun i => raw t .ly (lam / 2) x i +
      (2 : K) ^ 25 * (raw t .lr (lam / 2) x i - raw t .l3 (lam / 2) x i)) u
    rw [Aff.value_add, Aff.value_scale, Aff.value_sub, F.num.pw, F.shA .ly rfl g1,
      F.shA .lr rfl g2, F.shA .l3 rfl g3, Blocks.ext_add, Blocks.ext_smul, Blocks.ext_sub]
  have e : ∀ x, x < D.nx → ∀ i, key D t tb L0 w .CLR lam x i =
      (raw t .ly (lam / 2) x i +
        (2 : K) ^ 25 * (raw t .lr (lam / 2) x i - raw t .l3 (lam / 2) x i)) +
        ((2 : K) ^ 15 + (2 : K) ^ 39) := by
    intro x _ i
    simp only [key, raw, Arr.off]
    push_cast
    ring
  show _ = wsum (wt ρ ew) D.lT u D.nx _
  rw [wsum_congr _ _ _ _ e, wsum_add, wsum_const, Aff.value_add, Aff.value_ofConst, ρ.mul,
    sumE_size hs, clampKey_value F.num, hA]

/-- LH: the high digit of the rounding that gives the router's logits, on an odd layer. -/
theorem Fits.line_LH (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hsz : ew.size = len D .LH) (hodd : lam % 2 = 1)
    {f : Aff} (h : v.line "LH" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .LH) (fun x i => key D t tb L0 w .LH lam x i) := by
  have hs : ew.size = D.nx := hsz
  rw [line_LH_eq, F.NE, F.hr, F.kr_odd hlam hodd] at h
  obtain ⟨A, h1, h2⟩ := pure_some h
  cases h2
  have e : ∀ x, x < D.nx → ∀ i, key D t tb L0 w .LH lam x i =
      (2 : K) ^ (24 - max (D.Pl lam).kr 16) * (raw t .rl (lam / 2) x i + 128) := by
    intro x _ i
    simp only [key, Inst.Model.Site.shigh_eq, Inst.Model.Site.up, raw, Arr.off]
    push_cast
    ring
  show _ = wsum (wt ρ ew) D.lT u D.nx _
  rw [wsum_congr _ _ _ _ e, wsum_smul, wsum_add, wsum_const, high_value F.num, oOf_one F.num,
    sumE_size hs, F.shSum .rl rfl h1]
  show (2 : K) ^ (24 - max (D.Pl lam).kr 16) * _ = _
  ring

/-- LR: the rounding that gives the router's logits, on an odd layer; the affine part of the key.
The quotient is 8 ly + l3. -/
theorem Fits.line_LR (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hsz : ew.size = len D .LR) (hodd : lam % 2 = 1)
    {f : Aff} (h : v.line "LR" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .LR) (fun x i => lin D t tb L0 w .LR lam x i) := by
  have hs : ew.size = D.nx := hsz
  rw [line_LR_eq, F.rcl, F.NE, F.hr, F.kr_odd hlam hodd] at h
  have h' : (do
      let q ← sumForms D.nx fun x => do
        pure ((← v.shA "ly" "zt" (lam / 2) x).scale (Model.ofNat 8) +
          (← v.shA "l3" "zt" (lam / 2) x), ew.getD x zeroE)
      Env.site (sumE ew) q (D.Pl lam).kr 1 fun _ => v.shSum ew D.nx "rl" "zt" (lam / 2)) =
      some f := h
  obtain ⟨Q, h1, h2⟩ := bind_some h'
  obtain ⟨S, h3, h4⟩ := site_value (W := W) F.num rfl h2
  have hQ : Q.value ρ W = wsum (wt ρ ew) D.lT u D.nx
      (fun x i => (8 : K) * raw t .ly (lam / 2) x i + raw t .l3 (lam / 2) x i) := by
    refine sumForms_value ρ W _ _ _ ?_ h1
    intro x a k hb
    obtain ⟨a1, a2, g1, g2, g3⟩ := pure_some₂ hb
    cases g3
    show _ = ρ.val (ew.getD x zeroE) * Blocks.ext D.lT
      (fun i => (8 : K) * raw t .ly (lam / 2) x i + raw t .l3 (lam / 2) x i) u
    rw [Aff.value_add, Aff.value_scale, F.num.ofNat, Nat.cast_ofNat, F.shA .ly rfl g1,
      F.shA .l3 rfl g2, Blocks.ext_add, Blocks.ext_smul]
  have e : ∀ x, x < D.nx → ∀ i, lin D t tb L0 w .LR lam x i =
      (2 : K) ^ (16 - (D.Pl lam).kr) * ((2 : K) ^ ((D.Pl lam).kr - 1) - (2 : K) ^ (D.Pl lam).kr *
        ((8 : K) * raw t .ly (lam / 2) x i + raw t .l3 (lam / 2) x i)) -
      (2 : K) ^ 16 * (raw t .rl (lam / 2) x i + 128) := by
    intro x _ i
    simp only [lin, Inst.Model.FFSeg.lw, Inst.Model.Site.ssite_eq, Inst.Model.Site.dn, raw, Arr.off]
    push_cast
    ring
  show _ = wsum (wt ρ ew) D.lT u D.nx _
  rw [wsum_congr _ _ _ _ e, wsum_sub, wsum_smul, wsum_sub, wsum_const, wsum_smul, ← hQ, wsum_smul,
    wsum_add, wsum_const, h4, oOf_one F.num, sumE_size hs, F.shSum .rl rfl h3]
  ring

/-- XR: the rounding that gives the routed expert's input; the affine part of the key. -/
theorem Fits.line_XR (lam : ℕ) {ew wh : Array E} (hsz : ew.size = len D .XR) {f : Aff}
    (h : v.line "XR" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .XR) (fun x i => lin D t tb L0 w .XR lam x i) := by
  have hs : ew.size = D.d := hsz
  rw [line_XR_eq, F.d] at h
  obtain ⟨A, h1, h2⟩ := pure_some h
  cases h2
  have e : ∀ x, x < D.d → ∀ i, lin D t tb L0 w .XR lam x i =
      (2 : K) ^ 15 - (2 : K) ^ 16 * raw t .xr (lam / 2) x i := by
    intro x _ i
    simp only [lin, raw, Arr.off]
    push_cast
    ring
  show _ = wsum (wt ρ ew) D.lT u D.d _
  rw [wsum_congr _ _ _ _ e, wsum_sub, wsum_const, wsum_smul, Aff.value_sub, Aff.value_ofConst,
    Aff.value_scale, ρ.mul, F.num.pw, F.num.pw, sumE_size hs, F.shSum .xr rfl h1]

/-- MR: the chosen expert's logit and its score in one key; the affine part of the key, which holds
the score and not the logit. The segment has one entry. -/
theorem Fits.line_MR (lam : ℕ) {ew wh : Array E} {f : Aff} (h : v.line "MR" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .MR) (fun x i => lin D t tb L0 w .MR lam x i) := by
  rw [line_MR_eq, F.gcl] at h
  have h' : (do
      let a ← v.shA "sc" "zt" (lam / 2) 0
      pure ((Aff.ofConst (pw 14) + a.scale (pw 17)).scale (ew.getD 0 zeroE))) = some f := h
  obtain ⟨A, h1, h2⟩ := pure_some h'
  cases h2
  have hk : (fun i => lin D t tb L0 w .MR lam 0 i) =
      fun i => (2 : K) ^ 14 + (2 : K) ^ 17 * raw t .sc (lam / 2) 0 i := by
    funext i
    simp only [lin, raw, Arr.off]
    push_cast
    ring
  show _ = ∑ x ∈ range 1,
    ρ.val (ew.getD x zeroE) * Blocks.ext D.lT (fun i => lin D t tb L0 w .MR lam x i) u
  rw [Finset.sum_range_one, hk, Blocks.ext_add, Blocks.ext_const, Blocks.ext_smul, Aff.value_scale,
    Aff.value_add, Aff.value_ofConst, Aff.value_scale, F.num.pw, F.num.pw, F.shA .sc rfl h1]

/-- UT: the range of the up product. -/
theorem Fits.line_UT (lam : ℕ) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff}
    (h : v.line "UT" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .UT) (fun x i => key D t tb L0 w .UT lam x i) := by
  have hL : Model.Layer.LBU = 15 := rfl
  rw [line_UT_eq, hL] at h
  obtain ⟨A, h1, h2⟩ := pure_some h
  cases h2
  have e : ∀ x, x < D.f → ∀ i, key D t tb L0 w .UT lam x i =
      raw t .up lam x i + (2 : K) ^ 15 := by
    intro x _ i
    simp only [key, raw, Arr.off]
    push_cast
    ring
  show _ = wsum (wt ρ ew) D.lT u D.f _
  rw [wsum_congr _ _ _ _ e, wsum_add, wsum_const, Aff.value_add, Aff.value_ofConst, ρ.mul,
    F.num.pw, hw.sumE, F.SA .up rfl hw h1]

/-- G0: the range of the gate's low byte. -/
theorem Fits.line_G0 (lam : ℕ) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff}
    (h : v.line "G0" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .G0) (fun x i => key D t tb L0 w .G0 lam x i) := by
  rw [line_G0_eq] at h
  obtain ⟨A, h1, h2⟩ := pure_some h
  cases h2
  have e : ∀ x, x < D.f → ∀ i, key D t tb L0 w .G0 lam x i = raw t .g0 lam x i + (128 : K) := by
    intro x _ i
    simp only [key, raw, Arr.off]
    push_cast
    ring
  show _ = wsum (wt ρ ew) D.lT u D.f _
  rw [wsum_congr _ _ _ _ e, wsum_add, wsum_const, Aff.value_add, Aff.value_ofConst, ρ.mul,
    F.num.ofNat, Nat.cast_ofNat, hw.sumE, F.SA .g0 rfl hw h1]

end Families

#print axioms Fits.line_L3
#print axioms Fits.line_LT
#print axioms Fits.line_CLR
#print axioms Fits.line_LH
#print axioms Fits.line_LR
#print axioms Fits.line_XR
#print axioms Fits.line_MR
#print axioms Fits.line_UT
#print axioms Fits.line_G0

end OnBytes.Road
