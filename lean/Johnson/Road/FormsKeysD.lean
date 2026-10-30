-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysD.lean: the forms of six segments of a layer sub-proof's lookup against the
library's keys: GH, UH, D, QK, G, U.

Johnson/Road/FormsKeysKit.lean says what is compared and in what sense, and has the record Fits of
all hypotheses. For each segment there are two statements here: what Env.line is at the segment's
name (by unfolding alone), and what that form is worth under Fits. For GH and UH the key is affine
in the cells, and the form is worth the weighted sum of the extensions of the keys themselves. For
D, QK, G and U the key also holds a product; the form is worth the weighted sum of the extensions of
the key's affine part (FFSeg.lin).

The segments GH, UH, G and U differ from layer to layer. On a layer without routed experts all
hidden units have one shift. On a layer with routed experts the first fe units belong to the shared
expert and the others to the routed one, and each half has its own shift. The verifier tests the
layer and then builds one form or the sum of two; the library chooses the shift unit by unit. Each
proof here splits on the layer's number being odd.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysKit

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff tenCell TenAt)
open OnBytes.Model.Layer (Env Ten sumForms aff0 pw sumE sumR)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key lin len val gw kG kU kQK routed isExpL xS)
open Inst.Model.Site (ssite shigh)

variable {K : Type} [Field K]

/-! ## What line is at each segment -/

section Eqs

/-- What line is at the segment GH. -/
theorem line_GH_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "GH" lam ew wh = (if !v.isMoe lam then do
      let a ← v.SA wh "rg" lam "Z"
      pure (Env.high (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.Lkg) v.y.h.hgD)
    else do
      let a ← v.SBA wh 0 v.y.h.fe "rg" lam "Z" 0
      let b ← v.SBA wh v.y.h.fe v.y.h.f "rg" lam "Z" 0
      pure (Env.high (sumR ew 0 v.y.h.fe) a (v.sc.kl (v.lay lam) Model.Layer.Lkg) v.y.h.hgD +
        Env.high (sumR ew v.y.h.fe v.y.h.f) b (v.sc.klM (v.lay lam) 1) v.y.h.hgD)) := by
  rfl

/-- What line is at the segment UH. -/
theorem line_UH_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "UH" lam ew wh = (if !v.isMoe lam then do
      let a ← v.SA wh "ru" lam "Z"
      pure (Env.high (sumE ew) a (v.sc.kl (v.lay lam) Model.Layer.Lku) v.y.h.huD)
    else do
      let a ← v.SBA wh 0 v.y.h.fe "ru" lam "Z" 0
      let b ← v.SBA wh v.y.h.fe v.y.h.f "ru" lam "Z" 0
      pure (Env.high (sumR ew 0 v.y.h.fe) a (v.sc.kl (v.lay lam) Model.Layer.Lku) v.y.h.huD +
        Env.high (sumR ew v.y.h.fe v.y.h.f) b (v.sc.klM (v.lay lam) 2) v.y.h.huD)) := by
  rfl

/-- What line is at the segment D. -/
theorem line_D_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "D" lam ew wh = (do
      let a ← v.SxsA wh "Z" (2 * lam + 2)
      let b ← v.SxsA wh "Z" (2 * lam + 1)
      Env.site (sumE ew) (a - b) (v.sc.kl (v.lay lam) Model.Layer.Lkd) v.y.h.hdD
        fun _ => v.SA wh "rd" lam "Z") := by
  rfl

/-- What line is at the segment QK. -/
theorem line_QK_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "QK" lam ew wh = (do
      let p ← (do
        let a ← v.SBA wh 0 v.y.dq "qkw" lam "Z" 0
        Env.site (sumR ew 0 v.y.dq) a (v.sc.kl (v.lay lam) Model.Layer.Lkq) v.y.h.hq
          fun _ => v.SBA wh 0 v.y.dq "rqk" lam "Z" 0)
      let q ← (do
        let b ← v.SBA wh v.y.dq v.y.nqk "qkw" lam "Z" 0
        Env.site (sumR ew v.y.dq v.y.nqk) b (v.sc.kl (v.lay lam) Model.Layer.Lkk) v.y.h.hq
          fun _ => v.SBA wh v.y.dq v.y.nqk "rqk" lam "Z" 0)
      pure (p + q)) := by
  rfl

/-- The quotient of the gate's rounding over the entries a to b - 1 of the segment G. If the gate's
clamp is on, the quotient lies in two tensors: its low byte in g0 and the rest in gh. -/
def gateQ (v : Env) (lam : ℕ) (wh : Array E) (a b : ℕ) : Option Aff :=
  if !v.y.h.gcl then v.SBA wh a b "gi" lam "Z" 0
  else do
    let x ← v.SBA wh a b "g0" lam "Z" 0
    let y ← v.SBA wh a b "gh" lam "Z" 0
    pure (x + y.scale (Model.ofNat 256))

/-- What line is at the segment G. -/
theorem line_G_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "G" lam ew wh = (if !v.isMoe lam then do
      let q ← gateQ v lam wh 0 v.y.h.f
      Env.site (sumE ew) q (v.sc.kl (v.lay lam) Model.Layer.Lkg) v.y.h.hgD
        fun _ => v.SA wh "rg" lam "Z"
    else do
      let p ← gateQ v lam wh 0 v.y.h.fe
      let a ← Env.site (sumR ew 0 v.y.h.fe) p (v.sc.kl (v.lay lam) Model.Layer.Lkg) v.y.h.hgD
        fun _ => v.SBA wh 0 v.y.h.fe "rg" lam "Z" 0
      let q ← gateQ v lam wh v.y.h.fe v.y.h.f
      let b ← Env.site (sumR ew v.y.h.fe v.y.h.f) q (v.sc.klM (v.lay lam) 1) v.y.h.hgD
        fun _ => v.SBA wh v.y.h.fe v.y.h.f "rg" lam "Z" 0
      pure (a + b)) := by
  rfl

/-- What line is at the segment U. -/
theorem line_U_eq (v : Env) (lam : ℕ) (ew wh : Array E) :
    v.line "U" lam ew wh = (if !v.isMoe lam then do
      let q ← v.SBA wh 0 v.y.h.f "u" lam "Z" 0
      Env.site (sumE ew) q (v.sc.kl (v.lay lam) Model.Layer.Lku) v.y.h.huD
        fun _ => v.SA wh "ru" lam "Z"
    else do
      let p ← v.SBA wh 0 v.y.h.fe "u" lam "Z" 0
      let a ← Env.site (sumR ew 0 v.y.h.fe) p (v.sc.kl (v.lay lam) Model.Layer.Lku) v.y.h.huD
        fun _ => v.SBA wh 0 v.y.h.fe "ru" lam "Z" 0
      let q ← v.SBA wh v.y.h.fe v.y.h.f "u" lam "Z" 0
      let b ← Env.site (sumR ew v.y.h.fe v.y.h.f) q (v.sc.klM (v.lay lam) 2) v.y.h.huD
        fun _ => v.SBA wh v.y.h.fe v.y.h.f "ru" lam "Z" 0
      pure (a + b)) := by
  rfl

end Eqs

/-! ## Tools -/

/-- An odd layer has routed experts. -/
theorem isExpL_odd {l : ℕ} (h : l % 2 = 1) : isExpL l = true := by
  simp [isExpL, h]

/-- An even layer has none. -/
theorem isExpL_even {l : ℕ} (h : ¬ l % 2 = 1) : isExpL l = false := by
  simp [isExpL, h]

/-- On an even layer no hidden unit belongs to a routed expert. -/
theorem routed_even (D : Dim) {l : ℕ} (h : ¬ l % 2 = 1) (x : ℕ) : routed D l x = false := by
  unfold routed
  rw [isExpL_even h, Bool.false_and]

/-- The first fe hidden units belong to no routed expert. -/
theorem routed_low (D : Dim) (l : ℕ) {x : ℕ} (h : x < D.fe) : routed D l x = false := by
  unfold routed
  rw [decide_eq_false (by omega : ¬ D.fe ≤ x), Bool.and_false]

/-- On an odd layer the hidden units from fe on belong to the routed expert. -/
theorem routed_high (D : Dim) {l : ℕ} (h : l % 2 = 1) (y : ℕ) : routed D l (D.fe + y) = true := by
  unfold routed
  rw [isExpL_odd h, decide_eq_true (by omega : D.fe ≤ D.fe + y), Bool.and_true]

section Shifts

variable [scl : Scl] (D : Dim) {l x : ℕ}

/-- The gate's shift at a unit of no routed expert. -/
theorem kG_shared (h : routed D l x = false) : kG D l x = (D.Pl l).kg := by
  simp [kG, h]

/-- The gate's shift at a unit of the routed expert. -/
theorem kG_routed (h : routed D l x = true) : kG D l x = (D.Pl l).kg' := by
  simp [kG, h]

/-- The up projection's shift at a unit of no routed expert. -/
theorem kU_shared (h : routed D l x = false) : kU D l x = (D.Pl l).ku := by
  simp [kU, h]

/-- The up projection's shift at a unit of the routed expert. -/
theorem kU_routed (h : routed D l x = true) : kU D l x = (D.Pl l).ku' := by
  simp [kU, h]

end Shifts

section Sums

variable {ρ : Reading K} {W : World K}

/-- The sum of the m weights from entry a on. -/
theorem sumR_stretch (ew : Array E) (a m : ℕ) (hb : a + m ≤ ew.size) :
    ρ.val (sumR ew a (a + m)) = ∑ y ∈ range m, wt ρ ew (a + y) := by
  rw [sumR_value ρ ew a (a + m) hb, Nat.add_sub_cancel_left]

/-- The key of the high digits, if the digits are worth a weighted sum of extensions: the weighted
sum of the extensions of the library's high keys. Rf: the digits without their offset. -/
theorem high_wsum (hρ : Numerals ρ) {g : ℕ → K} {lt : ℕ} {u : ℕ → K} {m : ℕ} {w : E} {S : Aff}
    (k : ℕ) {form top : ℕ} {Rf : ℕ → ℕ → K} (ht : (if form == 1 then 24 else 32) = top)
    (hw : ρ.val w = ∑ x ∈ range m, g x) (hS : S.value ρ W = wsum g lt u m Rf) :
    (Env.high w S k form).value ρ W =
      wsum g lt u m (fun y i => shigh (Rf y i + ρ.val (Env.oOf form)) k top) := by
  have e : ∀ x, x < m → ∀ i, shigh (Rf x i + ρ.val (Env.oOf form)) k top =
      (2 : K) ^ (top - max k 16) * (Rf x i + ρ.val (Env.oOf form)) := by
    intro x _ i
    rw [Inst.Model.Site.shigh_eq]
    rfl
  rw [wsum_congr _ _ _ _ e, wsum_smul, wsum_add, wsum_const, high_value hρ, ht, hw, hS]
  ring

/-- The low key without its accumulator, if the quotient and the high digits are worth weighted sums
of extensions: the weighted sum of the extensions of the library's low keys at the accumulator 0.
Qf: the quotient; Rf: the digits without their offset. -/
theorem site_wsum (hρ : Numerals ρ) {g : ℕ → K} {lt : ℕ} {u : ℕ → K} {m : ℕ} {w : E} {SQ : Aff}
    {k form : ℕ} {Srh : Unit → Option Aff} {Qf Rf : ℕ → ℕ → K} (hf : (form == 0) = false)
    (hw : ρ.val w = ∑ x ∈ range m, g x) (hQ : SQ.value ρ W = wsum g lt u m Qf)
    (hR : ∀ S, Srh () = some S → S.value ρ W = wsum g lt u m Rf) {f : Aff}
    (h : Env.site w SQ k form Srh = some f) :
    f.value ρ W =
      wsum g lt u m (fun y i => ssite 0 (Qf y i) (Rf y i + ρ.val (Env.oOf form)) k) := by
  obtain ⟨S, h2, h3⟩ := site_value (W := W) hρ hf h
  have e : ∀ x, x < m → ∀ i, ssite 0 (Qf x i) (Rf x i + ρ.val (Env.oOf form)) k =
      (2 : K) ^ (16 - k) * ((2 : K) ^ (k - 1) - (2 : K) ^ k * Qf x i) -
        (2 : K) ^ 16 * (Rf x i + ρ.val (Env.oOf form)) := by
    intro x _ i
    simp only [Inst.Model.Site.ssite_eq, Inst.Model.Site.dn]
    ring
  rw [wsum_congr _ _ _ _ e, wsum_sub, wsum_smul, wsum_sub, wsum_const, wsum_smul, wsum_smul,
    wsum_add, wsum_const, h3, hw, hQ, hR S h2]
  ring

end Sums

/-! ## Readings, high keys and low keys under the record -/

section Families

variable {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim} {c : Cells K} {t : Cell → K}
  {low u : ℕ → K} (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
include F

/-- The offset of a digit tensor of form 1 is that of an array with the offset 128. -/
theorem Fits.off1 (X : Arr) (hX : X.off = 128) : ρ.val (Env.oOf 1) = ((X.off : ℤ) : K) := by
  rw [oOf_one F.num, hX]
  norm_num

/-- The offset of a digit tensor of form 2 is that of an array with the offset 32896. -/
theorem Fits.off2 (X : Arr) (hX : X.off = 32896) : ρ.val (Env.oOf 2) = ((X.off : ℤ) : K) := by
  rw [oOf_two F.num, hX]
  norm_num

/-- A stretch of an array without offset: m entries from entry a0 of the segment on, where the
segment's entry 0 is the array's first channel. -/
theorem Fits.stretch (X : Arr) (hX : readLong X = true) (h0 : X.off = 0) {ew wh : Array E} {n : ℕ}
    (hw : Wts ρ ew wh v.y.ls low n) {lam a0 b0 m : ℕ} (hb : b0 = a0 + m)
    (ha : ∃ q, a0 = q * 2 ^ v.y.ls) (hm : ∃ q, m = q * 2 ^ v.y.ls) {a : Aff}
    (h : v.SBA wh a0 b0 (arrName X) lam "Z" 0 = some a) :
    a.value ρ W =
      wsum (fun y => wt ρ ew (a0 + y)) D.lT u m (fun y i => val t X lam (a0 + y) i) := by
  subst hb
  have e := F.SBA X hX hw ha hm ⟨0, (Nat.zero_mul _).symm⟩ (Nat.zero_le _) h
  rw [e]
  exact wsum_congr _ _ _ _ fun y _ i => by
    simp only [raw, h0, Int.cast_zero, sub_zero, Nat.sub_zero]

/-- The high key of a stretch of a segment. X: the array of the high digits. -/
theorem Fits.highS (X : Arr) (hX : readLong X = true) {ew wh : Array E} {n : ℕ}
    (hw : Wts ρ ew wh v.y.ls low n) {lam a0 b0 m : ℕ} (k : ℕ) {form top : ℕ} (hb : b0 = a0 + m)
    (hn : b0 ≤ n) (ha : ∃ q, a0 = q * 2 ^ v.y.ls) (hm : ∃ q, m = q * 2 ^ v.y.ls)
    (ht : (if form == 1 then 24 else 32) = top) (ho : ρ.val (Env.oOf form) = ((X.off : ℤ) : K))
    {S : Aff} (h : v.SBA wh a0 b0 (arrName X) lam "Z" 0 = some S) :
    (Env.high (sumR ew a0 b0) S k form).value ρ W =
      wsum (fun y => wt ρ ew (a0 + y)) D.lT u m
        (fun y i => shigh (val t X lam (a0 + y) i) k top) := by
  subst hb
  have e := F.SBA X hX hw ha hm ⟨0, (Nat.zero_mul _).symm⟩ (Nat.zero_le _) h
  rw [high_wsum F.num k ht (sumR_stretch ew a0 m (by rw [hw.size]; exact hn)) e]
  exact wsum_congr _ _ _ _ fun y _ i => by simp only [ho, raw, sub_add_cancel, Nat.sub_zero]

/-- The high key of a whole segment. -/
theorem Fits.highW (X : Arr) (hX : readLong X = true) {ew wh : Array E} {n : ℕ}
    (hw : Wts ρ ew wh v.y.ls low n) {lam : ℕ} (k : ℕ) {form top : ℕ}
    (ht : (if form == 1 then 24 else 32) = top) (ho : ρ.val (Env.oOf form) = ((X.off : ℤ) : K))
    {S : Aff} (h : v.SA wh (arrName X) lam "Z" = some S) :
    (Env.high (sumE ew) S k form).value ρ W =
      wsum (wt ρ ew) D.lT u n (fun x i => shigh (val t X lam x i) k top) := by
  rw [high_wsum F.num k ht hw.sumE (F.SA X hX hw h)]
  exact wsum_congr _ _ _ _ fun y _ i => by simp only [ho, raw, sub_add_cancel]

/-- The low key of a stretch of a segment, without its accumulator. X: the array of the high digits;
Qf: what the quotient is worth. -/
theorem Fits.siteS (X : Arr) (hX : readLong X = true) {ew wh : Array E} {n : ℕ}
    (hw : Wts ρ ew wh v.y.ls low n) {lam a0 b0 m k form : ℕ} (hb : b0 = a0 + m)
    (hn : b0 ≤ n) (ha : ∃ q, a0 = q * 2 ^ v.y.ls) (hm : ∃ q, m = q * 2 ^ v.y.ls)
    (hf : (form == 0) = false) (ho : ρ.val (Env.oOf form) = ((X.off : ℤ) : K))
    {SQ : Aff} {Qf : ℕ → ℕ → K}
    (hQ : SQ.value ρ W = wsum (fun y => wt ρ ew (a0 + y)) D.lT u m Qf) {f : Aff}
    (h : Env.site (sumR ew a0 b0) SQ k form (fun _ => v.SBA wh a0 b0 (arrName X) lam "Z" 0) =
      some f) :
    f.value ρ W = wsum (fun y => wt ρ ew (a0 + y)) D.lT u m
      (fun y i => ssite 0 (Qf y i) (val t X lam (a0 + y) i) k) := by
  subst hb
  rw [site_wsum F.num hf (sumR_stretch ew a0 m (by rw [hw.size]; exact hn)) hQ
    (fun S hS => F.SBA X hX hw ha hm ⟨0, (Nat.zero_mul _).symm⟩ (Nat.zero_le _) hS) h]
  exact wsum_congr _ _ _ _ fun y _ i => by simp only [ho, raw, sub_add_cancel, Nat.sub_zero]

/-- The low key of a whole segment, without its accumulator. -/
theorem Fits.siteW (X : Arr) (hX : readLong X = true) {ew wh : Array E} {n : ℕ}
    (hw : Wts ρ ew wh v.y.ls low n) {lam k form : ℕ}
    (hf : (form == 0) = false) (ho : ρ.val (Env.oOf form) = ((X.off : ℤ) : K))
    {SQ : Aff} {Qf : ℕ → ℕ → K} (hQ : SQ.value ρ W = wsum (wt ρ ew) D.lT u n Qf) {f : Aff}
    (h : Env.site (sumE ew) SQ k form (fun _ => v.SA wh (arrName X) lam "Z") = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u n (fun x i => ssite 0 (Qf x i) (val t X lam x i) k) := by
  rw [site_wsum F.num hf hw.sumE hQ (fun S hS => F.SA X hX hw hS) h]
  exact wsum_congr _ _ _ _ fun y _ i => by simp only [ho, raw, sub_add_cancel]

/-- The quotient of the gate's rounding over a stretch: the library's gw = g0 + 256 gh. -/
theorem Fits.gate {ew wh : Array E} {n : ℕ} (hw : Wts ρ ew wh v.y.ls low n) {lam a0 b0 m : ℕ}
    (hb : b0 = a0 + m) (ha : ∃ q, a0 = q * 2 ^ v.y.ls) (hm : ∃ q, m = q * 2 ^ v.y.ls) {q : Aff}
    (h : gateQ v lam wh a0 b0 = some q) :
    q.value ρ W = wsum (fun y => wt ρ ew (a0 + y)) D.lT u m (fun y i => gw t lam (a0 + y) i) := by
  unfold gateQ at h
  rw [F.gcl, if_neg (show ¬ (!true) = true by decide)] at h
  obtain ⟨x, hx, h⟩ := bind_some h
  obtain ⟨y, hy, h⟩ := bind_some h
  cases h
  have e : ∀ z, z < m → ∀ i, gw t lam (a0 + z) i =
      val t .g0 lam (a0 + z) i + (256 : K) * val t .gh lam (a0 + z) i := fun _ _ _ => rfl
  rw [wsum_congr _ _ _ _ e, wsum_add, wsum_smul, Aff.value_add, Aff.value_scale, F.num.ofNat,
    F.stretch .g0 rfl rfl hw hb ha hm hx, F.stretch .gh rfl rfl hw hb ha hm hy]
  norm_num

/-! ## What the forms are worth -/

/-- GH: the high digit of the rounding that gives the gate. On an odd layer the segment has two
stretches, each with its own shift. -/
theorem Fits.line_GH (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff}
    (h : v.line "GH" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .GH) (fun x i => key D t tb L0 w .GH lam x i) := by
  have hff := F.ffe
  rw [line_GH_eq, F.isMoe, F.f, F.fe, F.hgD, F.kg lam hlam] at h
  show _ = wsum (wt ρ ew) D.lT u D.f _
  by_cases hodd : lam % 2 = 1
  · rw [isExpL_odd hodd, if_neg (show ¬ (!true) = true by decide), F.kgR lam hlam hodd] at h
    obtain ⟨A, h1, h⟩ := bind_some h
    obtain ⟨B, h2, h⟩ := bind_some h
    cases h
    have E1 := F.highS .rg rfl hw (D.Pl lam).kg (top := 24) (Nat.zero_add D.fe).symm (by omega)
      ⟨0, (Nat.zero_mul _).symm⟩ F.bfe rfl (F.off1 .rg rfl) h1
    have E2 := F.highS .rg rfl hw (D.Pl lam).kg' (top := 24) hff (Nat.le_refl _) F.bfe F.bfe rfl
      (F.off1 .rg rfl) h2
    simp only [Nat.zero_add] at E1
    rw [Aff.value_add, E1, E2, hff, wsum_split]
    refine congrArg₂ (· + ·) (wsum_congr _ _ _ _ fun x hx i => ?_)
      (wsum_congr _ _ _ _ fun y _ i => ?_)
    · show _ = shigh (val t .rg lam x i) (kG D lam x) 24
      rw [kG_shared D (routed_low D lam hx)]
    · show _ = shigh (val t .rg lam (D.fe + y) i) (kG D lam (D.fe + y)) 24
      rw [kG_routed D (routed_high D hodd y)]
  · rw [isExpL_even hodd, if_pos (show (!false) = true by decide)] at h
    obtain ⟨A, h1, h⟩ := bind_some h
    cases h
    rw [F.highW .rg rfl hw (D.Pl lam).kg (top := 24) rfl (F.off1 .rg rfl) h1]
    refine wsum_congr _ _ _ _ fun x _ i => ?_
    show _ = shigh (val t .rg lam x i) (kG D lam x) 24
    rw [kG_shared D (routed_even D hodd x)]

/-- UH: the high digit of the rounding that gives the up projection. On an odd layer the segment has
two stretches, each with its own shift. -/
theorem Fits.line_UH (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff}
    (h : v.line "UH" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .UH) (fun x i => key D t tb L0 w .UH lam x i) := by
  have hff := F.ffe
  rw [line_UH_eq, F.isMoe, F.f, F.fe, F.huD, F.ku lam hlam] at h
  show _ = wsum (wt ρ ew) D.lT u D.f _
  by_cases hodd : lam % 2 = 1
  · rw [isExpL_odd hodd, if_neg (show ¬ (!true) = true by decide), F.kuR lam hlam hodd] at h
    obtain ⟨A, h1, h⟩ := bind_some h
    obtain ⟨B, h2, h⟩ := bind_some h
    cases h
    have E1 := F.highS .ru rfl hw (D.Pl lam).ku (top := 24) (Nat.zero_add D.fe).symm (by omega)
      ⟨0, (Nat.zero_mul _).symm⟩ F.bfe rfl (F.off1 .ru rfl) h1
    have E2 := F.highS .ru rfl hw (D.Pl lam).ku' (top := 24) hff (Nat.le_refl _) F.bfe F.bfe rfl
      (F.off1 .ru rfl) h2
    simp only [Nat.zero_add] at E1
    rw [Aff.value_add, E1, E2, hff, wsum_split]
    refine congrArg₂ (· + ·) (wsum_congr _ _ _ _ fun x hx i => ?_)
      (wsum_congr _ _ _ _ fun y _ i => ?_)
    · show _ = shigh (val t .ru lam x i) (kU D lam x) 24
      rw [kU_shared D (routed_low D lam hx)]
    · show _ = shigh (val t .ru lam (D.fe + y) i) (kU D lam (D.fe + y)) 24
      rw [kU_routed D (routed_high D hodd y)]
  · rw [isExpL_even hodd, if_pos (show (!false) = true by decide)] at h
    obtain ⟨A, h1, h⟩ := bind_some h
    cases h
    rw [F.highW .ru rfl hw (D.Pl lam).ku (top := 24) rfl (F.off1 .ru rfl) h1]
    refine wsum_congr _ _ _ _ fun x _ i => ?_
    show _ = shigh (val t .ru lam x i) (kU D lam x) 24
    rw [kU_shared D (routed_even D hodd x)]

/-- D: the rounding that adds the hidden units' output to the stream; the affine part of the key. -/
theorem Fits.line_D (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff}
    (h : v.line "D" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .D) (fun x i => lin D t tb L0 w .D lam x i) := by
  rw [line_D_eq, F.hdD, F.kd lam hlam] at h
  obtain ⟨A, h1, h⟩ := bind_some h
  obtain ⟨B, h2, h⟩ := bind_some h
  have hQ : (A - B).value ρ W = wsum (wt ρ ew) D.lT u D.d
      (fun x i => xS D t (2 * lam + 2) x i - xS D t (2 * lam + 1) x i) := by
    rw [wsum_sub, Aff.value_sub, F.Sxs hw h1, F.Sxs hw h2]
  exact F.siteW .rd rfl hw rfl (F.off1 .rd rfl) hQ h

/-- QK: the roundings that give queries and keys; the affine part of the key. One segment in two
stretches, each with its own shift. -/
theorem Fits.line_QK (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.dqk) {f : Aff}
    (h : v.line "QK" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .QK) (fun x i => lin D t tb L0 w .QK lam x i) := by
  have hsum : D.dqk = D.dq + D.dkv := rfl
  have z0 : ∃ q, 0 = q * 2 ^ v.y.ls := ⟨0, (Nat.zero_mul _).symm⟩
  rw [line_QK_eq, F.dq, F.nqk, F.hq, F.kq lam hlam, F.kk lam hlam] at h
  show _ = wsum (wt ρ ew) D.lT u D.dqk _
  obtain ⟨P, hP, h⟩ := bind_some h
  obtain ⟨Q, hQ, h⟩ := bind_some h
  cases h
  obtain ⟨A, h1, hP⟩ := bind_some hP
  obtain ⟨B, h2, hQ⟩ := bind_some hQ
  have E1 := F.siteS .rqk rfl hw (Nat.zero_add D.dq).symm (by omega) z0 F.bdq rfl (F.off2 .rqk rfl)
    (F.stretch .qkw rfl rfl hw (Nat.zero_add D.dq).symm z0 F.bdq h1) hP
  have E2 := F.siteS .rqk rfl hw hsum (Nat.le_refl _) F.bdq F.bdkv rfl (F.off2 .rqk rfl)
    (F.stretch .qkw rfl rfl hw hsum F.bdq F.bdkv h2) hQ
  simp only [Nat.zero_add] at E1
  rw [Aff.value_add, E1, E2, hsum, wsum_split]
  refine congrArg₂ (· + ·) (wsum_congr _ _ _ _ fun x hx i => ?_)
    (wsum_congr _ _ _ _ fun y _ i => ?_)
  · show _ = ssite 0 (val t .qkw lam x i) (val t .rqk lam x i) (kQK D lam x)
    rw [show kQK D lam x = (D.Pl lam).kq from if_pos hx]
  · show _ = ssite 0 (val t .qkw lam (D.dq + y) i) (val t .rqk lam (D.dq + y) i)
      (kQK D lam (D.dq + y))
    rw [show kQK D lam (D.dq + y) = (D.Pl lam).kk from if_neg (by omega)]

/-- G: the rounding that gives the gate; the affine part of the key. On an odd layer the segment
has two stretches, each with its own shift. -/
theorem Fits.line_G (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff}
    (h : v.line "G" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .G) (fun x i => lin D t tb L0 w .G lam x i) := by
  have hff := F.ffe
  have z0 : ∃ q, 0 = q * 2 ^ v.y.ls := ⟨0, (Nat.zero_mul _).symm⟩
  rw [line_G_eq, F.isMoe, F.f, F.fe, F.hgD, F.kg lam hlam] at h
  show _ = wsum (wt ρ ew) D.lT u D.f _
  by_cases hodd : lam % 2 = 1
  · rw [isExpL_odd hodd, if_neg (show ¬ (!true) = true by decide), F.kgR lam hlam hodd] at h
    obtain ⟨P, hP, h⟩ := bind_some h
    obtain ⟨A, hA, h⟩ := bind_some h
    obtain ⟨Q, hQ, h⟩ := bind_some h
    obtain ⟨B, hB, h⟩ := bind_some h
    cases h
    have E1 := F.siteS .rg rfl hw (Nat.zero_add D.fe).symm (by omega) z0 F.bfe rfl
      (F.off1 .rg rfl) (F.gate hw (Nat.zero_add D.fe).symm z0 F.bfe hP) hA
    have E2 := F.siteS .rg rfl hw hff (Nat.le_refl _) F.bfe F.bfe rfl
      (F.off1 .rg rfl) (F.gate hw hff F.bfe F.bfe hQ) hB
    simp only [Nat.zero_add] at E1
    rw [Aff.value_add, E1, E2, hff, wsum_split]
    refine congrArg₂ (· + ·) (wsum_congr _ _ _ _ fun x hx i => ?_)
      (wsum_congr _ _ _ _ fun y _ i => ?_)
    · show _ = ssite 0 (gw t lam x i) (val t .rg lam x i) (kG D lam x)
      rw [kG_shared D (routed_low D lam hx)]
    · show _ = ssite 0 (gw t lam (D.fe + y) i) (val t .rg lam (D.fe + y) i)
        (kG D lam (D.fe + y))
      rw [kG_routed D (routed_high D hodd y)]
  · rw [isExpL_even hodd, if_pos (show (!false) = true by decide)] at h
    obtain ⟨Q, hQ, h⟩ := bind_some h
    have EQ := F.gate hw (Nat.zero_add D.f).symm z0 F.bf hQ
    simp only [Nat.zero_add] at EQ
    rw [F.siteW .rg rfl hw rfl (F.off1 .rg rfl) EQ h]
    refine wsum_congr _ _ _ _ fun x _ i => ?_
    show _ = ssite 0 (gw t lam x i) (val t .rg lam x i) (kG D lam x)
    rw [kG_shared D (routed_even D hodd x)]

/-- U: the rounding that gives the up projection; the affine part of the key. On an odd layer the
segment has two stretches, each with its own shift. -/
theorem Fits.line_U (lam : ℕ) (hlam : lam < D.nl) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff}
    (h : v.line "U" lam ew wh = some f) :
    f.value ρ W = wsum (wt ρ ew) D.lT u (len D .U) (fun x i => lin D t tb L0 w .U lam x i) := by
  have hff := F.ffe
  have z0 : ∃ q, 0 = q * 2 ^ v.y.ls := ⟨0, (Nat.zero_mul _).symm⟩
  rw [line_U_eq, F.isMoe, F.f, F.fe, F.huD, F.ku lam hlam] at h
  show _ = wsum (wt ρ ew) D.lT u D.f _
  by_cases hodd : lam % 2 = 1
  · rw [isExpL_odd hodd, if_neg (show ¬ (!true) = true by decide), F.kuR lam hlam hodd] at h
    obtain ⟨P, hP, h⟩ := bind_some h
    obtain ⟨A, hA, h⟩ := bind_some h
    obtain ⟨Q, hQ, h⟩ := bind_some h
    obtain ⟨B, hB, h⟩ := bind_some h
    cases h
    have E1 := F.siteS .ru rfl hw (Nat.zero_add D.fe).symm (by omega) z0 F.bfe rfl
      (F.off1 .ru rfl) (F.stretch .up rfl rfl hw (Nat.zero_add D.fe).symm z0 F.bfe hP) hA
    have E2 := F.siteS .ru rfl hw hff (Nat.le_refl _) F.bfe F.bfe rfl
      (F.off1 .ru rfl) (F.stretch .up rfl rfl hw hff F.bfe F.bfe hQ) hB
    simp only [Nat.zero_add] at E1
    rw [Aff.value_add, E1, E2, hff, wsum_split]
    refine congrArg₂ (· + ·) (wsum_congr _ _ _ _ fun x hx i => ?_)
      (wsum_congr _ _ _ _ fun y _ i => ?_)
    · show _ = ssite 0 (val t .up lam x i) (val t .ru lam x i) (kU D lam x)
      rw [kU_shared D (routed_low D lam hx)]
    · show _ = ssite 0 (val t .up lam (D.fe + y) i) (val t .ru lam (D.fe + y) i)
        (kU D lam (D.fe + y))
      rw [kU_routed D (routed_high D hodd y)]
  · rw [isExpL_even hodd, if_pos (show (!false) = true by decide)] at h
    obtain ⟨Q, hQ, h⟩ := bind_some h
    have EQ := F.stretch .up rfl rfl hw (Nat.zero_add D.f).symm z0 F.bf hQ
    simp only [Nat.zero_add] at EQ
    rw [F.siteW .ru rfl hw rfl (F.off1 .ru rfl) EQ h]
    refine wsum_congr _ _ _ _ fun x _ i => ?_
    show _ = ssite 0 (val t .up lam x i) (val t .ru lam x i) (kU D lam x)
    rw [kU_shared D (routed_even D hodd x)]

end Families

#print axioms Fits.line_GH
#print axioms Fits.line_UH
#print axioms Fits.line_D
#print axioms Fits.line_QK
#print axioms Fits.line_G
#print axioms Fits.line_U

end OnBytes.Road
