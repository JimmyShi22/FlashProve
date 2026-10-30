-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgLin.lean: the affine part of the library's key, beside G.lean's affG.
G.lean is OnBytes/Tie/Pv/Lookup/Ends/G.lean: a file of terms written for these files over the
verifier's records; no function of the verifier returns them.
States: (TiesG.lin_affG) FOR ALL 34 FAMILIES: the affine part of the library's key (lin,
Inst/Model/FF/Objects.lean) IS G.lean's affG at the segment of that name, at every layer of the
group on which the family is present, every entry and every token.
(alg_line) WHAT A SEGMENT's FORM IS WORTH, OVER G.lean's TERMS: under the record Fits (every read
that the forms name has its rule value at this world; and public numbers) and TiesG: the form that
the verifier's Env.line returns for the segment is worth the sum over its entries x of the weight of
x times the extension over the tokens of affG at x.
Under TiesG: the library's value of an array that an affine part reads is G.lean's tensor of that
name plus the array's offset; the library's stream is G.lean's xs; eleven switches; three sizes; the
shifts on the group's layers; both norms' shifts from 16 on. AlgTies.lean draws TiesG from Fits.
Does not say: anything on the products in the keys; that a run's reads have their rule values.
-/
import Johnson.Road.FormsKeysAll
import OnBytes.Tie.Pv.Lookup.Ends.G

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open Finset
open OnBytes.Ends
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key lin len present val xS gw lw led kG kU kQK)

section Tools

variable {K : Type} [Field K]

/-- G.lean's sum over the numbers below n. -/
theorem sumN_eq (f : ℕ → K) : ∀ n : ℕ, G.sumN n f = ∑ k ∈ range n, f k
  | 0 => by simp [G.sumN]
  | n + 1 => by
    unfold G.sumN
    rw [List.range_succ, List.foldl_append, sum_range_succ, ← sumN_eq f n]
    rfl

/-- A sum over the numbers below n that lie above x. -/
theorem sum_above (f : ℕ → K) (n x : ℕ) :
    ∑ e ∈ (range n).filter (x < ·), f e = ∑ k ∈ range (n - (x + 1)), f (x + 1 + k) := by
  have h : (range n).filter (x < ·) = Ico (x + 1) n := by
    ext e
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [h, sum_Ico_eq_sum_range]

/-- G.lean's low key without its accumulator, digit form 1, is the library's. -/
theorem site_one (q r : K) (k : ℕ) :
    G.site 0 q k 1 r = Inst.Model.Site.ssite 0 q (r + 128) k := by
  have e0 : ((1 : ℕ) == 0) = false := rfl
  have e1 : ((1 : ℕ) == 1) = true := rfl
  rw [Inst.Model.Site.ssite_eq]
  unfold G.site G.oOf Inst.Model.Site.dn
  rw [e0, e1, if_neg Bool.false_ne_true, if_pos rfl]
  ring

/-- The same at digit form 2. -/
theorem site_two (q r : K) (k : ℕ) :
    G.site 0 q k 2 r = Inst.Model.Site.ssite 0 q (r + 32896) k := by
  have e0 : ((2 : ℕ) == 0) = false := rfl
  have e1 : ((2 : ℕ) == 1) = false := rfl
  rw [Inst.Model.Site.ssite_eq]
  unfold G.site G.oOf Inst.Model.Site.dn
  rw [e0, e1, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  ring

/-- G.lean's high key, digit form 1, is the library's. -/
theorem high_one (r : K) (k : ℕ) : G.high r k 1 = Inst.Model.Site.shigh (r + 128) k 24 := by
  have e1 : ((1 : ℕ) == 1) = true := rfl
  rw [Inst.Model.Site.shigh_eq]
  unfold G.high G.oOf Inst.Model.Site.up
  rw [e1, if_pos rfl, if_pos rfl]
  ring

/-- The same at digit form 2. -/
theorem high_two (r : K) (k : ℕ) : G.high r k 2 = Inst.Model.Site.shigh (r + 32896) k 32 := by
  have e1 : ((2 : ℕ) == 1) = false := rfl
  rw [Inst.Model.Site.shigh_eq]
  unfold G.high G.oOf Inst.Model.Site.up
  rw [e1, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  ring

/-- The multiplier of a digit of a row: the library's is the verifier's. -/
theorem mu_eq (n : ℕ) : ((Inst.Model.Ledger.mu n : ℤ) : K) = ((Model.ledMu5 n : ℕ) : K) := by
  unfold Inst.Model.Ledger.mu Model.ledMu5
  simp only [beq_iff_eq]
  split_ifs <;> simp

end Tools

/-- True for the arrays that an affine part reads as a tensor of the verifier's: all but the
attention output o and the two arrays at the borders of the stream, which are no tensors of the
verifier's. -/
def readsG : Arr → Bool
  | .o | .x0 | .x8 => false
  | _ => true

section Ties

variable {K : Type} [Field K] [scl : Scl]

/-- **What ties G.lean's terms to the library's.** -/
structure TiesG (P : Model.Layer.Pub) (g : ℕ) (cell : G.NameG → K) (D : Dim) (t : Cell → K) :
    Prop where
  /-- the library's value of an array is the tensor of its name, plus the array's offset -/
  val : ∀ X : Arr, readsG X = true → ∀ inst j i : ℕ,
    val t X inst j i = G.ten P cell (arrName X) inst j i + ((X.off : ℤ) : K)
  /-- the stream -/
  xs : ∀ s j i : ℕ, s ≤ 2 * D.nl → xS D t s j i = G.xs P cell s j i
  /-- the odd layers have routed experts -/
  p3 : P.y.h.p3 = true
  /-- the gate's clamp is on -/
  gcl : P.y.h.gcl = true
  /-- the router's clamp is on -/
  rcl : P.y.h.rcl = true
  /-- a value of the stream has five limbs -/
  xl : P.y.h.xl = 5
  /-- the digit forms -/
  hq : P.y.h.hq = 2
  /-- see hq -/
  hv : P.y.h.hv = 1
  /-- see hq -/
  ho : P.y.h.ho = 1
  /-- see hq -/
  hgD : P.y.h.hgD = 1
  /-- see hq -/
  huD : P.y.h.huD = 1
  /-- see hq -/
  hdD : P.y.h.hdD = 1
  /-- see hq -/
  hr : P.y.h.hr = 1
  /-- the hidden units of one expert -/
  fe : P.y.h.fe = D.fe
  /-- the experts -/
  NE : P.y.h.NE = D.nx
  /-- the width of the queries -/
  dq : P.y.dq = D.dq
  /-- the shifts, on the layers of the group -/
  kq : ∀ lam, lam < D.nl → P.sc.kl (g * P.y.Lam + lam) Model.Layer.Lkq = (D.Pl lam).kq
  /-- see kq -/
  kk : ∀ lam, lam < D.nl → P.sc.kl (g * P.y.Lam + lam) Model.Layer.Lkk = (D.Pl lam).kk
  /-- see kq -/
  kv : ∀ lam, lam < D.nl → P.sc.kl (g * P.y.Lam + lam) Model.Layer.Lkv = (D.Pl lam).kv
  /-- see kq -/
  ko : ∀ lam, lam < D.nl → P.sc.kl (g * P.y.Lam + lam) Model.Layer.Lko = (D.Pl lam).ko
  /-- see kq -/
  kg : ∀ lam, lam < D.nl → P.sc.kl (g * P.y.Lam + lam) Model.Layer.Lkg = (D.Pl lam).kg
  /-- see kq -/
  ku : ∀ lam, lam < D.nl → P.sc.kl (g * P.y.Lam + lam) Model.Layer.Lku = (D.Pl lam).ku
  /-- see kq -/
  kd : ∀ lam, lam < D.nl → P.sc.kl (g * P.y.Lam + lam) Model.Layer.Lkd = (D.Pl lam).kd
  /-- see kq -/
  K1 : ∀ lam, lam < D.nl → P.sc.kl (g * P.y.Lam + lam) Model.Layer.LK1 = (D.Pl lam).n1.K
  /-- see kq -/
  K2 : ∀ lam, lam < D.nl → P.sc.kl (g * P.y.Lam + lam) Model.Layer.LK2 = (D.Pl lam).n2.K
  /-- the router's shift, on a layer with experts -/
  kr : ∀ lam, lam < D.nl → lam % 2 = 1 → P.sc.klM (g * P.y.Lam + lam) 0 = (D.Pl lam).kr
  /-- the routed expert's gate's -/
  kgR : ∀ lam, lam < D.nl → lam % 2 = 1 → P.sc.klM (g * P.y.Lam + lam) 1 = (D.Pl lam).kg'
  /-- the routed expert's up product's -/
  kuR : ∀ lam, lam < D.nl → lam % 2 = 1 → P.sc.klM (g * P.y.Lam + lam) 2 = (D.Pl lam).ku'
  /-- both norms' shifts are at least 16 -/
  K1le : ∀ lam, lam < D.nl → 16 ≤ (D.Pl lam).n1.K
  /-- see K1le -/
  K2le : ∀ lam, lam < D.nl → 16 ≤ (D.Pl lam).n2.K

variable {P : Model.Layer.Pub} {g : ℕ} {cell : G.NameG → K} {D : Dim} {t : Cell → K}

/-- Which entries belong to the routed expert. -/
theorem TiesG.routed_eq (T : TiesG P g cell D t) (lam x : ℕ) :
    G.routed P lam x = Inst.Model.FFSeg.routed D lam x := by
  unfold G.routed G.moe Inst.Model.FFSeg.routed Inst.Model.FFSeg.isExpL
  rw [T.p3, T.fe, Bool.true_and]

omit scl in
/-- An entry of the routed expert stands on an odd layer. -/
theorem odd_of_routed {D : Dim} {lam x : ℕ} (h : Inst.Model.FFSeg.routed D lam x = true) :
    lam % 2 = 1 := by
  simp [Inst.Model.FFSeg.routed, Inst.Model.FFSeg.isExpL] at h
  exact h.1

/-- The gate's shift. -/
theorem TiesG.kGU_false (T : TiesG P g cell D t) {lam x : ℕ} (hlam : lam < D.nl) :
    G.kGU P g false lam x = kG D lam x := by
  unfold G.kGU Inst.Model.FFSeg.kG
  rw [T.routed_eq]
  cases h : Inst.Model.FFSeg.routed D lam x with
  | false => exact T.kg lam hlam
  | true => exact T.kgR lam hlam (odd_of_routed h)

/-- The up product's shift. -/
theorem TiesG.kGU_true (T : TiesG P g cell D t) {lam x : ℕ} (hlam : lam < D.nl) :
    G.kGU P g true lam x = kU D lam x := by
  unfold G.kGU Inst.Model.FFSeg.kU
  rw [T.routed_eq]
  cases h : Inst.Model.FFSeg.routed D lam x with
  | false => exact T.ku lam hlam
  | true => exact T.kuR lam hlam (odd_of_routed h)

/-- The shift of queries and keys. -/
theorem TiesG.kQK_eq (T : TiesG P g cell D t) {lam x : ℕ} (hlam : lam < D.nl) :
    G.kQK P g lam x = kQK D lam x := by
  unfold G.kQK Inst.Model.FFSeg.kQK
  rw [T.dq]
  split_ifs
  · exact T.kq lam hlam
  · exact T.kk lam hlam

/-- The gate's quotient. -/
theorem TiesG.gQ_eq (T : TiesG P g cell D t) (lam x i : ℕ) :
    G.gQ P cell lam x i = G.ten P cell "g0" lam x i + 256 * G.ten P cell "gh" lam x i := by
  unfold G.gQ
  rw [T.gcl, if_pos rfl]

/-- **The affine part of the library's key is G.lean's affG: all 34 families.** -/
theorem TiesG.lin_affG (T : TiesG P g cell D t) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (s : Fam)
    (lam x i : ℕ) (hlam : lam < D.nl) (hp : present s lam = true) :
    lin D t tb L0 w s lam x i = G.affG P g cell (segName s) lam x i := by
  cases s
  case G =>
    have hR : G.affG P g cell "G" lam x i =
        G.site 0 (G.gQ P cell lam x i) (G.kGU P g false lam x) P.y.h.hgD (G.ten P cell "rg" lam x
          i) := rfl
    show lin D t tb L0 w .G lam x i = G.affG P g cell "G" lam x i
    rw [hR]
    rw [T.hgD, site_one, T.kGU_false hlam, T.gQ_eq]
    simp only [lin, gw, T.val .g0 rfl, T.val .gh rfl, T.val .rg rfl, arrName, Arr.off]
    push_cast
    ring_nf
  case U =>
    have hR : G.affG P g cell "U" lam x i =
        G.site 0 (G.ten P cell "u" lam x i) (G.kGU P g true lam x) P.y.h.huD (G.ten P cell "ru" lam
          x i) := rfl
    show lin D t tb L0 w .U lam x i = G.affG P g cell "U" lam x i
    rw [hR]
    rw [T.huD, site_one, T.kGU_true hlam]
    simp only [lin, T.val .up rfl, T.val .ru rfl, arrName, Arr.off]
    push_cast
    ring_nf
  case UT =>
    have hR : G.affG P g cell "UT" lam x i =
        G.ten P cell "u" lam x i + 2 ^ 15 := rfl
    show lin D t tb L0 w .UT lam x i = G.affG P g cell "UT" lam x i
    rw [hR]
    simp only [lin, key, T.val .up rfl, arrName, Arr.off]
    push_cast
    ring
  case QK =>
    have hR : G.affG P g cell "QK" lam x i =
        G.site 0 (G.ten P cell "qkw" lam x i) (G.kQK P g lam x) P.y.h.hq (G.ten P cell "rqk" lam x
          i) := rfl
    show lin D t tb L0 w .QK lam x i = G.affG P g cell "QK" lam x i
    rw [hR]
    rw [T.hq, site_two, T.kQK_eq hlam]
    simp only [lin, T.val .qkw rfl, T.val .rqk rfl, arrName, Arr.off]
    push_cast
    ring_nf
  case N1 =>
    have hR : G.affG P g cell "N1" lam x i =
        G.site 0 (G.ten P cell "aw" lam x i) (G.kL P g lam Model.Layer.LK1) 2 (G.ten P cell "ra"
          lam x i) := rfl
    show lin D t tb L0 w .N1 lam x i = G.affG P g cell "N1" lam x i
    rw [hR]
    rw [site_two, show G.kL P g lam Model.Layer.LK1 = (D.Pl lam).n1.K from T.K1 lam hlam,
      Inst.Model.Site.ssite_of_le (T.K1le lam hlam)]
    simp only [lin, T.val .aw rfl, T.val .ra rfl, arrName, Arr.off]
    push_cast
    ring_nf
  case N2 =>
    have hR : G.affG P g cell "N2" lam x i =
        G.site 0 (G.ten P cell "mw" lam x i) (G.kL P g lam Model.Layer.LK2) 2 (G.ten P cell "rm"
          lam x i) := rfl
    show lin D t tb L0 w .N2 lam x i = G.affG P g cell "N2" lam x i
    rw [hR]
    rw [site_two, show G.kL P g lam Model.Layer.LK2 = (D.Pl lam).n2.K from T.K2 lam hlam,
      Inst.Model.Site.ssite_of_le (T.K2le lam hlam)]
    simp only [lin, T.val .mw rfl, T.val .rm rfl, arrName, Arr.off]
    push_cast
    ring_nf
  case O =>
    have hR : G.affG P g cell "O" lam x i =
        G.site 0 (G.xs P cell (2 * lam + 1) x i - G.xs P cell (2 * lam) x i)
        (G.kL P g lam Model.Layer.Lko) P.y.h.ho (G.ten P cell "ro" lam x i) := rfl
    show lin D t tb L0 w .O lam x i = G.affG P g cell "O" lam x i
    rw [hR]
    rw [T.ho, site_one, show G.kL P g lam Model.Layer.Lko = (D.Pl lam).ko from T.ko lam hlam]
    simp only [lin, T.val .ro rfl, T.xs _ x i (show 2 * lam + 1 ≤ 2 * D.nl by omega),
      T.xs _ x i (show 2 * lam ≤ 2 * D.nl by omega), arrName, Arr.off]
    push_cast
    ring
  case D =>
    have hR : G.affG P g cell "D" lam x i =
        G.site 0 (G.xs P cell (2 * lam + 2) x i - G.xs P cell (2 * lam + 1) x i)
        (G.kL P g lam Model.Layer.Lkd) P.y.h.hdD (G.ten P cell "rd" lam x i) := rfl
    show lin D t tb L0 w .D lam x i = G.affG P g cell "D" lam x i
    rw [hR]
    rw [T.hdD, site_one, show G.kL P g lam Model.Layer.Lkd = (D.Pl lam).kd from T.kd lam hlam]
    simp only [lin, T.val .rd rfl, T.xs _ x i (show 2 * lam + 2 ≤ 2 * D.nl by omega),
      T.xs _ x i (show 2 * lam + 1 ≤ 2 * D.nl by omega), arrName, Arr.off]
    push_cast
    ring
  case V =>
    have hR : G.affG P g cell "V" lam x i =
        G.site 0 (G.ten P cell "vw" lam x i) (G.kL P g lam Model.Layer.Lkv) P.y.h.hv (G.ten P cell
          "rv" lam x i) := rfl
    show lin D t tb L0 w .V lam x i = G.affG P g cell "V" lam x i
    rw [hR]
    rw [T.hv, site_one, show G.kL P g lam Model.Layer.Lkv = (D.Pl lam).kv from T.kv lam hlam]
    simp only [lin, T.val .vw rfl, T.val .rv rfl, arrName, Arr.off]
    push_cast
    ring_nf
  case LR =>
    have hR : G.affG P g cell "LR" lam x i =
        G.site 0 (if P.y.h.rcl then 8 * G.ten P cell "ly" (lam / 2) x i + G.ten P cell "l3" (lam /
          2) x i
        else G.ten P cell "lr" (lam / 2) x i) (G.kR P g lam) P.y.h.hr (G.ten P cell "rl" (lam / 2)
          x i) := rfl
    show lin D t tb L0 w .LR lam x i = G.affG P g cell "LR" lam x i
    rw [hR]
    rw [T.hr, site_one, T.rcl, if_pos rfl,
      show G.kR P g lam = (D.Pl lam).kr from T.kr lam hlam (odd_of_present rfl hp)]
    simp only [lin, lw, T.val .ly rfl, T.val .l3 rfl, T.val .rl rfl, arrName, Arr.off]
    push_cast
    ring_nf
  case XR =>
    have hR : G.affG P g cell "XR" lam x i =
        2 ^ 15 - 2 ^ 16 * G.ten P cell "xr" (lam / 2) x i := rfl
    show lin D t tb L0 w .XR lam x i = G.affG P g cell "XR" lam x i
    rw [hR]
    simp only [lin, T.val .xr rfl, arrName, Arr.off]
    push_cast
    ring
  case LT =>
    have hR : G.affG P g cell "LT" lam x i =
        2 * (G.ten P cell "lr" (lam / 2) x i + 2 ^ 14) := rfl
    show lin D t tb L0 w .LT lam x i = G.affG P g cell "LT" lam x i
    rw [hR]
    simp only [lin, key, T.val .lr rfl, arrName, Arr.off]
    push_cast
    ring
  case DD =>
    have hR : G.affG P g cell "DD" lam x i =
        -G.ten P cell "lr" (lam / 2) x i -
        G.sumN (P.y.h.NE - (x + 1)) fun k => G.ten P cell "sel" (lam / 2) (x + 1 + k) i := rfl
    show lin D t tb L0 w .DD lam x i = G.affG P g cell "DD" lam x i
    rw [hR]
    rw [sumN_eq, T.NE]
    simp only [lin, T.val .lr rfl, T.val .sel rfl, arrName, Arr.off, sum_above]
    push_cast
    ring_nf
  case GH =>
    have hR : G.affG P g cell "GH" lam x i =
        G.high (G.ten P cell "rg" lam x i) (G.kGU P g false lam x) P.y.h.hgD := rfl
    show lin D t tb L0 w .GH lam x i = G.affG P g cell "GH" lam x i
    rw [hR]
    rw [T.hgD, high_one, T.kGU_false hlam]
    simp only [lin, key, T.val .rg rfl, arrName, Arr.off]
    push_cast
    ring
  case UH =>
    have hR : G.affG P g cell "UH" lam x i =
        G.high (G.ten P cell "ru" lam x i) (G.kGU P g true lam x) P.y.h.huD := rfl
    show lin D t tb L0 w .UH lam x i = G.affG P g cell "UH" lam x i
    rw [hR]
    rw [T.huD, high_one, T.kGU_true hlam]
    simp only [lin, key, T.val .ru rfl, arrName, Arr.off]
    push_cast
    ring
  case OH =>
    have hR : G.affG P g cell "OH" lam x i =
        G.high (G.ten P cell "ro" lam x i) (G.kL P g lam Model.Layer.Lko) P.y.h.ho := rfl
    show lin D t tb L0 w .OH lam x i = G.affG P g cell "OH" lam x i
    rw [hR]
    rw [T.ho, high_one, show G.kL P g lam Model.Layer.Lko = (D.Pl lam).ko from T.ko lam hlam]
    simp only [lin, key, T.val .ro rfl, arrName, Arr.off]
    push_cast
    ring
  case DH =>
    have hR : G.affG P g cell "DH" lam x i =
        G.high (G.ten P cell "rd" lam x i) (G.kL P g lam Model.Layer.Lkd) P.y.h.hdD := rfl
    show lin D t tb L0 w .DH lam x i = G.affG P g cell "DH" lam x i
    rw [hR]
    rw [T.hdD, high_one, show G.kL P g lam Model.Layer.Lkd = (D.Pl lam).kd from T.kd lam hlam]
    simp only [lin, key, T.val .rd rfl, arrName, Arr.off]
    push_cast
    ring
  case VH =>
    have hR : G.affG P g cell "VH" lam x i =
        G.high (G.ten P cell "rv" lam x i) (G.kL P g lam Model.Layer.Lkv) P.y.h.hv := rfl
    show lin D t tb L0 w .VH lam x i = G.affG P g cell "VH" lam x i
    rw [hR]
    rw [T.hv, high_one, show G.kL P g lam Model.Layer.Lkv = (D.Pl lam).kv from T.kv lam hlam]
    simp only [lin, key, T.val .rv rfl, arrName, Arr.off]
    push_cast
    ring
  case LH =>
    have hR : G.affG P g cell "LH" lam x i =
        G.high (G.ten P cell "rl" (lam / 2) x i) (G.kR P g lam) P.y.h.hr := rfl
    show lin D t tb L0 w .LH lam x i = G.affG P g cell "LH" lam x i
    rw [hR]
    rw [T.hr, high_one,
      show G.kR P g lam = (D.Pl lam).kr from T.kr lam hlam (odd_of_present rfl hp)]
    simp only [lin, key, T.val .rl rfl, arrName, Arr.off]
    push_cast
    ring
  case QKH =>
    have hR : G.affG P g cell "QKH" lam x i =
        G.high (G.ten P cell "rqk" lam x i) (G.kQK P g lam x) P.y.h.hq := rfl
    show lin D t tb L0 w .QKH lam x i = G.affG P g cell "QKH" lam x i
    rw [hR]
    rw [T.hq, high_two, T.kQK_eq hlam]
    simp only [lin, key, T.val .rqk rfl, arrName, Arr.off]
    push_cast
    ring
  case N1H =>
    have hR : G.affG P g cell "N1H" lam x i =
        G.high (G.ten P cell "ra" lam x i) (G.kL P g lam Model.Layer.LK1) 2 := rfl
    show lin D t tb L0 w .N1H lam x i = G.affG P g cell "N1H" lam x i
    rw [hR]
    rw [high_two, show G.kL P g lam Model.Layer.LK1 = (D.Pl lam).n1.K from T.K1 lam hlam,
      Inst.Model.Site.shigh_of_le (T.K1le lam hlam)]
    simp only [lin, key, T.val .ra rfl, arrName, Arr.off]
    push_cast
    ring
  case N2H =>
    have hR : G.affG P g cell "N2H" lam x i =
        G.high (G.ten P cell "rm" lam x i) (G.kL P g lam Model.Layer.LK2) 2 := rfl
    show lin D t tb L0 w .N2H lam x i = G.affG P g cell "N2H" lam x i
    rw [hR]
    rw [high_two, show G.kL P g lam Model.Layer.LK2 = (D.Pl lam).n2.K from T.K2 lam hlam,
      Inst.Model.Site.shigh_of_le (T.K2le lam hlam)]
    simp only [lin, key, T.val .rm rfl, arrName, Arr.off]
    push_cast
    ring
  case ROW =>
    have hR : G.affG P g cell "ROW" lam x i =
        ((Model.ledMu P.y.h.xl (x % Model.ledNR P.y.h.xl) : ℕ) : K) *
        G.dig P cell (2 * lam + x / Model.ledNR P.y.h.xl) (x % Model.ledNR P.y.h.xl) i := rfl
    show lin D t tb L0 w .ROW lam x i = G.affG P g cell "ROW" lam x i
    rw [hR]
    rw [T.xl, show Model.ledNR 5 = 99 from rfl, show Model.ledMu 5 (x % 99) = Model.ledMu5 (x % 99)
      from rfl,
      ← mu_eq]
    simp only [lin, key, led, Inst.Model.FFSeg.nLedger, G.dig, T.val .D rfl, arrName, Arr.off]
    push_cast
    ring
  case SEL =>
    have hR : G.affG P g cell "SEL" lam x i =
        128 * G.ten P cell "sel" (lam / 2) x i := rfl
    show lin D t tb L0 w .SEL lam x i = G.affG P g cell "SEL" lam x i
    rw [hR]
    simp only [lin, key, T.val .sel rfl, arrName, Arr.off]
    push_cast
    ring
  case L3 =>
    have hR : G.affG P g cell "L3" lam x i =
        32 * G.ten P cell "l3" (lam / 2) x i := rfl
    show lin D t tb L0 w .L3 lam x i = G.affG P g cell "L3" lam x i
    rw [hR]
    simp only [lin, key, T.val .l3 rfl, arrName, Arr.off]
    push_cast
    ring
  case G0 =>
    have hR : G.affG P g cell "G0" lam x i =
        G.ten P cell "g0" lam x i + 128 := rfl
    show lin D t tb L0 w .G0 lam x i = G.affG P g cell "G0" lam x i
    rw [hR]
    simp only [lin, key, T.val .g0 rfl, arrName, Arr.off]
    push_cast
    ring
  case CN1 =>
    have hR : G.affG P g cell "CN1" lam x i =
        G.ten P cell "aw" lam x i + 2 ^ 28 * G.ten P cell "a" lam x i + G.clampK := rfl
    show lin D t tb L0 w .CN1 lam x i = G.affG P g cell "CN1" lam x i
    rw [hR]
    simp only [lin, key, G.clampK, T.val .aw rfl, T.val .a rfl, arrName, Arr.off]
    push_cast
    ring
  case CN2 =>
    have hR : G.affG P g cell "CN2" lam x i =
        G.ten P cell "mw" lam x i + 2 ^ 28 * G.ten P cell "m" lam x i + G.clampK := rfl
    show lin D t tb L0 w .CN2 lam x i = G.affG P g cell "CN2" lam x i
    rw [hR]
    simp only [lin, key, G.clampK, T.val .mw rfl, T.val .m rfl, arrName, Arr.off]
    push_cast
    ring
  case CQK =>
    have hR : G.affG P g cell "CQK" lam x i =
        G.ten P cell "qkw" lam x i + 2 ^ 28 * (if x < P.y.dq then G.ten P cell "q" lam x i
        else G.ten P cell "kx" lam (x - P.y.dq) i) + G.clampK := rfl
    show lin D t tb L0 w .CQK lam x i = G.affG P g cell "CQK" lam x i
    rw [hR]
    rw [T.dq]
    simp only [lin, key, G.clampK, T.val .qkw rfl, T.val .q rfl, T.val .kx rfl, arrName, Arr.off]
    split_ifs <;> push_cast <;> ring
  case CV =>
    have hR : G.affG P g cell "CV" lam x i =
        G.ten P cell "vw" lam x i + 2 ^ 28 * G.ten P cell "v" lam x i + G.clampK := rfl
    show lin D t tb L0 w .CV lam x i = G.affG P g cell "CV" lam x i
    rw [hR]
    simp only [lin, key, G.clampK, T.val .vw rfl, T.val .v rfl, arrName, Arr.off]
    push_cast
    ring
  case CLR =>
    have hR : G.affG P g cell "CLR" lam x i =
        G.ten P cell "ly" (lam / 2) x i + 2 ^ 25 * (G.ten P cell "lr" (lam / 2) x i - G.ten P cell
          "l3" (lam / 2) x i) + G.clampK := rfl
    show lin D t tb L0 w .CLR lam x i = G.affG P g cell "CLR" lam x i
    rw [hR]
    simp only [lin, key, G.clampK, T.val .ly rfl, T.val .lr rfl, T.val .l3 rfl, arrName, Arr.off]
    push_cast
    ring
  case F =>
    have hR : G.affG P g cell "F" lam x i =
        (if P.y.h.gcl then G.ten P cell "g0" lam x i + 256 * G.ten P cell "gc" lam x i else G.ten P
          cell "gi" lam x i) +
        2 ^ 28 * G.ten P cell "s" lam x i + 2 ^ 15 + 2 ^ 40 := rfl
    show lin D t tb L0 w .F lam x i = G.affG P g cell "F" lam x i
    rw [hR]
    rw [T.gcl, if_pos rfl]
    simp only [lin, key, T.val .g0 rfl, T.val .gc rfl, T.val .sl rfl, arrName, Arr.off]
    push_cast
    ring
  case MR =>
    have hR : G.affG P g cell "MR" lam x i =
        2 ^ (if P.y.h.gcl then 14 else 15) + 2 ^ 17 * G.ten P cell "sc" (lam / 2) 0 i := rfl
    show lin D t tb L0 w .MR lam x i = G.affG P g cell "MR" lam x i
    rw [hR]
    rw [T.gcl, if_pos rfl]
    simp only [lin, T.val .sc rfl, arrName, Arr.off]
    push_cast
    ring
  case CG =>
    have hR : G.affG P g cell "CG" lam x i =
        G.ten P cell "gh" lam x i + 2 ^ 28 * G.ten P cell "gc" lam x i + 49152 + 2 ^ 35 + 2 ^ 40 :=
          rfl
    show lin D t tb L0 w .CG lam x i = G.affG P g cell "CG" lam x i
    rw [hR]
    simp only [lin, key, T.val .gh rfl, T.val .gc rfl, arrName, Arr.off]
    push_cast
    ring

end Ties

section Line

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low u : ℕ → K} {P : Model.Layer.Pub} {g : ℕ} {cell : G.NameG → K}

/-- **What a segment's form is worth, over G.lean's terms: all 34, the affine part.** -/
theorem alg_line (F : Fits ρ W v D c t low u) (T : TiesG P g cell D t) (s : Fam)
    (lam : ℕ) (hlam : lam < D.nl) (hp : present s lam = true) {ew wh : Array E}
    (hsz : ew.size = len D s) (hbl : byBlocks s = true → Wts ρ ew wh v.y.ls low (len D s)) {f : Aff}
    (h : v.line (segName s) lam ew wh = some f) :
    f.value ρ W = ∑ x ∈ range (len D s), ρ.val (ew.getD x zeroE) *
      Blocks.ext D.lT (fun i => G.affG P g cell (segName s) lam x i) u := by
  rw [F.line_lin ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩ 0
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
      fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩) s lam hlam hp hsz
    hbl h]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  exact Blocks.ext_congr (fun i _ => T.lin_affG _ _ _ s lam x i hlam hp) u

end Line

#print axioms TiesG.lin_affG
#print axioms alg_line

end OnBytes.Road.Alg
