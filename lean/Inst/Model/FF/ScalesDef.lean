-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/ScalesDef.lean: this library's rendering of the checks of the implementation's
  verifier on the shifts and normalisations of one layer. To audit the relation `RinfPP` at valid
  settings (`Lawful`; both in Inst/Model/Scales.lean), read this file. Definitions only.

  The definitions on which "valid" (`Lawful` in Lean names) rests are in this file, separate from
  Inst/Model/FF/Scales.lean, so that they can be read without a proof beside them.
  * `Scales.Ty` .. `Bu`, `top`, `Shift`, `SiteU`, `dfTerm`, `SiteW`: the constants of the
    no-overflow conditions of the implementation's verifier (verifier/src/cp_verify.cpp: the
    rejections "no-wrap-.."), its check on a shift's range ("KL-shift-range") and its two
    no-overflow conditions of a rounding site ("U-", "W-").
  * `LawfulW s`: the rendering of the checks on the scales of one layer, clause by clause, evaluated
    at the reference sizes and digit forms.
  * `Ranges s`: the closed intervals; that `LawfulW s ↔ Ranges s` is the theorem `lawfulW_iff` of
    Inst/Model/FF/Lawful.lean.
  Notation:
    a rounding site: Inst/Model/Common/Site.lean tells "how two lookups express a rounding q =
      rhu(A, k)".
    `s`: a `LayerScale`, "The scales of one layer."; M, K, eps: the fields of a `NormPar`, "exponent
      of the reciprocal; shift; constant" (Inst/Model/Program.lean).
    k, df: natural numbers: a shift; a digit form, 0, 1 or 2 (`top`: "at most 16, 24 or 32 at digit
      form 0, 1 or 2").
    up(k), dn(k): `Site.up k`, "up(k) = max(k, 16): the number of bits of the scaled remainder.";
      `Site.dn k`, "dn(k) = max(0, 16 − k): the remainder of a rounding by k is scaled by 2^dn(k),
      so that it fills 16 bits at least." (Inst/Model/Common/Site.lean).
    SP, Ab, Qb: natural numbers, arguments of `SiteU` and `SiteW`; in `LawfulW` their values stand
      in the fields' doc comments, in the order "name | k | df | Ab | SP | Qb".
  Limits: how `LawfulW` relates to the implementation's checks, and where it differs from them, is
  said in the header of Inst/Model/FF/Scales.lean.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Program
import Inst.Model.Common.Site

set_option autoImplicit false

namespace Inst.Model.FFSeg

/-! ## The rendering of the implementation's checks on the scales of one layer -/

namespace Scales

/-- The constants of the no-overflow conditions (verifier/src/cp_verify.cpp): Ty = 2^18, the bound
on a cell; Ty_2 = 257 Ty; BC = 2^11, the bound on a clamped cell; BW = 2^12, the bound on a weight's
absolute value; acc = d BC BW; Bu = 2^15. -/
def Ty : ℕ := 2 ^ 18
def Ty2 : ℕ := 257 * Ty
def BC : ℕ := 2 ^ 11
def BW : ℕ := 2 ^ 12
def acc : ℕ := 5120 * BC * BW
def Bu : ℕ := 2 ^ 15

/-- [KL-shift-range]: k is at least 1, and at most 16, 24 or 32 at digit form 0, 1 or 2. -/
def top : ℕ → ℕ
  | 0 => 16
  | 1 => 24
  | _ => 32
def Shift (df k : ℕ) : Prop := 1 ≤ k ∧ k ≤ top df

/-- The condition (U-name) of a rounding site: SP 2^up(k) <= 2^60. -/
def SiteU (SP k : ℕ) : Prop := SP * 2 ^ Site.up k ≤ 2 ^ 60

/-- the term of the digit form in (W-name): "[df = 1] 2^16 (Ty + 128) + [df = 2] 2^16 (Ty_2 +
32,896)" -/
def dfTerm : ℕ → ℕ
  | 1 => 2 ^ 16 * (Ty + 128)
  | 2 => 2 ^ 16 * (Ty2 + 32896)
  | _ => 0

/-- The condition (W-name) of a rounding site: 2^dn(k) (Ab + 2^(k−1) + Qb 2^k) + [df = 1] 2^16 (Ty +
128) + [df = 2] 2^16 (Ty_2 + 32,896) < 2^60. -/
def SiteW (df Ab Qb k : ℕ) : Prop :=
  2 ^ Site.dn k * (Ab + 2 ^ (k - 1) + Qb * 2 ^ k) + dfTerm df < 2 ^ 60

instance (df k : ℕ) : Decidable (Shift df k) := by unfold Shift; infer_instance
instance (SP k : ℕ) : Decidable (SiteU SP k) := by unfold SiteU; infer_instance
instance (df Ab Qb k : ℕ) : Decidable (SiteW df Ab Qb k) := by unfold SiteW; infer_instance

end Scales

open Scales

instance (np : NormPar) : Decidable np.OK := by unfold NormPar.OK; infer_instance

/-- The scales of one layer are valid: this library's rendering of the checks of the
implementation's verifier that read them (verifier/src/cp_verify.cpp: the rejections "KL-..",
"policy-norm" and "no-wrap-.."), at the reference sizes and digit forms. The arguments of its calls
of "site" are given as "name | k | df | Ab | SP | Qb". `LawfulW` does not read sh and expRows, which
are attention's (Inst/Model/Att/Scales.lean). -/
structure LawfulW (s : LayerScale) : Prop where
  /-- [KL-shift-range], class {q, k}, digit form 2 -/
  rq : Shift 2 s.kq
  rk : Shift 2 s.kk
  /-- class {v}, digit form 1 -/
  rv : Shift 1 s.kv
  /-- class {o}, digit form 1 -/
  ro : Shift 1 s.ko
  /-- class {dense, shared, routed gate}, digit form 1 -/
  rg : Shift 1 s.kg
  rg' : Shift 1 s.kg'
  /-- class {the three ups}, digit form 1 -/
  ru : Shift 1 s.ku
  ru' : Shift 1 s.ku'
  /-- class {dense down, experts' down}, digit form 1 -/
  rd : Shift 1 s.kd
  /-- class {router}, digit form 1 -/
  rr : Shift 1 s.kr
  /-- [KL-kq-kk]: kq = kk unless both are >= 16 -/
  qk : s.kq = s.kk ∨ (16 ≤ s.kq ∧ 16 ≤ s.kk)
  /-- [KL-norm]: 24 <= M <= 47; M <= K + 14; 17 <= K <= 32, and [policy-norm], (ledger-eps):
  1 <= eps < 2^48 -/
  n1 : s.n1.OK
  n2 : s.n2.OK
  /-- "gate | kg; kgR | gate's | acc | 2 Qb + 1 | 2^22 + 128" -/
  Ug : SiteU (2 * (2 ^ 22 + 128) + 1) s.kg
  Wg : SiteW 1 acc (2 ^ 22 + 128) s.kg
  Ug' : SiteU (2 * (2 ^ 22 + 128) + 1) s.kg'
  Wg' : SiteW 1 acc (2 ^ 22 + 128) s.kg'
  /-- "up | ku; kuR | up's | acc | 2^16 | 2^15" -/
  Uu : SiteU (2 ^ 16) s.ku
  Wu : SiteW 1 acc (2 ^ 15) s.ku
  Uu' : SiteU (2 ^ 16) s.ku'
  Wu' : SiteW 1 acc (2 ^ 15) s.ku'
  /-- "norm | K_1; K_2 | 2 | 2^M + 2^38 | 2^16 | 2^15" -/
  Un1 : SiteU (2 ^ 16) s.n1.K
  Wn1 : SiteW 2 (2 ^ s.n1.M + 2 ^ 38) (2 ^ 15) s.n1.K
  Un2 : SiteU (2 ^ 16) s.n2.K
  Wn2 : SiteW 2 (2 ^ s.n2.M + 2 ^ 38) (2 ^ 15) s.n2.K
  /-- "down | kd | down's | f 2^12 Bu BW | 2^41 | 2^40" -/
  Ud : SiteU (2 ^ 41) s.kd
  Wd : SiteW 1 (16384 * 2 ^ 12 * Bu * BW) (2 ^ 40) s.kd
  /-- "qk | kq; kk | q, k's | 2 . 2^cs d BC BW | 2^16 | 2^15", cs = 12 -/
  Uq : SiteU (2 ^ 16) s.kq
  Wq : SiteW 2 (2 * 2 ^ 12 * 5120 * BC * BW) (2 ^ 15) s.kq
  Uk : SiteU (2 ^ 16) s.kk
  Wk : SiteW 2 (2 * 2 ^ 12 * 5120 * BC * BW) (2 ^ 15) s.kk
  /-- "o | ko | o's | dq BC BW | 2^41 | 2^40" -/
  Uo : SiteU (2 ^ 41) s.ko
  Wo : SiteW 1 (5120 * BC * BW) (2 ^ 40) s.ko
  /-- "v | kv | v's | acc | 2^16 | 2^15" -/
  Uv : SiteU (2 ^ 16) s.kv
  Wv : SiteW 1 acc (2 ^ 15) s.kv
  /-- "lr | kr | router's | acc | 16 Ty_2 + 15 | 8 Ty_2 + 7" -/
  Ur : SiteU (16 * Ty2 + 15) s.kr
  Wr : SiteW 1 acc (8 * Ty2 + 7) s.kr
  /-- "(guard-radix-clamp), each mixture-of-experts layer: floor((acc + 2^(kr−1)) / 2^(kr+3)) + 1 +
  2^15 + 2^16 < 2^25" -/
  grc : (acc + 2 ^ (s.kr - 1)) / 2 ^ (s.kr + 3) + 1 + 2 ^ 15 + 2 ^ 16 < 2 ^ 25

/-- The conditions of `LawfulW` in closed form, as intervals. -/
structure Ranges (s : LayerScale) : Prop where
  kq : 5 ≤ s.kq ∧ s.kq ≤ 32
  kk : 5 ≤ s.kk ∧ s.kk ≤ 32
  qk : s.kq = s.kk ∨ (16 ≤ s.kq ∧ 16 ≤ s.kk)
  kv : 1 ≤ s.kv ∧ s.kv ≤ 24
  ko : 1 ≤ s.ko ∧ s.ko ≤ 19
  kg : 1 ≤ s.kg ∧ s.kg ≤ 24
  kg' : 1 ≤ s.kg' ∧ s.kg' ≤ 24
  ku : 1 ≤ s.ku ∧ s.ku ≤ 24
  ku' : 1 ≤ s.ku' ∧ s.ku' ≤ 24
  kd : 10 ≤ s.kd ∧ s.kd ≤ 19
  kr : 8 ≤ s.kr ∧ s.kr ≤ 24
  n1 : s.n1.OK
  n2 : s.n2.OK

instance (s : LayerScale) : Decidable (Ranges s) :=
  decidable_of_iff ((5 ≤ s.kq ∧ s.kq ≤ 32) ∧ (5 ≤ s.kk ∧ s.kk ≤ 32) ∧
      (s.kq = s.kk ∨ (16 ≤ s.kq ∧ 16 ≤ s.kk)) ∧ (1 ≤ s.kv ∧ s.kv ≤ 24) ∧
      (1 ≤ s.ko ∧ s.ko ≤ 19) ∧ (1 ≤ s.kg ∧ s.kg ≤ 24) ∧ (1 ≤ s.kg' ∧ s.kg' ≤ 24) ∧
      (1 ≤ s.ku ∧ s.ku ≤ 24) ∧ (1 ≤ s.ku' ∧ s.ku' ≤ 24) ∧ (10 ≤ s.kd ∧ s.kd ≤ 19) ∧
      (8 ≤ s.kr ∧ s.kr ≤ 24) ∧ s.n1.OK ∧ s.n2.OK)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩,
      fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩⟩

end Inst.Model.FFSeg
