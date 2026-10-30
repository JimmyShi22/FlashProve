-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/KeyForms.lean: the key forms of an attention segment, and the rule values of its
  named scalars. Definitions, and one count at the reference parameters (`ref_count`).

  The rule value of a masked scalar (`Forms.scalar`, Blocks/RelForm.lean) is the polynomial in the
  cells and the challenges that its value is claimed to equal. A key form KF_c is a formula in
  masked scalars. That at their rule values it is the multilinear extension of the call's vector of
  looked-up values (keys in Lean names; Inst/Model/Att/Trace.lean) at its key point z_c, under
  hypotheses on the sizes, is `kfExt` (Inst/Model/Att/KeyFormsExt/All.lean). One of the hypotheses:
  calls 1 and 2 have the same size: the sums SS2M, SS2D are formed with the weights of call 1 while
  KF_2 is compared with call 2; without it the statement is false (found by evaluating an instance;
  not proved in this library). The calls 1 to 4 of the comments are 0 to 3 in `Fin 4`.
  * `KSc`: the names of the masked scalars of the key forms (37 at the reference parameters): R0,
    R1, FL of the four families of calls 1 and 2 and E0, E1 of 2M, 2D are `cell u jj`; then MS, SS
    of 2M, 2D; ACC, ZO, ZC, RH, RH'; IB_k; RG, RG'.
  * `rv`: the rule value of each, a polynomial in the cells and in z.
  * `KF`: the four key forms, as functions of any values v of these scalars. So `KF .. (rv ..) c`,
    the key form at the rule values, is rv(KF_c), and at the values of the sent scalars it is
    val(KF_c).
  * `joinRhs`: ∑_c w_c (α - KF_c), the right-hand side of the join: the claim that this sum is the
    value of C_end, the end form of the product tree over the looked-up values. α is the argument
    `al` of `joinRhs`, the challenge of the lookup argument.
  * `rvM6`, `rvCl`, `rvKC`, `rvIBP`, `Ebk`, `rvX`: the rule values of the other named scalars.

  Notation: `D`: `Dim` (Inst/Model/Att/Index.lean): the sizes of an attention segment; `C`: `Calls`
  (Inst/Model/Att/Trace.lean): the numbers of the main lookup argument: call c has 2^(a c) indices;
  a tree has 2^Dk looked-up values; 2^sg tree numbers; `p`: `Pub E` (Inst/Model/Att/Sums.lean): the
  challenges on which the summands depend; `p.z`: the end point of the product tree over the
  looked-up values of the main lookup argument; `t`: `Raw → E`; `Raw` (Trace.lean): the names of the
  cells (without the multiplicity bits); `Fam` (Inst/Model/Att/Points.lean): the seven families of
  looked-up values; `u.l D`: ℓ: a piece of the family has 2^ℓ keys; `C.zC c z`: the key point of
  call c: z_c = (the last e coordinates of z_tr | z_in), a_c coordinates; `inn u`: the inner point
  of a family: the last ℓ coordinates of z_c; `wp u b`: the weight of the piece (u, b); `LL u`: L^u
  = ∑_b wp^u_b; `sh u off`: the part of a point from the coordinate off on.
-/
import Inst.Model.Att.Sums

set_option autoImplicit false

namespace Inst.Model.AttSeg

open Finset Blocks

variable {E : Type} [Field E]

/-- the region of a family of calls 1 and 2 -/
def Fam.reg : Fam → Reg
  | .m1 => .M
  | .m2 => .M
  | _ => .D

/-- The names of the masked scalars of the key forms. -/
inductive KSc
  /-- R0, R1, FL (jj = 0, 1, 2) for u = 1M, 1D, 2M, 2D; E0, E1 (jj = 3, 4) for u = 2M, 2D -/
  | cell (u : Fam) (jj : ℕ)
  /-- MS2M, MS2D -/
  | ms (ρ : Reg)
  /-- SS2M, SS2D -/
  | ss (ρ : Reg)
  | acc
  | zo
  | zc
  | rh
  | rh'
  | ib (k : ℕ)
  | rg
  | rg'
  deriving DecidableEq

/-- the list of the scalars -/
def KSc.all (D : Dim) : List KSc :=
  [.cell .m1 0, .cell .m1 1, .cell .m1 2, .cell .d1 0, .cell .d1 1, .cell .d1 2,
   .cell .m2 0, .cell .m2 1, .cell .m2 2, .cell .m2 3, .cell .m2 4, .ms .M, .ss .M,
   .cell .d2 0, .cell .d2 1, .cell .d2 2, .cell .d2 3, .cell .d2 4, .ms .D, .ss .D,
   .acc, .zo, .zc, .rh, .rh'] ++ (List.range D.lT).map .ib ++ [.rg, .rg']

section Rules
variable (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E)

/-- the extension of an array over (g | i | n) at (y_g | y_i | y_n) -/
def atY (a : ℕ → ℕ → ℕ → E) : E :=
  ext D.l4 (fun X => a (X / D.ch / D.T) (X / D.ch % D.T) (X % D.ch)) (sh (uW D C p.z) 1)

/-- The rule values. -/
def rv : KSc → E
  | .cell u jj =>
    ∑ b ∈ range D.nb, wp D C p.z u b * ext (u.l D) (fun x => t (.c u.reg jj b x)) (inn D C p.z u)
  | .ms .M =>
    ∑ b ∈ range D.nb, wp D C p.z .m2 b *
      rd2 D (zg D C p.z) (psiRow D (zP D C p.z) (zs D C p.z) (zi' D C p.z)) (mxV t b)
  | .ms .D =>
    ∑ b ∈ range D.nb, wp D C p.z .d2 b *
      rd2 D (zgD D C p.z) (eqT D (cat (D.lP + 1) (zID D C p.z) (zi' D C p.z))) (mxV t b)
  | .ss .M => sumPhi D C p t .s6b
  | .ss .D => sumPhi D C p t .s6d
  | .acc => ∑ b ∈ range D.nb, wp D C p.z .w3 b * atY D C p (AC D t b)
  | .zo => sumPhi D C p t .s8
  | .zc => ∑ b ∈ range D.nb, wp D C p.z .w3 b * rd2 D (yg D C p.z) (eqT D (yi D C p.z)) (denV t b)
  | .rh => ∑ b ∈ range D.nb, wp D C p.z .w3 b * atY D C p fun g i n => t (.qh b g i n)
  | .rh' => ∑ b ∈ range D.nb, wp D C p.z .w3 b * atY D C p fun g i n => t (.qh' b g i n)
  | .ib k =>
    ∑ b ∈ range D.nb, wp D C p.z .x3 b * rd2 D (xg D C p.z) (eqT D (xi D C p.z)) (ibV t k b)
  | .rg => ∑ b ∈ range D.nb, wp D C p.z .f4 b * atY D C p fun g i n => t (.qh b g i n)
  | .rg' => ∑ b ∈ range D.nb, wp D C p.z .f4 b * atY D C p fun g i n => t (.qh' b g i n)

/-! ### The key forms -/

variable (v : KSc → E)

/-- DP2M = MS2M - SS2M + C L^M ones(z_s); DP2D = MS2D - SS2D + Om L^D (1 - LE(z_j', z_i')). Here C
is `D.cutC` (not the variable `C`, a `Calls`), L^M and L^D are `LL` at the families `.m2` and `.d2`,
and Om is `Om D`. -/
def DP [scl : Scl] : Reg → E
  | .M =>
    v (.ms .M) - v (.ss .M) + ((D.cutC : ℤ) : E) * LL D C p.z .m2 * ones (D.lP + 1) (zs D C p.z)
  | .D =>
    v (.ms .D) - v (.ss .D) +
      ((Om D : ℤ) : E) * LL D C p.z .d2 * (1 - LE D.lB (zj' D C p.z) (zi' D C p.z))

/-- REM = 2 ACC + ZC - 2 ZO -/
def REM : E := 2 * v .acc + v .zc - 2 * v .zo

/-- The four key forms, as functions of the values of the scalars. -/
def KF [scl : Scl] : Fin 4 → E
  | 0 =>
    ∑ u ∈ ({.m1, .d1} : Finset Fam), ((v (.cell u 0) + 128 * LL D C p.z u) +
      2 ^ 20 * (v (.cell u 1) + 128 * LL D C p.z u) + 2 ^ 40 * v (.cell u 2))
  | 1 =>
    (1 - LL D C p.z .m2 - LL D C p.z .d2) * ((D.cutC - 2 ^ D.sh + 2 ^ 32 : ℤ) : E) +
      ∑ u ∈ ({.m2, .d2} : Finset Fam), (DP D C p v u.reg - (v (.cell u 0) + 128 * LL D C p.z u) -
        256 * (v (.cell u 1) + 128 * LL D C p.z u) + 2 ^ 32 * v (.cell u 2) +
        2 ^ 33 * (v (.cell u 3) + 128 * LL D C p.z u + 256 * v (.cell u 4)))
  | 2 =>
    (1 - zChi D C p.z) * (REM v - 2 ^ 16 * (v .rh + 128 * LL D C p.z .w3)) +
      zChi D C p.z *
        (2 * v .zc - LL D C p.z .w3 - REM v - 2 ^ 16 * (v .rh' + 128 * LL D C p.z .w3)) +
      2 ^ (16 - D.lT) *
        (LL D C p.z .x3 * idP D.lT (xi D C p.z) - ∑ k ∈ range D.lT, 2 ^ k * v (.ib k))
  | 3 => (v .rg + 128 * LL D C p.z .f4) + 2 ^ 20 * (v .rg' + 128 * LL D C p.z .f4)

/-- ∑_c w_c (α - KF_c): the join says that this is val(C_end) -/
def joinRhs [scl : Scl] (al : E) : E := ∑ c : Fin 4, C.wC c p.z * (al - KF D C p v c)

/-! ### The other named scalars -/

/-- M6_b = ~mx_b(t_g, t_i) -/
def rvM6 (b : ℕ) : E := rd2 D p.tg (eqT D p.ti) (mxV t b)
/-- clM, clD: the sums of Φ_11, Φ_12 over their hypercubes -/
def rvCl : Reg → E
  | .M => sumPhi D C p t .s11
  | .D => sumPhi D C p t .s12
/-- KC_λ = ~key_λ(p_g, p_j, f_n), at the end point (p_j | p_g | p_i) of step 18 -/
def rvKC (pt : ℕ → E) (lam : ℕ) : E := rd3 D (sh pt D.lT) (eqT D pt) p.fn (keyV t lam)
/-- IBP_(b,k) = ~ib_(b,k)(p_g, p_i) -/
def rvIBP (pt : ℕ → E) (b k : ℕ) : E := rd2 D (sh pt D.lT) (eqT D (sh pt (D.lT + D.lg))) (ibV t k b)
/-- E_(b,k) = IBP_(b,k) (2 y_k - 1) + (1 - y_k), as a function of the value of IBP_(b,k); y_k is the
coordinate of p_j that belongs to the bit of weight 2^k -/
def Ebk (pt : ℕ → E) (ibp : E) (k : ℕ) : E :=
  ibp * (2 * pt (D.lT - 1 - k) - 1) + (1 - pt (D.lT - 1 - k))
/-- x_(b,k) = ∏_(k' ≤ k) E_(b,k') -/
def rvX (pt : ℕ → E) (b k : ℕ) : E := ∏ k' ∈ range (k + 1), Ebk D pt (rvIBP D t pt b k') k'

end Rules

theorem ref_count : (KSc.all Dim.ref).length = 37 ∧ (KSc.all Dim.ref).Nodup := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

end Inst.Model.AttSeg
