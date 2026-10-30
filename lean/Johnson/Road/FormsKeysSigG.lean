-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysSigG.lean: the late panels' shares make up the summand of the sumcheck over
the positions at its end point: the library with itself.

A key of a feed-forward segment holds, beside its affine part and a matrix product, products of two
values at one position (term in Inst/Model/FF/Objects.lean). The library sums them under the
weights to TS, and has for the sumcheck over the positions the summand Gpos: the same sum with each
of the two factors replaced by its extension (termHat). The same file defines the late panels of
the batched inner-product sumcheck and Sig1, the sum of their shares. This file shows that Sig1, at
the true contractions of the cells at a point zh, is Gpos at zh.

Every statement here compares objects of the library with objects of the library. The file imports
no file of OnBytes/ but two of this folder that do not either.

Main definitions: nine, nineIn. Main theorems: sig1_gpos; sig1_gpos_of (the same with the panel
QK's share as a hypothesis); share_N1, share_N2, share_XR, share_DD, share_MR, share_Gr, share_Ur,
share_Dr (the share of one panel); famsIn_nine, sum_hat_nine, hat_zero.

The second point of the record rdTrue and the point zh that the panels take are one and the same
here: the theorems speak of that case alone.

The hypotheses, and that they can be met.
 - H2 l' j = hhU D t (2 l' + 1) (fe + j) zh for l' < ne and j < fe: the vector that the panels Dr
   read is the honest vector of the routed gated products at zh. Met by taking that for H2.
 - Dim.ChOK, and for each layer kq = kk or both at least 16: for the panel QK alone; met by the
   reference sizes and by every lawful table of scales; whether the clause on the shifts holds at
   the small public example, where the library's LawfulW fails, is run nowhere: see
   Johnson/Road/FormsKeysSigQ.lean. Nothing is asked of H1, tb, L0, w or z.

What is not claimed. That Gpos at the vertices of the cube sums to the products in the keys is
another statement. Between the two stands the sumcheck over the positions, of which nothing is
said. Nothing is a statement on what a verifier's acceptance shows. The program does not import
this file.
-/
import Johnson.Road.FormsKeysSigL
import Johnson.Road.FormsKeysSigQ

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW Pan Rd rdTrue pans Sig1 Gpos termHat fams famsIn present
  isExp isExpL ew sw el wc valU hhU xU)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A sum over the list of the first n numbers is the sum over the range. -/
theorem listRange_sum (g : ℕ → K) (n : ℕ) :
    ((List.range n).map g).sum = ∑ x ∈ range n, g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A sum over the numbers below n of a function that vanishes at the even numbers. -/
theorem sum_oddOnly (f : ℕ → K) (h0 : ∀ l, ¬ l % 2 = 1 → f l = 0) : ∀ n : ℕ,
    ∑ l ∈ range n, f l = ∑ l' ∈ range (n / 2), f (2 * l' + 1)
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, sum_oddOnly f h0 n]
    by_cases h : n % 2 = 1
    · have e : (n + 1) / 2 = n / 2 + 1 := by omega
      have e2 : 2 * (n / 2) + 1 = n := by omega
      rw [e, sum_range_succ, e2]
    · have e : (n + 1) / 2 = n / 2 := by omega
      rw [h0 n h, e, add_zero]

/-- A weight under the factor of a shift, times a number: the weight times the number under the
factor. -/
theorem scl_pass (k : ℕ) (a b : K) :
    Inst.Model.Site.scl k a * b = a * Inst.Model.Site.scl k b := by
  rw [Inst.Model.Site.scl_mul, Inst.Model.Site.mul_scl]

/-- Half of an odd number. -/
theorem half_odd (l' : ℕ) : (2 * l' + 1) / 2 = l' := by omega

/-- An odd layer has routed experts. -/
theorem odd_hasExp (l' : ℕ) : isExpL (2 * l' + 1) = true := by
  have e : (2 * l' + 1) % 2 = 1 := by omega
  simp [isExpL, e]

/-- A layer whose number is not odd has none. -/
theorem even_noExp {l : ℕ} (h : ¬ l % 2 = 1) : ¬ isExpL l = true := by
  have e : l % 2 = 0 := by omega
  simp [isExpL, e]

/-! ## The families with a product of two values -/

/-- The nine families whose keys hold products of two values at one position. -/
def nine : List Fam := [.G, .U, .D, .N1, .N2, .QK, .XR, .DD, .MR]

/-- Those of them that call c holds in a layer; b: the layer has routed experts. -/
def nineIn : Fin 8 → Bool → List Fam
  | 0, _ => [.G, .U]
  | 1, _ => [.N1, .N2, .D]
  | 2, true => [.QK, .XR, .DD]
  | 2, false => [.QK]
  | 5, true => [.MR]
  | _, _ => []

/-- The families of call c that are present in layer l and hold such products. -/
theorem famsIn_nine (c : Fin 8) (l : ℕ) :
    (famsIn c l).filter (fun s => decide (s ∈ nine)) = nineIn c (isExpL l) := by
  have h : ∀ (b : Bool) (c : Fin 8),
      ((fams c).filter fun s => !isExp s || b).filter (fun s => decide (s ∈ nine)) =
        nineIn c b := by decide
  exact h (isExpL l) c

section Hat

variable [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
  (z zh : ℕ → K)

/-- The summand of the other families is 0. -/
theorem hat_zero {s : Fam} (hs : s ∉ nine) (l : ℕ) : termHat D t tb L0 w z s l zh = 0 := by
  cases s <;> first
    | rfl
    | exact absurd (by simp [nine]) hs

/-- In a sum of the summands over a list of families only the nine count. -/
theorem sum_hat_nine (l : ℕ) : ∀ L : List Fam,
    (L.map fun s => termHat D t tb L0 w z s l zh).sum =
      ((L.filter fun s => decide (s ∈ nine)).map fun s => termHat D t tb L0 w z s l zh).sum
  | [] => rfl
  | s :: L => by
    by_cases hs : s ∈ nine
    · rw [List.filter_cons_of_pos (by simpa using hs), List.map_cons, List.map_cons, List.sum_cons,
        List.sum_cons, sum_hat_nine l L]
    · rw [List.filter_cons_of_neg (by simpa using hs), List.map_cons, List.sum_cons,
        hat_zero D t tb L0 w z zh hs l, zero_add, sum_hat_nine l L]

/-- On a layer without routed experts the summands of G, U and D are 0. -/
theorem hat_G_even {l : ℕ} (h : ¬ l % 2 = 1) : termHat D t tb L0 w z .G l zh = 0 :=
  if_neg (even_noExp h)
/-- The same for U. -/
theorem hat_U_even {l : ℕ} (h : ¬ l % 2 = 1) : termHat D t tb L0 w z .U l zh = 0 :=
  if_neg (even_noExp h)
/-- The same for D. -/
theorem hat_D_even {l : ℕ} (h : ¬ l % 2 = 1) : termHat D t tb L0 w z .D l zh = 0 :=
  if_neg (even_noExp h)

end Hat

/-! ## The share of each late panel but QK -/

section Shares

variable [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
  (z zh : ℕ → K) (H1 H2 : ℕ → ℕ → K)

omit scl in
/-- What the record of the true contractions has for the stream before the first norm of a layer. -/
theorem xF_even (l : ℕ) : (rdTrue D t z zh H1 H2).xF (2 * l) =
    ∑ x ∈ range D.d, ew D z .N1 x * xU D t (2 * l) x zh := by
  show ∑ x ∈ range D.d, ew D z (if (2 * l) % 2 = 0 then Fam.N1 else .N2) x *
    xU D t (2 * l) x zh = _
  rw [if_pos (by omega)]

omit scl in
/-- The same before the second norm. -/
theorem xF_odd (l : ℕ) : (rdTrue D t z zh H1 H2).xF (2 * l + 1) =
    ∑ x ∈ range D.d, ew D z .N2 x * xU D t (2 * l + 1) x zh := by
  show ∑ x ∈ range D.d, ew D z (if (2 * l + 1) % 2 = 0 then Fam.N1 else .N2) x *
    xU D t (2 * l + 1) x zh = _
  rw [if_neg (by omega)]

/-- Panel N1. -/
theorem share_N1 : Pan.N1.share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
    wc D z 1 * ∑ l ∈ range D.nl, el D z 1 l * termHat D t tb L0 w z .N1 l zh := by
  show wc D z 1 * ∑ l ∈ range D.nl, el D z 1 l *
    ∑ _ι ∈ range 1, (rdTrue D t z zh H1 H2).R2 (2 * l) * (rdTrue D t z zh H1 H2).xF (2 * l) = _
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [sum_range_one, xF_even]
  rfl

/-- Panel N2. -/
theorem share_N2 : Pan.N2.share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
    wc D z 1 * ∑ l ∈ range D.nl, el D z 1 l * termHat D t tb L0 w z .N2 l zh := by
  show wc D z 1 * ∑ l ∈ range D.nl, el D z 1 l *
    ∑ _ι ∈ range 1, (rdTrue D t z zh H1 H2).R2 (2 * l + 1) *
      (rdTrue D t z zh H1 H2).xF (2 * l + 1) = _
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [sum_range_one, xF_odd]
  rfl

/-- Panel XR: row l' is layer 2 l' + 1. -/
theorem share_XR : Pan.XR.share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
    wc D z 2 * ∑ l' ∈ range D.ne, el D z 2 (2 * l' + 1) *
      termHat D t tb L0 w z .XR (2 * l' + 1) zh := by
  show wc D z 2 * ∑ l' ∈ range D.ne, el D z 2 (2 * l' + 1) *
    ∑ _ι ∈ range 1, valU D t .sc l' 0 zh *
      ∑ x ∈ range D.d, ew D z .XR x * valU D t .m (2 * l' + 1) x zh = _
  congr 1
  refine sum_congr rfl fun l' _ => ?_
  rw [sum_range_one]
  show _ = el D z 2 (2 * l' + 1) * (valU D t .sc ((2 * l' + 1) / 2) 0 zh *
    ∑ x ∈ range D.d, ew D z .XR x * valU D t .m (2 * l' + 1) x zh)
  rw [half_odd]

/-- Panel DD. -/
theorem share_DD : Pan.DD.share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
    wc D z 2 * ∑ l' ∈ range D.ne, el D z 2 (2 * l' + 1) *
      termHat D t tb L0 w z .DD (2 * l' + 1) zh := by
  show wc D z 2 * ∑ l' ∈ range D.ne, (el D z 2 (2 * l' + 1) * sw D z .DD) *
    ∑ e ∈ range D.nx, valU D t .sel l' e zh * valU D t .lr l' e zh = _
  congr 1
  refine sum_congr rfl fun l' _ => ?_
  show _ = el D z 2 (2 * l' + 1) * (sw D z .DD * ∑ e ∈ range D.nx,
    valU D t .sel ((2 * l' + 1) / 2) e zh * valU D t .lr ((2 * l' + 1) / 2) e zh)
  rw [half_odd, mul_assoc]

/-- Panel MR. -/
theorem share_MR : Pan.MR.share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
    wc D z 5 * ∑ l' ∈ range D.ne, el D z 5 (2 * l' + 1) *
      termHat D t tb L0 w z .MR (2 * l' + 1) zh := by
  show wc D z 5 * ∑ l' ∈ range D.ne, (el D z 5 (2 * l' + 1) * ew D z .MR 0) *
    ∑ e ∈ range D.nx, valU D t .sel l' e zh * valU D t .lr l' e zh = _
  congr 1
  refine sum_congr rfl fun l' _ => ?_
  show _ = el D z 5 (2 * l' + 1) * (ew D z .MR 0 * ∑ e ∈ range D.nx,
    valU D t .sel ((2 * l' + 1) / 2) e zh * valU D t .lr ((2 * l' + 1) / 2) e zh)
  rw [half_odd, mul_assoc]

omit scl in
/-- The rows and columns of a panel with the selector, with the selector's entry drawn out of the
sum over the columns and the rows' one weight out of the sum over the rows. -/
theorem tri_sums (a : K) (n m : ℕ) (s x : ℕ → K) (Y : ℕ → ℕ → K) :
    ∑ e ∈ range n, a * ∑ j ∈ range m, (s e * x j) * Y e j =
      a * ∑ e ∈ range n, s e * ∑ j ∈ range m, x j * Y e j := by
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  congr 1
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- Panel Gr l': the routed gates of layer 2 l' + 1. -/
theorem share_Gr (l' : ℕ) : (Pan.Gr l').share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
    wc D z 0 * (el D z 0 (2 * l' + 1) * termHat D t tb L0 w z .G (2 * l' + 1) zh) := by
  show wc D z 0 * ∑ e ∈ range D.nx,
    Inst.Model.Site.scl (D.Pl (2 * l' + 1)).kg' (el D z 0 (2 * l' + 1)) *
      ∑ j ∈ range D.d, (valU D t .sel l' e zh * valU D t .xr l' j zh) *
        ∑ x ∈ range D.fe, ew D z .G (D.fe + x) * (w (2 * l' + 1)).Eg e j x = _
  rw [tri_sums, scl_pass]
  show _ = wc D z 0 * (el D z 0 (2 * l' + 1) * (if isExpL (2 * l' + 1) then
    Inst.Model.Site.scl (D.Pl (2 * l' + 1)).kg'
      (∑ e ∈ range D.nx, valU D t .sel ((2 * l' + 1) / 2) e zh *
        ∑ j ∈ range D.d, valU D t .xr ((2 * l' + 1) / 2) j zh *
          ∑ x ∈ range D.fe, ew D z .G (D.fe + x) * (w (2 * l' + 1)).Eg e j x) else 0))
  rw [if_pos (odd_hasExp l'), half_odd]

/-- Panel Ur l'. -/
theorem share_Ur (l' : ℕ) : (Pan.Ur l').share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
    wc D z 0 * (el D z 0 (2 * l' + 1) * termHat D t tb L0 w z .U (2 * l' + 1) zh) := by
  show wc D z 0 * ∑ e ∈ range D.nx,
    Inst.Model.Site.scl (D.Pl (2 * l' + 1)).ku' (el D z 0 (2 * l' + 1)) *
      ∑ j ∈ range D.d, (valU D t .sel l' e zh * valU D t .xr l' j zh) *
        ∑ x ∈ range D.fe, ew D z .U (D.fe + x) * (w (2 * l' + 1)).Eu e j x = _
  rw [tri_sums, scl_pass]
  show _ = wc D z 0 * (el D z 0 (2 * l' + 1) * (if isExpL (2 * l' + 1) then
    Inst.Model.Site.scl (D.Pl (2 * l' + 1)).ku'
      (∑ e ∈ range D.nx, valU D t .sel ((2 * l' + 1) / 2) e zh *
        ∑ j ∈ range D.d, valU D t .xr ((2 * l' + 1) / 2) j zh *
          ∑ x ∈ range D.fe, ew D z .U (D.fe + x) * (w (2 * l' + 1)).Eu e j x) else 0))
  rw [if_pos (odd_hasExp l'), half_odd]

/-- Panel Dr l'. H2 is asked to be the honest vector of the routed gated products at the end point,
at this layer. -/
theorem share_Dr (l' : ℕ)
    (hH : ∀ j, j < D.fe → H2 l' j = hhU D t (2 * l' + 1) (D.fe + j) zh) :
    (Pan.Dr l').share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
      wc D z 1 * (el D z 1 (2 * l' + 1) * termHat D t tb L0 w z .D (2 * l' + 1) zh) := by
  show wc D z 1 * ∑ e ∈ range D.nx,
    Inst.Model.Site.scl (D.Pl (2 * l' + 1)).kd (el D z 1 (2 * l' + 1)) *
      ∑ j ∈ range D.fe, (valU D t .sel l' e zh * H2 l' j) *
        ∑ x ∈ range D.d, ew D z .D x * (w (2 * l' + 1)).Ed e j x = _
  rw [tri_sums, scl_pass]
  show _ = wc D z 1 * (el D z 1 (2 * l' + 1) * (if isExpL (2 * l' + 1) then
    Inst.Model.Site.scl (D.Pl (2 * l' + 1)).kd
      (∑ e ∈ range D.nx, valU D t .sel ((2 * l' + 1) / 2) e zh *
        ∑ j ∈ range D.fe, hhU D t (2 * l' + 1) (D.fe + j) zh *
          ∑ x ∈ range D.d, ew D z .D x * (w (2 * l' + 1)).Ed e j x) else 0))
  rw [if_pos (odd_hasExp l'), half_odd]
  have e : ∀ e, ∑ j ∈ range D.fe, H2 l' j * ∑ x ∈ range D.d, ew D z .D x *
      (w (2 * l' + 1)).Ed e j x = ∑ j ∈ range D.fe, hhU D t (2 * l' + 1) (D.fe + j) zh *
        ∑ x ∈ range D.d, ew D z .D x * (w (2 * l' + 1)).Ed e j x :=
    fun e => sum_congr rfl fun j hj => by rw [hH j (mem_range.mp hj)]
  simp only [e]

/-! ## All late panels -/

/-- The late panels' shares make up the summand of the sumcheck over the positions at its end point,
if the panel QK's share does (hQK). At the true contractions of the cells at the end point zh, with
the honest vector of the routed gated products there: Sig1 is Gpos at zh. -/
theorem sig1_gpos_of
    (hH : ∀ l', l' < D.ne → ∀ j, j < D.fe → H2 l' j = hhU D t (2 * l' + 1) (D.fe + j) zh)
    (hQK : Pan.QK.share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
      wc D z 2 * ∑ l ∈ range D.nl, el D z 2 l * termHat D t tb L0 w z .QK l zh) :
    Sig1 D (rdTrue D t z zh H1 H2) tb L0 w z zh = Gpos D t tb L0 w z zh := by
  have hs : ∀ (c : Fin 8) (l : ℕ), ((famsIn c l).map fun s => termHat D t tb L0 w z s l zh).sum =
      ((nineIn c (isExpL l)).map fun s => termHat D t tb L0 w z s l zh).sum := by
    intro c l
    rw [sum_hat_nine D t tb L0 w z zh l, famsIn_nine]
  -- the blocks of panels with the selector
  have bG : ((List.range D.ne).map fun l' =>
      (Pan.Gr l').share D (rdTrue D t z zh H1 H2) tb L0 w z zh).sum =
      wc D z 0 * ∑ l ∈ range D.nl, el D z 0 l * termHat D t tb L0 w z .G l zh := by
    rw [listRange_sum, sum_oddOnly (fun l => el D z 0 l * termHat D t tb L0 w z .G l zh)
      (fun l h => by simp only [hat_G_even D t tb L0 w z zh h, mul_zero]) D.nl, mul_sum]
    exact sum_congr rfl fun l' _ => share_Gr D t tb L0 w z zh H1 H2 l'
  have bU : ((List.range D.ne).map fun l' =>
      (Pan.Ur l').share D (rdTrue D t z zh H1 H2) tb L0 w z zh).sum =
      wc D z 0 * ∑ l ∈ range D.nl, el D z 0 l * termHat D t tb L0 w z .U l zh := by
    rw [listRange_sum, sum_oddOnly (fun l => el D z 0 l * termHat D t tb L0 w z .U l zh)
      (fun l h => by simp only [hat_U_even D t tb L0 w z zh h, mul_zero]) D.nl, mul_sum]
    exact sum_congr rfl fun l' _ => share_Ur D t tb L0 w z zh H1 H2 l'
  have bD : ((List.range D.ne).map fun l' =>
      (Pan.Dr l').share D (rdTrue D t z zh H1 H2) tb L0 w z zh).sum =
      wc D z 1 * ∑ l ∈ range D.nl, el D z 1 l * termHat D t tb L0 w z .D l zh := by
    rw [listRange_sum, sum_oddOnly (fun l => el D z 1 l * termHat D t tb L0 w z .D l zh)
      (fun l h => by simp only [hat_D_even D t tb L0 w z zh h, mul_zero]) D.nl, mul_sum]
    exact sum_congr rfl fun l' hl => share_Dr D t tb L0 w z zh H1 H2 l' (hH l' (mem_range.mp hl))
  -- the right side, call by call
  have c0 : ∀ l, ((nineIn 0 (isExpL l)).map fun s => termHat D t tb L0 w z s l zh).sum =
      termHat D t tb L0 w z .G l zh + termHat D t tb L0 w z .U l zh := fun l => by
    show _ + (_ + 0) = _
    rw [add_zero]
  have c1 : ∀ l, ((nineIn 1 (isExpL l)).map fun s => termHat D t tb L0 w z s l zh).sum =
      termHat D t tb L0 w z .N1 l zh + termHat D t tb L0 w z .N2 l zh +
        termHat D t tb L0 w z .D l zh := fun l => by
    show _ + (_ + (_ + 0)) = _
    ring
  have c2 : ∑ l ∈ range D.nl, el D z 2 l *
      ((nineIn 2 (isExpL l)).map fun s => termHat D t tb L0 w z s l zh).sum =
      ∑ l ∈ range D.nl, el D z 2 l * termHat D t tb L0 w z .QK l zh +
        (∑ l' ∈ range D.ne, el D z 2 (2 * l' + 1) * termHat D t tb L0 w z .XR (2 * l' + 1) zh +
          ∑ l' ∈ range D.ne, el D z 2 (2 * l' + 1) *
            termHat D t tb L0 w z .DD (2 * l' + 1) zh) := by
    have e : ∀ l, el D z 2 l *
        ((nineIn 2 (isExpL l)).map fun s => termHat D t tb L0 w z s l zh).sum =
        el D z 2 l * termHat D t tb L0 w z .QK l zh + (if l % 2 = 1 then
          el D z 2 l * termHat D t tb L0 w z .XR l zh +
            el D z 2 l * termHat D t tb L0 w z .DD l zh else 0) := by
      intro l
      by_cases h : l % 2 = 1
      · have hb : isExpL l = true := by simp [isExpL, h]
        rw [hb, if_pos h]
        show el D z 2 l * (_ + (_ + (_ + 0))) = _
        ring
      · have hb : isExpL l = false := by simpa using even_noExp h
        rw [hb, if_neg h]
        show el D z 2 l * (_ + 0) = _
        ring
    simp only [e]
    rw [sum_add_distrib, sum_oddOnly _ (fun l h => if_neg h) D.nl, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun l' _ => ?_
    rw [if_pos (by omega)]
  have c5 : ∑ l ∈ range D.nl, el D z 5 l *
      ((nineIn 5 (isExpL l)).map fun s => termHat D t tb L0 w z s l zh).sum =
      ∑ l' ∈ range D.ne, el D z 5 (2 * l' + 1) * termHat D t tb L0 w z .MR (2 * l' + 1) zh := by
    have e : ∀ l, el D z 5 l *
        ((nineIn 5 (isExpL l)).map fun s => termHat D t tb L0 w z s l zh).sum =
        if l % 2 = 1 then el D z 5 l * termHat D t tb L0 w z .MR l zh else 0 := by
      intro l
      by_cases h : l % 2 = 1
      · have hb : isExpL l = true := by simp [isExpL, h]
        rw [hb, if_pos h]
        show el D z 5 l * (_ + 0) = _
        rw [add_zero]
      · have hb : isExpL l = false := by simpa using even_noExp h
        rw [hb, if_neg h]
        show el D z 5 l * 0 = _
        rw [mul_zero]
    simp only [e]
    rw [sum_oddOnly _ (fun l h => if_neg h) D.nl]
    refine sum_congr rfl fun l' _ => ?_
    rw [if_pos (by omega)]
  have cz : ∀ c : Fin 8, c.val = 3 ∨ c.val = 4 ∨ c.val = 6 ∨ c.val = 7 → ∀ l,
      ((nineIn c (isExpL l)).map fun s => termHat D t tb L0 w z s l zh).sum = 0 := by
    intro c hc l
    have e : ∀ b, nineIn c b = [] := by
      revert c
      decide
    rw [e]
    rfl
  unfold Sig1 Gpos
  rw [late_pans D]
  simp only [List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hs, Function.comp_def]
  rw [bG, bU, bD, share_N1, share_N2, hQK, share_XR, share_DD, share_MR, Fin.sum_univ_eight, c2,
    c5]
  simp only [c0, c1, cz 3 (by decide), cz 4 (by decide), cz 6 (by decide), cz 7 (by decide),
    mul_zero, sum_const_zero, mul_add, sum_add_distrib]
  ring

/-- The late panels' shares make up the summand of the sumcheck over the positions at its end point.
At the true contractions of the cells at the point zh, with the honest vector of the routed gated
products there: Sig1 is Gpos at zh. Asked beside: what the panel QK needs of the sizes, and that in
each layer the shifts of queries and keys are equal or both at least 16. -/
theorem sig1_gpos (C : D.ChOK)
    (hk : ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (hH : ∀ l', l' < D.ne → ∀ j, j < D.fe → H2 l' j = hhU D t (2 * l' + 1) (D.fe + j) zh) :
    Sig1 D (rdTrue D t z zh H1 H2) tb L0 w z zh = Gpos D t tb L0 w z zh :=
  sig1_gpos_of D t tb L0 w z zh H1 H2 hH (share_QK D t tb L0 w z zh C H1 H2 hk)

end Shares

#print axioms famsIn_nine
#print axioms share_N1
#print axioms share_Gr
#print axioms share_Dr
#print axioms sig1_gpos_of
#print axioms sig1_gpos

end OnBytes.Road
