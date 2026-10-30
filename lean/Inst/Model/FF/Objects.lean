-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/Objects.lean: the quantities that the claims in the reduction part of a feed-forward
  segment are about, as functions of the witness.

  Words of this library: lean/GLOSSARY.md.
  Mathematics only: no statement types, no stages, no affine forms. Definitions and a few small
  theorems. The claims arise in this order: (1) the end claim of the main lookup argument, split by
  calls; (2) a sumcheck over the positions; (3) the inner-product sumcheck over the panels.
  Every quantity is a function of the cells t (the integers of the segment's execution trace,
  Inst/Model/FF/Trace.lean), mapped into a field E; the weights w of the layers, with entries in E;
  the public tables; and challenges. A key is a looked-up value of one of the segment's eight
  lookups (calls); keys come in families (`key`, `Fam`). The identities (J1) to (J11) are those of
  `Idn`.
  Points are numbered as in Blocks/LookupCalls.lean: a point is a function on ℕ, and coordinate 0
  belongs to the highest bit. The end point of the product tree over the keys is z = (z_in | z_tr),
  with z_in at the coordinates below `Dk D`.
  The sections:
  1. The calls as blocks of batches of looked-up values, their points z_c = (z_c^lay | z_c^col |
     z_pos) and weights w_c; the public weights.
  2. `key_eq`: a key is its affine part (`lin`), plus products of two values at one position
     (`term`), plus matrix products (`mat`). `LINE`, `TERM`, `ACC`: the sums of the three parts
     under the weights. `ClT`: the honest value of the masked scalar Cl. `Gpos`: the summand of the
     sumcheck over the positions at z_pos.
  3. The squares, the products of the normalisations' ledgers (Inst/Model/Common/Ledger.lean), the
     defects of the identities.
  4. The gated products.
  5. The panels (`Pan`): blocks of indices of the vectors `SA`, `SB` of the inner-product sumcheck.
     `Pan.A` and `Pan.B` read contractions of the cells and the vectors Hh1, Hh2 through a record
     `Rd` of values, so that the same expressions serve for the contractions computed from the cells
     (`rdTrue`) and for the entries that the prover has sent.
  6. The end of the inner-product sumcheck; the tensor claims. Then the figures at `Dim.ref`.
  This file has no affine form that denotes `LINE`, and no other file of Inst/ names `LINE`.
  The quantization scales are the instance argument `[scl : Scl]` (Inst/Model/Scl.lean;
  Inst/Model/FF/Index.lean says how they are read). Where this file says "the reference
  parameters", read: the reference sizes and any scales, valid ones where a statement has the
  argument `[Lawful]` (Inst/Model/FF/Lawful.lean). A theorem marked "omit scl in" reads no scale.

  Notation: `Dim.OK`: the conditions on the sizes that the statements of its file need; f = 2 fe is
  its field `f`; G, U, QK, ..: the families of keys (`Fam`); a, m, o, sc, ..: the arrays (`Arr`)
  (Inst/Model/FF/Index.lean); the arrays of the router have the instance ℓ′, which is layer 2ℓ′ + 1
  (`hv`); ν = 2ℓ + n, n = 0 or 1: a norm instance (`npOf`) (Inst/Model/FF/Trace.lean); in this file:
  `zc D z c`: the point z_c of call c; `zpos D z`: z_pos, the last lT coordinates of z_in; `el`,
  `ew`, `wc`: el_c[ℓ] = eq(z_c^lay, ℓ), ew_s[x] = eq(z_c^col, pos_s[x]), the weight w_c; `lin`: the
  affine part of the key of the family s at (ℓ, x, i); `zh`, `rJ`, `pV`: ẑ_pos, ϱ_J, p_V of the
  docstrings; `AipV`, `BipV`: the values of A_ip, B_ip; `PTt`: the honest value of PT.
-/
import Inst.Model.FF.Trace
import Inst.Model.Common.LedgerForms
import Blocks.LookupCalls

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset Blocks
open Site (site high ssite shigh)

variable {E : Type} [Field E] (D : Dim)

/-! ## 1. The calls and the points -/

/-- the point u without its first off coordinates -/
def sh (u : ℕ → E) (off : ℕ) : ℕ → E := fun t => u (off + t)

/-- call c has 2^(eC c) batches of keys -/
def eC (c : Fin 8) : ℕ := aC D c - Dk D
/-- call c as a block of batches -/
def lkCall (c : Fin 8) : LkCall := ⟨eC D c, pre D c⟩
/-- the point z_c of call c: (the last eC c coordinates of z_tr | z_in), with a_c coordinates -/
def zc (z : ℕ → E) (c : Fin 8) (t : ℕ) : E :=
  if t < eC D c then z (Dk D + (sg D - eC D c) + t) else z (t - eC D c)
/-- the weight w_c = eq(the first σ − eC c coordinates of z_tr, pre_c) -/
def wc (z : ℕ → E) (c : Fin 8) : E := eqN (sg D - eC D c) (Dk D) z (pre D c)
/-- z_pos: the last lT coordinates of z_in -/
def zpos (z : ℕ → E) : ℕ → E := sh z (Dk D - D.lT)
/-- el_c[ℓ] = eq(z_c^lay, ℓ) -/
def el (z : ℕ → E) (c : Fin 8) (l : ℕ) : E := eqN D.lL 0 (zc D z c) l
/-- eq(z_c^col, ȷ) -/
def ewc (z : ℕ → E) (c : Fin 8) (jj : ℕ) : E := eqN (lJ D c) D.lL (zc D z c) jj
/-- ew_s[x] = eq(z_c^col, pos_s[x]) -/
def ew (z : ℕ → E) (s : Fam) (x : ℕ) : E := ewc D z (call s) (pos D s x)
/-- the sum of ew_s[x] over the family s -/
def sw (z : ℕ → E) (s : Fam) : E := ∑ x ∈ range (len D s), ew D z s x
/-- PADW_c = Σ_ℓ el_c[ℓ] Σ_ȷ eq(z_c^col, ȷ), the inner sum over the columns that are padding in
layer ℓ -/
def PADW (z : ℕ → E) (c : Fin 8) : E :=
  ∑ l ∈ range D.nl, el D z c l * ∑ jj ∈ range (2 ^ lJ D c), if isPad D c l jj then ewc D z c jj
  else 0
/-- the families of call c that are present in layer ℓ -/
def famsIn (c : Fin 8) (l : ℕ) : List Fam := (fams c).filter (present · l)

section Cells
variable (t : Cell → E) (tb : Tables) (L0 : ℕ) (w : ℕ → LW E)

/-- X̃(inst, j; u) = Σ_i eq(u, i) X[inst, j, i] -/
def valU (X : Arr) (inst j : ℕ) (u : ℕ → E) : E := ext D.lT (fun i => val t X inst j i) u
/-- the same for x_s, state s of the stream -/
def xU (s j : ℕ) (u : ℕ → E) : E := ext D.lT (fun i => xS D t s j i) u
/-- the same for the gated product hh, which "counts as one vector" -/
def hhU (l j : ℕ) (u : ℕ → E) : E := ext D.lT (fun i => hh t l j i) u

/-! ## 2. The parts of a key -/

/-- The affine part of the key of the family s at (ℓ, x, i). -/
def lin : Fam → ℕ → ℕ → ℕ → E
  | .G, l, x, i => ssite 0 (gw t l x i) (val t .rg l x i) (kG D l x)
  | .U, l, x, i => ssite 0 (val t .up l x i) (val t .ru l x i) (kU D l x)
  | .QK, l, x, i => ssite 0 (val t .qkw l x i) (val t .rqk l x i) (kQK D l x)
  | .N1, l, x, i => site 0 (val t .aw l x i) (val t .ra l x i) (D.Pl l).n1.K
  | .N2, l, x, i => site 0 (val t .mw l x i) (val t .rm l x i) (D.Pl l).n2.K
  | .O, l, x, i => ssite 0 (xS D t (2 * l + 1) x i - xS D t (2 * l) x i) (val t .ro l x i) (D.Pl l).ko
  | .D, l, x, i => ssite 0 (xS D t (2 * l + 2) x i - xS D t (2 * l + 1) x i) (val t .rd l x i) (D.Pl l).kd
  | .V, l, x, i => ssite 0 (val t .vw l x i) (val t .rv l x i) (D.Pl l).kv
  | .LR, l, x, i => ssite 0 (lw t (l / 2) x i) (val t .rl (l / 2) x i) (D.Pl l).kr
  | .XR, l, x, i => 2 ^ 15 - 2 ^ 16 * val t .xr (l / 2) x i
  | .DD, l, x, i => -val t .lr (l / 2) x i - ∑ e ∈ (range D.nx).filter (x < ·), val t .sel (l / 2) e i
  | .MR, l, _, i => 2 ^ 14 + 2 ^ 17 * val t .sc (l / 2) 0 i
  | s, l, x, i => key D t tb L0 w s l x i

/-- The part of the key that is a sum of products of two values at the position i (before the sum
over x). In the case D, hh counts as one value. -/
def term : Fam → ℕ → ℕ → ℕ → E
  | .N1, l, x, i => xS D t (2 * l) x i * Ledger.R (led t (2 * l) i)
  | .N2, l, x, i => xS D t (2 * l + 1) x i * Ledger.R (led t (2 * l + 1) i)
  | .QK, l, x, i => Site.scl (kQK D l x) (Y' D t tb L0 w l x i)
  | .XR, l, x, i => val t .sc (l / 2) 0 i * val t .m l x i
  | .DD, l, _, i => mr D t (l / 2) i
  | .MR, l, _, i => mr D t (l / 2) i
  | .G, l, x, i => if routed D l x then Site.scl (D.Pl l).kg' (Ag D t w l x i) else 0
  | .U, l, x, i => if routed D l x then Site.scl (D.Pl l).ku' (Au D t w l x i) else 0
  | .D, l, x, i =>
    if isExpL l then
      Site.scl (D.Pl l).kd
        (∑ e ∈ range D.nx,
          val t .sel (l / 2) e i * ∑ j ∈ range D.fe, hh t l (D.fe + j) i * (w l).Ed e j x)
    else 0
  | _, _, _, _ => 0

/-- The part of the key that is a matrix product of a vector of values at the position i with a
weight matrix (before the sums over x and i). -/
def mat : Fam → ℕ → ℕ → ℕ → E
  | .G, l, x, i => if routed D l x then 0 else Site.scl (D.Pl l).kg (Ag D t w l x i)
  | .U, l, x, i => if routed D l x then 0 else Site.scl (D.Pl l).ku (Au D t w l x i)
  | .V, l, x, i => Site.scl (D.Pl l).kv (Av D t w l x i)
  | .O, l, x, i => Site.scl (D.Pl l).ko (∑ j ∈ range D.dq, val t .o l j i * (w l).Wo j x)
  | .LR, l, x, i => Site.scl (D.Pl l).kr (∑ j ∈ range D.d, val t .m l j i * (w l).Wr j x)
  | .D, l, x, i => Site.scl (D.Pl l).kd (∑ j ∈ range (if isExpL l then D.fe else D.f), hh t l j i * (w l).Wd j x)
  | _, _, _, _ => 0

/-- A key is the sum of its three parts. -/
theorem key_eq (s : Fam) (l x i : ℕ) :
    key D t tb L0 w s l x i =
      lin D t tb L0 w s l x i + term D t tb L0 w s l x i + mat D t w s l x i := by
  cases s <;> simp only [key, lin, term, mat, site, Ad, kG, kU, Site.ssite_eq, Site.scl_eq]
    <;> (try split_ifs) <;> ring

/-- LINE_s(ℓ) = Σ_x ew_s[x] Σ_i eq(z_pos, i) lin_s(ℓ, x, i) -/
def LINE (z : ℕ → E) (s : Fam) (l : ℕ) : E :=
  ∑ x ∈ range (len D s), ew D z s x * ext D.lT (fun i => lin D t tb L0 w s l x i) (zpos D z)
/-- TERM_s(ℓ, i) = Σ_x ew_s[x] term_s(ℓ, x, i) -/
def TERM (z : ℕ → E) (s : Fam) (l i : ℕ) : E :=
  ∑ x ∈ range (len D s), ew D z s x * term D t tb L0 w s l x i
/-- ACC_s(ℓ) = Σ_x ew_s[x] Σ_i eq(z_pos, i) mat_s(ℓ, x, i) -/
def ACC (z : ℕ → E) (s : Fam) (l : ℕ) : E :=
  ∑ x ∈ range (len D s), ew D z s x * ext D.lT (fun i => mat D t w s l x i) (zpos D z)
/-- TS_c = Σ_i eq(z_pos, i) Σ_ℓ el_c[ℓ] Σ_(s ∈ c) TERM_s(ℓ, i) -/
def TS (z : ℕ → E) (c : Fin 8) : E :=
  ext D.lT (fun i =>
      ∑ l ∈ range D.nl, el D z c l * ((famsIn c l).map fun s => TERM D t tb L0 w z s l i).sum)
    (zpos D z)
/-- KF_c = pad_c PADW_c + TS_c + Σ_ℓ el_c[ℓ] Σ_(s ∈ c) (LINE_s(ℓ) + ACC_s(ℓ)); pad_c: the table's
padding value -/
def KF (z : ℕ → E) (c : Fin 8) : E :=
  (((lut tb c).pad : ℤ) : E) * PADW D z c + TS D t tb L0 w z c +
    ∑ l ∈ range D.nl,
      el D z c l * ((famsIn c l).map fun s => LINE D t tb L0 w z s l + ACC D t w z s l).sum
/-- the honest value of the masked scalar Cl = Σ_c w_c TS_c -/
def ClT (z : ℕ → E) : E := ∑ c, wc D z c * TS D t tb L0 w z c

/-- the extension of AY_x at X, which is linear in the extensions of a -/
def AYU (l x : ℕ) (X : ℕ → E) : E :=
  if x < D.dq then ∑ j ∈ range D.d, valU D t .a l j X * (w l).Wq j x
  else ∑ j ∈ range D.d, valU D t .a l j X * (w l).Wk j (x - D.dq)
/-- the extensions of the rotary tables of layer L0 + ℓ at ȷ -/
def Ct (l jj : ℕ) (X : ℕ → E) : E := ext D.lT (fun i => ((tb.C (L0 + l) i jj : ℤ) : E)) X
def St (l jj : ℕ) (X : ℕ → E) : E := ext D.lT (fun i => ((tb.S (L0 + l) i jj : ℤ) : E)) X

/-- TERM_s(ℓ, ·) as a polynomial in X ∈ E^lT: the same sum with each of the two vectors of a product
replaced by its multilinear extension. The pairs are (R_ν, x_ν[x]); (a rotary table, a[j]); (sc,
m[x]); (sel_e, lr_e); (sel_e, xr[j]); (sel_e, hh[fe + j]). -/
def termHat (z : ℕ → E) : Fam → ℕ → (ℕ → E) → E
  | .N1, l, X =>
    ext D.lT (fun i => Ledger.R (led t (2 * l) i)) X *
      ∑ x ∈ range D.d, ew D z .N1 x * xU D t (2 * l) x X
  | .N2, l, X =>
    ext D.lT (fun i => Ledger.R (led t (2 * l + 1) i)) X *
      ∑ x ∈ range D.d, ew D z .N2 x * xU D t (2 * l + 1) x X
  | .QK, l, X =>
    ∑ x ∈ range D.dqk, ew D z .QK x *
      Site.scl (kQK D l x)
        (if (x % D.P.ch) % 2 = 0 then
            Ct D tb L0 l (x % D.P.ch / 2) X * AYU D t w l x X -
              St D tb L0 l (x % D.P.ch / 2) X * AYU D t w l (x + 1) X
          else
            St D tb L0 l (x % D.P.ch / 2) X * AYU D t w l (x - 1) X +
              Ct D tb L0 l (x % D.P.ch / 2) X * AYU D t w l x X)
  | .XR, l, X => valU D t .sc (l / 2) 0 X * ∑ x ∈ range D.d, ew D z .XR x * valU D t .m l x X
  | .DD, l, X => sw D z .DD * ∑ e ∈ range D.nx, valU D t .sel (l / 2) e X * valU D t .lr (l / 2) e X
  | .MR, l, X =>
    ew D z .MR 0 * ∑ e ∈ range D.nx, valU D t .sel (l / 2) e X * valU D t .lr (l / 2) e X
  | .G, l, X =>
    if isExpL l then
      Site.scl (D.Pl l).kg'
        (∑ e ∈ range D.nx, valU D t .sel (l / 2) e X *
          ∑ j ∈ range D.d,
            valU D t .xr (l / 2) j X * ∑ x ∈ range D.fe, ew D z .G (D.fe + x) * (w l).Eg e j x)
    else 0
  | .U, l, X =>
    if isExpL l then
      Site.scl (D.Pl l).ku'
        (∑ e ∈ range D.nx, valU D t .sel (l / 2) e X *
          ∑ j ∈ range D.d,
            valU D t .xr (l / 2) j X * ∑ x ∈ range D.fe, ew D z .U (D.fe + x) * (w l).Eu e j x)
    else 0
  | .D, l, X =>
    if isExpL l then
      Site.scl (D.Pl l).kd
        (∑ e ∈ range D.nx, valU D t .sel (l / 2) e X *
          ∑ j ∈ range D.fe, hhU D t l (D.fe + j) X * ∑ x ∈ range D.d, ew D z .D x * (w l).Ed e j x)
    else 0
  | _, _, _ => 0

/-- G_pos(X) = Σ_c w_c Σ_ℓ el_c[ℓ] Σ_(s ∈ c) TERM_s(ℓ, X). It needs f = 2 fe: the routed units of a
layer are the units fe, .., f − 1 in TERM and fe, .., 2 fe − 1 in G_pos. -/
def Gpos (z X : ℕ → E) : E :=
  ∑ c, wc D z c *
    ∑ l ∈ range D.nl, el D z c l * ((famsIn c l).map fun s => termHat D t tb L0 w z s l X).sum

/-! ## 3. The identities -/

/-- the number of bits of a channel index of the stream -/
def lDd : ℕ := Nat.clog 2 D.d

/-- P[(ν | j | i)] = Σ_l γ^l b_l[ν, j, i] for j < d, and 0 for the other j -/
def Pv (γ : E) (X : ℕ) : E :=
  if X / D.T % 2 ^ lDd D < D.d then
    ∑ l ∈ range 5, γ ^ l * bS D t (X / D.T / 2 ^ lDd D) l (X / D.T % 2 ^ lDd D) (X % D.T)
  else 0
/-- the honest vector H_V[(ν | j)] = Σ_i eq(p_V, i) P[(ν | j | i)]² -/
def HVt (pV : ℕ → E) (γ : E) (Y : ℕ) : E := ext D.lT (fun i => Pv D t γ (Y * D.T + i) ^ 2) pV
/-- the honest value of W_(ν,s) -/
def Wt (pV : ℕ → E) (ν s : ℕ) : E :=
  ext D.lT (fun i => Ledger.Wsum D.d (fun l j => bS D t ν l j i) s) pV
/-- the honest value of pv_(ν,n): the n-th product of row values, summed over the positions under
eq(p_V, ·) -/
def pvt (pV : ℕ → E) (ν n : ℕ) : E := ext D.lT (fun i => Ledger.prods (led t ν i) n) pV
/-- G^V(X) = Σ_ν Σ_n ω_(ν,n) Π̃_n[ν](X): products of the extensions of the two factors -/
def GV (ω : ℕ → ℕ → E) (X : ℕ → E) : E :=
  ∑ ν ∈ range D.nNu, ∑ n ∈ range 7, ω ν n *
    Ledger.prodsOf (ext D.lT (fun i => Ledger.sa (led t ν i)) X)
      (ext D.lT (fun i => Ledger.sb (led t ν i)) X) (ext D.lT (fun i => Ledger.Rlo (led t ν i)) X)
      (ext D.lT (fun i => Ledger.Rhi (led t ν i)) X) n
/-- the defects of (J1) to (J9), number k < 17, and of (J10), as functions of the position -/
def dJ (k ν i : ℕ) : E :=
  Ledger.idn (npOf D ν) (Ledger.Wsum D.d fun l j => bS D t ν l j i) (led t ν i) k
def d10 (l' i : ℕ) : E := ∑ e ∈ range D.nx, val t .sel l' e i - 1

/-! ## 4. The gated products -/

/-- the numbers of bits of the index of a hidden unit of a layer, and of one expert -/
def lF : ℕ := Nat.clog 2 D.f
def lFe : ℕ := Nat.clog 2 D.fe

/-- f0 = −sl and f1 = −up over (ℓ | j | i) -/
def slV (X : ℕ) : E := -val t .sl (X / D.T / 2 ^ lF D) (X / D.T % 2 ^ lF D) (X % D.T)
def upV (X : ℕ) : E := -val t .up (X / D.T / 2 ^ lF D) (X / D.T % 2 ^ lF D) (X % D.T)
/-- the honest Hh1[(ℓ | j)] = Σ_i eq(z_pos, i) hh[ℓ, j, i] -/
def Hh1t (u : ℕ → E) (Y : ℕ) : E := hhU D t (Y / 2 ^ lF D) (Y % 2 ^ lF D) u
/-- f0 = −sl′ and f1 = −up′ over (ℓ′ | j | i): sl, up on the routed hidden units -/
def slV' (X : ℕ) : E :=
  -val t .sl (2 * (X / D.T / 2 ^ lFe D) + 1) (D.fe + X / D.T % 2 ^ lFe D) (X % D.T)
def upV' (X : ℕ) : E :=
  -val t .up (2 * (X / D.T / 2 ^ lFe D) + 1) (D.fe + X / D.T % 2 ^ lFe D) (X % D.T)
/-- the honest Hh2[(ℓ′ | j)] = Σ_i eq(ẑ_pos, i) hh[2ℓ′ + 1, fe + j, i] -/
def Hh2t (u : ℕ → E) (Y : ℕ) : E := hhU D t (2 * (Y / 2 ^ lFe D) + 1) (D.fe + Y % 2 ^ lFe D) u

end Cells

/-! ## 5. The panels of the inner-product sumcheck -/

/-- The values that the panels read: contractions of cells at z_pos (m1, a1, o1) and at ẑ_pos (R2 of
a norm instance; a2, sc2, m2, sel2, lr2, xr2), the entries of Hh1, Hh2, and xF ν = Σ_x ew_s[x]
x̃_ν[x](ẑ_pos), s = N1 or N2: the stream is read through block reads, which give this sum and not
its terms. The first index is the instance. -/
structure Rd (E : Type) where
  m1 : ℕ → ℕ → E
  a1 : ℕ → ℕ → E
  o1 : ℕ → ℕ → E
  hh1 : ℕ → ℕ → E
  R2 : ℕ → E
  xF : ℕ → E
  a2 : ℕ → ℕ → E
  sc2 : ℕ → E
  m2 : ℕ → ℕ → E
  sel2 : ℕ → ℕ → E
  lr2 : ℕ → ℕ → E
  xr2 : ℕ → ℕ → E
  hh2 : ℕ → ℕ → E

/-- the contractions computed from the cells, at z_pos and at u' = ẑ_pos, with given vectors Hh1,
Hh2 -/
def rdTrue (t : Cell → E) (z u' : ℕ → E) (H1 H2 : ℕ → ℕ → E) : Rd E where
  m1 l j := valU D t .m l j (zpos D z)
  a1 l j := valU D t .a l j (zpos D z)
  o1 l j := valU D t .o l j (zpos D z)
  hh1 := H1
  R2 ν := ext D.lT (fun i => Ledger.R (led t ν i)) u'
  xF ν := ∑ x ∈ range D.d, ew D z (if ν % 2 = 0 then .N1 else .N2) x * xU D t ν x u'
  a2 l j := valU D t .a l j u'
  sc2 l' := valU D t .sc l' 0 u'
  m2 l j := valU D t .m l j u'
  sel2 l' e := valU D t .sel l' e u'
  lr2 l' e := valU D t .lr l' e u'
  xr2 l' j := valU D t .xr l' j u'
  hh2 := H2

/-- The panels, sorted into kinds 1 to 11; these numbers only link one comment to another. G, U, O,
D, V, LR are the kinds 1, 1, 3, 4, 2, 5; Gr ℓ′, Ur ℓ′ kind 10; N1, N2 kind 6; Dr ℓ′ kind 11; QK, XR
kinds 7, 8; DD, MR kind 9. -/
inductive Pan
  | G | U | O | D | V | LR | Gr (l' : ℕ) | Ur (l' : ℕ) | N1 | N2 | Dr (l' : ℕ) | QK | XR | DD | MR
  deriving DecidableEq, Repr

/-- the list order of the panels -/
def pans : List Pan :=
  [.G, .U, .O, .D, .V, .LR] ++ (List.range D.ne).map .Gr ++ (List.range D.ne).map .Ur ++
    [.N1, .N2] ++ (List.range D.ne).map .Dr ++ [.QK, .XR, .DD, .MR]

namespace Pan

/-- the family to which a panel belongs -/
def fam : Pan → Fam
  | .G | .Gr _ => .G
  | .U | .Ur _ => .U
  | .O => .O
  | .D | .Dr _ => .D
  | .V => .V
  | .LR => .LR
  | .N1 => .N1
  | .N2 => .N2
  | .QK => .QK
  | .XR => .XR
  | .DD => .DD
  | .MR => .MR

/-- ω_p = ϱ_J: the kinds 6 to 11 -/
def late : Pan → Bool
  | .G | .U | .O | .D | .V | .LR => false
  | _ => true

/-- the three-factor panels: the kinds 10 and 11 -/
def three : Pan → Bool
  | .Gr _ | .Ur _ | .Dr _ => true
  | _ => false

/-- the weight panels: the kinds 1 to 5, 7, 10, 11 -/
def weight : Pan → Bool
  | .N1 | .N2 | .XR | .DD | .MR => false
  | _ => true

variable (D : Dim)

/-- the numbers of rows and of columns of a panel -/
def nr : Pan → ℕ
  | .G | .U | .O | .D | .V | .N1 | .N2 | .QK => D.nl
  | .LR | .XR | .DD | .MR => D.ne
  | .Gr _ | .Ur _ | .Dr _ => D.nx
def nc : Pan → ℕ
  | .G | .U | .V | .LR | .QK | .Gr _ | .Ur _ => D.d
  | .O => D.dq
  | .D => D.f
  | .Dr _ => D.fe
  | .DD | .MR => D.nx
  | .N1 | .N2 | .XR => 1

/-- the numbers of bits w_c = ⌈log2 n_c⌉ of a column and w = ⌈log2 n_r⌉ + w_c of an entry of a panel
(this w_c is not the weight of a call) -/
def wcol (p : Pan) : ℕ := Nat.clog 2 (p.nc D)
def wid (p : Pan) : ℕ := Nat.clog 2 (p.nr D) + p.wcol D

end Pan

/-- off_p: the panels are sorted by w, largest first, panels of equal w in list order, and placed
end to end from 0 -/
def offP (p : Pan) : ℕ :=
  ((pans D).map fun q =>
    if p.wid D < q.wid D ∨ (q.wid D = p.wid D ∧ (pans D).idxOf q < (pans D).idxOf p) then
      2 ^ q.wid D
    else 0).sum
/-- the number of indices that the panels occupy, and λ_S, the number of bits of an index -/
def panTotal : ℕ := ((pans D).map fun q => 2 ^ q.wid D).sum
def lamS : ℕ := Nat.clog 2 (panTotal D)

section Panels
variable (r : Rd E) (tb : Tables) (L0 : ℕ) (w : ℕ → LW E) (z zh : ℕ → E)

/-- the number of hidden units of layer ℓ that are not routed -/
def fSh (l : ℕ) : ℕ := if isExpL l then D.fe else D.f

/-- A(ρ, ι), the first factor at row ρ and column ι of a panel -/
def Pan.A : Pan → ℕ → ℕ → E
  | .G, l, j | .U, l, j => r.m1 l j
  | .V, l, j => r.a1 l j
  | .O, l, j => r.o1 l j
  | .D, l, j => if j < fSh D l then r.hh1 l j else 0
  | .LR, l', j => r.m1 (2 * l' + 1) j
  | .N1, l, _ => r.R2 (2 * l)
  | .N2, l, _ => r.R2 (2 * l + 1)
  | .QK, l, j => r.a2 l j
  | .XR, l', _ => r.sc2 l'
  | .DD, l', e | .MR, l', e => r.sel2 l' e
  | .Gr l', e, j | .Ur l', e, j => r.sel2 l' e * r.xr2 l' j
  | .Dr l', e, j => r.sel2 l' e * r.hh2 l' j

/-- wt_ρ, the weight of row ρ. In a panel of a matrix product with the shift k it has the factor
2^dn(k), dn(k) = max(0, 16 − k) (`Site.scl`): the scaled remainder of a rounding contains the
accumulator with this factor. For QK the factor is 2^dn(kq); it is that of kk too under `Dim.QKOne`
(Inst/Model/FF/Index.lean). -/
def Pan.wt : Pan → ℕ → E
  | .G, l => Site.scl (D.Pl l).kg (el D z (call .G) l)
  | .U, l => Site.scl (D.Pl l).ku (el D z (call .U) l)
  | .O, l => Site.scl (D.Pl l).ko (el D z (call .O) l)
  | .D, l => Site.scl (D.Pl l).kd (el D z (call .D) l)
  | .V, l => Site.scl (D.Pl l).kv (el D z (call .V) l)
  | .QK, l => Site.scl (D.Pl l).kq (el D z (call .QK) l)
  | .LR, l' => Site.scl (D.Pl (2 * l' + 1)).kr (el D z (call .LR) (2 * l' + 1))
  | .XR, l' => el D z (call .XR) (2 * l' + 1)
  | .DD, l' => el D z (call .DD) (2 * l' + 1) * sw D z .DD
  | .MR, l' => el D z (call .MR) (2 * l' + 1) * ew D z .MR 0
  | .Gr l', _ => Site.scl (D.Pl (2 * l' + 1)).kg' (el D z (call .G) (2 * l' + 1))
  | .Ur l', _ => Site.scl (D.Pl (2 * l' + 1)).ku' (el D z (call .U) (2 * l' + 1))
  | .Dr l', _ => Site.scl (D.Pl (2 * l' + 1)).kd (el D z (call .D) (2 * l' + 1))
  | p, l => el D z (call p.fam) l

/-- the number of bits of a channel index of a head -/
def lch : ℕ := Nat.log2 D.P.ch
/-- AH[h] = eq(z_c^col without its last lch coordinates, pos_QK[ch h] / ch); lf[x″] = eq(the last
lch coordinates of z_c^col, x″) -/
def AH (h : ℕ) : E :=
  eqN (lJ D (call .QK) - lch D) D.lL (zc D z (call .QK)) (pos D .QK (D.P.ch * h) / D.P.ch)
def lf (x : ℕ) : E := eqN (lch D) (D.lL + (lJ D (call .QK) - lch D)) (zc D z (call .QK)) x
/-- kp_ℓ[2ȷ] = Ct_ℓ[ȷ] lf[2ȷ] + St_ℓ[ȷ] lf[2ȷ + 1], kp_ℓ[2ȷ + 1] = Ct_ℓ[ȷ] lf[2ȷ + 1] − St_ℓ[ȷ]
lf[2ȷ], with the tables contracted at ẑ_pos -/
def kp (l x : ℕ) : E :=
  if x % 2 = 0 then Ct D tb L0 l (x / 2) zh * lf D z x + St D tb L0 l (x / 2) zh * lf D z (x + 1)
  else Ct D tb L0 l (x / 2) zh * lf D z x - St D tb L0 l (x / 2) zh * lf D z (x - 1)
/-- W_qk[j][(h, x″)] -/
def Wqk (l j h x : ℕ) : E :=
  if h < D.P.nq then (w l).Wq j (D.P.ch * h + x) else (w l).Wk j (D.P.ch * (h - D.P.nq) + x)

/-- B(ρ, ι), the second factor at row ρ and column ι of a panel -/
def Pan.B : Pan → ℕ → ℕ → E
  | .G, l, j => ∑ x ∈ range (fSh D l), ew D z .G x * (w l).Wg j x
  | .U, l, j => ∑ x ∈ range (fSh D l), ew D z .U x * (w l).Wu j x
  | .V, l, j => ∑ x ∈ range D.dkv, ew D z .V x * (w l).Wv j x
  | .O, l, j => ∑ x ∈ range D.d, ew D z .O x * (w l).Wo j x
  | .D, l, j => if j < fSh D l then ∑ x ∈ range D.d, ew D z .D x * (w l).Wd j x else 0
  | .LR, l', j => ∑ x ∈ range D.nx, ew D z .LR x * (w (2 * l' + 1)).Wr j x
  | .N1, l, _ => r.xF (2 * l)
  | .N2, l, _ => r.xF (2 * l + 1)
  | .QK, l, j => ∑ h ∈ range (D.P.nq + D.P.nkv), ∑ x ∈ range D.P.ch, AH D z h * kp D tb L0 z zh l x * Wqk D w l j h x
  | .XR, l', _ => ∑ x ∈ range D.d, ew D z .XR x * r.m2 (2 * l' + 1) x
  | .DD, l', e | .MR, l', e => r.lr2 l' e
  | .Gr l', e, j => ∑ x ∈ range D.fe, ew D z .G (D.fe + x) * (w (2 * l' + 1)).Eg e j x
  | .Ur l', e, j => ∑ x ∈ range D.fe, ew D z .U (D.fe + x) * (w (2 * l' + 1)).Eu e j x
  | .Dr l', e, j => ∑ x ∈ range D.d, ew D z .D x * (w (2 * l' + 1)).Ed e j x

/-- ω_p: ϱ_J for the kinds 6 to 11, else 1 -/
def Pan.om (rJ : E) (p : Pan) : E := if p.late then rJ else 1

/-- (ρ, ι) if the index y is that entry of the panel p; else none -/
def Pan.at (p : Pan) (y : ℕ) : Option (ℕ × ℕ) :=
  if offP D p ≤ y ∧
      y < offP D p + 2 ^ p.wid D ∧
      (y - offP D p) / 2 ^ p.wcol D < p.nr D ∧
      (y - offP D p) % 2 ^ p.wcol D < p.nc D then
    some ((y - offP D p) / 2 ^ p.wcol D, (y - offP D p) % 2 ^ p.wcol D)
  else none

/-- S_A[y] = ω_p w_c wt_ρ A(ρ, ι) and S_B[y] = B(ρ, ι) at an entry of a panel; 0 everywhere else -/
def SA (rJ : E) (y : ℕ) : E :=
  ((pans D).map fun p =>
    match p.at D y with
    | some (ρ, ι) => p.om rJ * wc D z (call p.fam) * p.wt D z ρ * p.A D r ρ ι
    | none => 0).sum
def SB (y : ℕ) : E :=
  ((pans D).map fun p =>
    match p.at D y with | some (ρ, ι) => p.B D r tb L0 w z zh ρ ι | none => 0).sum

/-- the share of a panel in Σ_y S_A[y] S_B[y], without ω_p -/
def Pan.share (p : Pan) : E :=
  wc D z (call p.fam) *
    ∑ ρ ∈ range (p.nr D), p.wt D z ρ * ∑ ι ∈ range (p.nc D), p.A D r ρ ι * p.B D r tb L0 w z zh ρ ι
/-- Σ_0: the kinds 1 to 5; Σ_1: the kinds 6 to 11 -/
def Sig0 : E := (((pans D).filter fun p => !p.late).map fun p => p.share D r tb L0 w z zh).sum
def Sig1 : E := (((pans D).filter fun p => p.late).map fun p => p.share D r tb L0 w z zh).sum

/-! ## 6. The end of the inner-product sumcheck -/

variable (ζ : ℕ → E)

/-- ζ = (ζ^hi | ζ^r | ζ^c): b_p = eq(ζ^hi, off_p / 2^w), Er[ρ] = eq(ζ^r, ρ), Ec[ι] = eq(ζ^c, ι) -/
def Pan.bP (p : Pan) : E := eqN (lamS D - p.wid D) 0 ζ (offP D p / 2 ^ p.wid D)
def Pan.Er (p : Pan) (ρ : ℕ) : E := eqN (p.wid D - p.wcol D) (lamS D - p.wid D) ζ ρ
def Pan.Ec (p : Pan) (ι : ℕ) : E := eqN (p.wcol D) (lamS D - p.wcol D) ζ ι

/-- the value of tensor claim a(p, ρ): Σ_ι Ec[ι] B(ρ, ι); of a(p), for a three-factor panel: Σ_(e,ι)
Er[e] Ec[ι] B(e, ι) -/
def Pan.TnRow (p : Pan) (ρ : ℕ) : E := ∑ ι ∈ range (p.nc D), p.Ec D ζ ι * p.B D r tb L0 w z zh ρ ι
def Pan.TnPan (p : Pan) : E := ∑ e ∈ range (p.nr D), p.Er D ζ e * p.TnRow D r tb L0 w z zh ζ e

/-- SE_p, XE_p and c_p of a three-factor panel -/
def Pan.SE : Pan → E
  | .Gr l' => ∑ e ∈ range D.nx, (Pan.Gr l').Er D ζ e * r.sel2 l' e
  | .Ur l' => ∑ e ∈ range D.nx, (Pan.Ur l').Er D ζ e * r.sel2 l' e
  | .Dr l' => ∑ e ∈ range D.nx, (Pan.Dr l').Er D ζ e * r.sel2 l' e
  | _ => 0
def Pan.XE : Pan → E
  | .Gr l' => ∑ j ∈ range D.d, (Pan.Gr l').Ec D ζ j * r.xr2 l' j
  | .Ur l' => ∑ j ∈ range D.d, (Pan.Ur l').Ec D ζ j * r.xr2 l' j
  | .Dr l' => ∑ j ∈ range D.fe, (Pan.Dr l').Ec D ζ j * r.hh2 l' j
  | _ => 0
def Pan.cP (rJ : E) (p : Pan) : E := p.bP D ζ * rJ * wc D z (call p.fam) * p.wt D z 0

/-- the honest value of PT = Σ_p c_p SE_p XE_p, over the three-factor panels -/
def PTt (rJ : E) : E :=
  (((pans D).filter Pan.three).map fun p => p.cP D z ζ rJ * p.SE D r ζ * p.XE D r ζ).sum

/-- the value of A_ip, with PT for the share of the three-factor panels -/
def AipV (rJ PT : E) : E :=
  (((pans D).filter fun p => !p.three).map fun p =>
      p.bP D ζ * p.om rJ * wc D z (call p.fam) *
        ∑ ρ ∈ range (p.nr D),
          p.wt D z ρ * p.Er D ζ ρ * ∑ ι ∈ range (p.nc D), p.Ec D ζ ι * p.A D r ρ ι).sum + PT

/-- the value of B_ip, with va p ρ for the tensor claims (ρ = 0 for a three-factor panel) -/
def BipV (va : Pan → ℕ → E) : E :=
  ((pans D).map fun p =>
    if p.three then p.bP D ζ * va p 0
    else if p.weight then p.bP D ζ * ∑ ρ ∈ range (p.nr D), p.Er D ζ ρ * va p ρ
    else p.bP D ζ * ∑ ρ ∈ range (p.nr D), p.Er D ζ ρ * p.TnRow D r tb L0 w z zh ζ ρ).sum

end Panels

/-- The conditions on the sizes that the panel QK needs: the number of channels of a head is a power
of two, it is even, and a head fits into the columns of the call. Then ew_QK[ch h + x″] = AH[h]
lf[x″], and the pairs (2ȷ, 2ȷ + 1) of the rotary embedding stay inside a head. -/
structure Dim.ChOK : Prop where
  pow : D.P.ch = 2 ^ lch D
  two : 1 ≤ lch D
  col : lch D ≤ lJ D (call .QK)

omit scl in
theorem ref_chOK : Dim.ref.ChOK := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## The reference parameters (`Dim.ref`): the figures of the panels -/

omit scl in
/-- 18 panels, which take 6,537,738 indices; λ_S = 23. -/
theorem ref_panels :
    (pans Dim.ref).length = 18 ∧ panTotal Dim.ref = 6537738 ∧ lamS Dim.ref = 23 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

omit scl in
/-- all six three-factor panels have w = 20 and w_c = 13 -/
theorem ref_three :
    ((pans Dim.ref).filter Pan.three).map (fun p => (p.wid Dim.ref, p.wcol Dim.ref)) =
      List.replicate 6 (20, 13) := by decide +kernel

omit scl in
/-- 32 tensor claims: one for each row of a weight panel with two factors, one for each three-factor
panel -/
theorem ref_tensor :
    (((pans Dim.ref).filter Pan.weight).map fun p => if p.three then 1 else p.nr Dim.ref).sum =
      32 := by decide +kernel

end Inst.Model.FFSeg
