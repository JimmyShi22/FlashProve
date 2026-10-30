-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Program.lean: the integer model, the computation that the proofs are about, and the
relation `Rinf` between weights, tokens and the next token.

Definitions and one small lemma; imports Mathlib only.
The sizes in `ppref` are those of the text model of Llama 4 Maverick, at a window of 1,024 positions
chosen by this project; the scales in `ppref` are the library's reference scales, which may depend
on Llama 2 7B and Llama 4 Maverick; their origin: THIRD_PARTY.md (What depends on Meta's models).
Source: the definitions follow, step by step, a paper of this project that is not part of this
repository.
Text in double quotes is quoted from that paper and cannot be checked without it. Labels such as
(N1), (PL5), (PA3) are its names for the steps; here they only link one docstring to another.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Int.Order.Basic

set_option autoImplicit false

namespace Inst.Model

/-! ## How the program is written

Every intermediate value is a total function of the weights and the tokens. The range conditions, at
which the paper's program "halts without output", are collected in `Runs` and `RunsK`.
Arrays are functions on natural numbers; at the sizes of `ppref` only the entries below the stated
sizes are read. `Fit2` and `Fit3` are two further bounds on intermediate values, which no relation
of this library uses.
The program is written twice: `X`, `lg`, `Runs`, `Rinf` with one set of scales for all layers, as in
the paper, and `XK`, `lgK`, `RunsK`, `RinfK` with scales for each layer.
The soundness theorems use the second, through the relations of Inst/Model/ProgramR.lean.
Differences from the paper are stated where they occur. The largest: `Instance` has two more fields,
the numbers r and e of a request, which `Rinf` and `RinfK` do not read.
The others: the field `sh` of `Params` in step (PA3); `expRows` in place of 2,307; well-formedness
in the type `Index`; the second form, with scales for each layer.
-/

abbrev Vec : Type := ℕ → ℤ
abbrev Mat : Type := ℕ → ℕ → ℤ

/-! ## Functions on integers. On ℤ, "/" and "%" by a positive number are ⌊·/·⌋ and the remainder in
[0, ·). -/

/-- "rhu(a, k) = ⌊(a + 2^(k−1)) / 2^k⌋, the quotient by 2^k rounded to the nearest integer, halves
up"; k ≥ 1. -/
def rhu (a : ℤ) (k : ℕ) : ℤ := (a + 2 ^ (k - 1)) / 2 ^ k
/-- "clamp_c(a) = min(max(a, −c), c)" -/
def clamp (c a : ℤ) : ℤ := min (max a (-c)) c
/-- "isqrt(v) is the greatest integer whose square is at most v"; v ≥ 0. -/
def isqrt (v : ℤ) : ℤ := (Nat.sqrt v.toNat : ℤ)
/-- "the balanced low byte of a is ((a + 128) mod 256) − 128" -/
def lowByte (a : ℤ) : ℤ := (a + 128) % 256 - 128
/-- "a fits 16 bits if −2^15 ≤ a < 2^15" -/
def Fits16 (a : ℤ) : Prop := -2 ^ 15 ≤ a ∧ a < 2 ^ 15
/-- Σ_{j<n} a[j] b[j] -/
def dot (n : ℕ) (a b : Vec) : ℤ := ∑ j ∈ Finset.range n, a j * b j
/-- max_{j ≤ n} f(j) -/
def maxTo (f : Vec) : ℕ → ℤ
  | 0 => f 0
  | n + 1 => max (maxTo f n) (f (n + 1))
/-- The least j ≤ n with f(j) = max_{j' ≤ n} f(j')  (`argTo_spec`, Inst/Model/Sanity.lean). -/
def argTo (f : Vec) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if f (argTo f n) < f (n + 1) then n + 1 else argTo f n

/-! ## The parameters on which the model depends, and the table functions -/

/-- "exponent of the reciprocal; shift; constant" of a normalisation -/
structure NormPar where
  M : ℕ
  K : ℕ
  eps : ℤ

/-- The parameters of the program: the sizes of the model, and one set of scales for all layers
(shifts, normalisations, `expRows`, `sh`). Each docstring below covers the fields up to the next
docstring. -/
structure Params where
  /-- Positions of a prompt; vocabulary; layers. -/
  T : ℕ
  V : ℕ
  layers : ℕ
  /-- Width of the residual stream; query heads; key/value heads; channels of a head. -/
  d : ℕ
  nq : ℕ
  nkv : ℕ
  ch : ℕ
  /-- Hidden units of a feed-forward block; of one expert; routed experts. -/
  f : ℕ
  fe : ℕ
  nexp : ℕ
  /-- The ten shifts of a layer: one value in all layers. -/
  kq : ℕ
  kk : ℕ
  kv : ℕ
  ko : ℕ
  kg : ℕ
  ku : ℕ
  kd : ℕ
  kr : ℕ
  kg' : ℕ
  ku' : ℕ
  /-- First and second normalisation of a layer, final normalisation. -/
  n1 : NormPar
  n2 : NormPar
  nf : NormPar
  /-- The number of rows in use of the table Exp of attention, step (PA4). -/
  expRows : ℤ
  /-- The shift applied to mx − sc before the look-up in Exp, step (PA3): u = ⌊(mx − sc) / 2^sh⌋. -/
  sh : ℕ

/-- The conditions under which NORM is stated: "1 ≤ ϵ < 2^48, 24 ≤ M ≤ 47, 17 ≤ K ≤ 32, M − 14 ≤ K".
-/
def NormPar.OK (np : NormPar) : Prop :=
  1 ≤ np.eps ∧ np.eps < 2 ^ 48 ∧ 24 ≤ np.M ∧ np.M ≤ 47 ∧ 17 ≤ np.K ∧ np.K ≤ 32 ∧ np.M - 14 ≤ np.K

/-- The reference parameters. The sizes V, layers, d, nq, nkv, ch, f, fe, nexp are those of the text
model of Llama 4 Maverick. The window T = 1,024 is a choice of this project.
The ten shifts, the numbers of the three normalisations, `expRows` and `sh` are one set of example
scales of this project (their origin: the head of this file). -/
def ppref : Params where
  T := 1024
  V := 202048
  layers := 48
  d := 5120
  nq := 40
  nkv := 8
  ch := 128
  f := 16384
  fe := 8192
  nexp := 128
  kq := 29
  kk := 29
  kv := 17
  ko := 17
  kg := 16
  ku := 20
  kd := 19
  kr := 17
  kg' := 16
  ku' := 20
  n1 := ⟨44, 30, 53687⟩
  n2 := ⟨44, 30, 53687⟩
  nf := ⟨44, 30, 53687⟩
  expRows := 2307
  sh := 8

/-- The five table functions that the program reads. C and S take the layer, the position and the
index ȷ of a pair of channels of a head, as in (PL4). -/
structure Tables where
  SILU : ℤ → ℤ
  SIGM : ℤ → ℤ
  Exp : ℤ → ℤ
  C : ℕ → ℕ → ℕ → ℤ
  S : ℕ → ℕ → ℕ → ℤ

/-! ## The weights -/

/-- The weight matrices of one layer. "A matrix has its input index first". Wg, Wu, Wd are the dense
matrices in a dense layer and the
shared ones in a layer with experts; Wr and the routed Eg, Eu, Ed (first argument: the expert) occur
in layers with experts only. -/
structure LayerW where
  Wq : Mat
  Wk : Mat
  Wv : Mat
  Wo : Mat
  Wg : Mat
  Wu : Mat
  Wd : Mat
  Wr : Mat
  Eg : ℕ → Mat
  Eu : ℕ → Mat
  Ed : ℕ → Mat

/-- An index: the weight tensors, as integers, independent of any layout. -/
structure Weights where
  layer : ℕ → LayerW
  Emb : Mat
  H : Mat

/-- "Layer L has experts if L is odd and is dense if L is even." -/
def hasExperts (L : ℕ) : Prop := L % 2 = 1
instance (L : ℕ) : Decidable (hasExperts L) := by unfold hasExperts; infer_instance

/-- An r × c matrix with entries in [lo, hi], and 0 outside, so that weights are determined by their
tensors. -/
def Box (r c : ℕ) (lo hi : ℤ) (W : Mat) : Prop :=
  ∀ j x, if j < r ∧ x < c then lo ≤ W j x ∧ W j x ≤ hi else W j x = 0

section WF
variable (P : Params)

/-- A matrix of two-byte weights: "b0 + 256 b1 ∈ [−2^12, 2^12)". -/
def Two (r c : ℕ) (W : Mat) : Prop := Box r c (-2 ^ 12) (2 ^ 12 - 1) W

/-- The matrices of layer L have the sizes of a layer with experts if `hasExperts L`, and of a dense
layer otherwise. Their entries are two-byte weights (`Two`), and 0 outside these sizes; a matrix
that the layer does not have is 0. -/
def LayerW.WF (L : ℕ) (w : LayerW) : Prop :=
  Two P.d (P.nq * P.ch) w.Wq ∧ Two P.d (P.nkv * P.ch) w.Wk ∧ Two P.d (P.nkv * P.ch) w.Wv ∧ Two
      (P.nq * P.ch) P.d w.Wo ∧
  (if hasExperts L then
    Two P.d P.fe w.Wg ∧ Two P.d P.fe w.Wu ∧ Two P.fe P.d w.Wd ∧ Two P.d P.nexp w.Wr ∧
    ∀ e, (if e < P.nexp then Two P.d P.fe (w.Eg e) ∧ Two P.d P.fe (w.Eu e) ∧ Two P.fe P.d (w.Ed e)
          else Two 0 0 (w.Eg e) ∧ Two 0 0 (w.Eu e) ∧ Two 0 0 (w.Ed e))
  else
    Two P.d P.f w.Wg ∧ Two P.d P.f w.Wu ∧ Two P.f P.d w.Wd ∧ Two 0 0 w.Wr ∧
    ∀ e, Two 0 0 (w.Eg e) ∧ Two 0 0 (w.Eu e) ∧ Two 0 0 (w.Ed e))

/-- The all-zero layer: the form of every layer beyond the last one. -/
def LayerW.IsZero (w : LayerW) : Prop :=
  Two 0 0 w.Wq ∧ Two 0 0 w.Wk ∧ Two 0 0 w.Wv ∧ Two 0 0 w.Wo ∧ Two 0 0 w.Wg ∧ Two 0 0 w.Wu ∧ Two 0 0
      w.Wd ∧ Two 0 0 w.Wr ∧
  ∀ e, Two 0 0 (w.Eg e) ∧ Two 0 0 (w.Eu e) ∧ Two 0 0 (w.Ed e)

/-- Well-formed weights. An entry of Emb is Σ_{ȷ<4} 256^ȷ b_ȷ with signed bytes b_ȷ: these are
exactly the
integers from −128 (256^4 − 1)/255 to 127 (256^4 − 1)/255. -/
def Weights.WF (i : Weights) : Prop :=
  (∀ L, if L < P.layers then (i.layer L).WF P L else (i.layer L).IsZero) ∧
  Box P.V P.d (-2155905152) 2139062143 i.Emb ∧ Two P.d P.V i.H

end WF

/-! ## The integer program -/

/-! ### Subroutine NORM. Input: the stream x at one position, of width d. -/
namespace NORM
variable (np : NormPar) (d : ℕ) (x : Vec)
/-- (N1) V = Σ_j x[j]² -/
def V : ℤ := ∑ j ∈ Finset.range d, x j ^ 2
/-- (N2) ς = isqrt(V + ϵ) -/
def sig : ℤ := isqrt (V d x + np.eps)
/-- (N3) R = ⌊(2^M + ⌊ς/2⌋) / ς⌋ -/
def R : ℤ := (2 ^ np.M + sig np d x / 2) / sig np d x
/-- (N4) yw[j] = rhu(x[j] R, K) -/
def yw (j : ℕ) : ℤ := rhu (x j * R np d x) np.K
/-- (N5) out[j] = clamp_2047(yw[j]) -/
def out (j : ℕ) : ℤ := clamp 2047 (yw np d x j)
/-- (N1) "halts unless V + ϵ < 2^78"; (N4) "halts unless every yw[j] fits 16 bits" -/
def OK : Prop := V d x + np.eps < 2 ^ 78 ∧ ∀ j < d, Fits16 (yw np d x j)
end NORM

/-! ### Subroutine UNIT, one hidden unit. Input: z, two columns wg, wu of weights, two shifts k, k'.
-/
namespace UNIT
variable (tb : Tables) (d : ℕ) (z wg wu : Vec) (k k' : ℕ)
/-- (U1) gw = rhu(Σ_j z[j] wg[j], k) -/
def gw : ℤ := rhu (dot d z wg) k
/-- (U2) g0 is the balanced low byte of gw. -/
def g0 : ℤ := lowByte (gw d z wg k)
/-- (U2) gh = (gw − g0)/256 -/
def gh : ℤ := (gw d z wg k - g0 d z wg k) / 256
/-- (U3) gc = clamp_127(gh) -/
def gc : ℤ := clamp 127 (gh d z wg k)
/-- (U4) sl = SILU[256 gc + g0 + 2^15] -/
def sl : ℤ := tb.SILU (256 * gc d z wg k + g0 d z wg k + 2 ^ 15)
/-- (U5) up = rhu(Σ_j z[j] wu[j], k') -/
def up : ℤ := rhu (dot d z wu) k'
/-- (U6) hh = sl · up -/
def hh : ℤ := sl tb d z wg k * up d z wu k'
/-- (U2) "halts unless −2^14 ≤ gh < 2^14"; (U5) "halts unless up fits 16 bits" -/
def OK : Prop := (-2 ^ 14 ≤ gh d z wg k ∧ gh d z wg k < 2 ^ 14) ∧ Fits16 (up d z wu k')
end UNIT

section Layer
variable (P : Params) (tb : Tables) (w : LayerW) (L : ℕ)

/-! ### The attention block of layer L: (PL2) to (PL7). x is the stream before it; i, j are
positions. Step (PL6) is (PA1) to (PA7). -/
namespace Att
variable (x : ℕ → Vec)
/-- The width of all query heads together (d_q). -/
def dq : ℕ := P.nq * P.ch
/-- (PL2) aw is the quotient yw, step (N4), of NORM(x). -/
def aw (i : ℕ) : Vec := NORM.yw P.n1 P.d (x i)
/-- (PL2) a = NORM(x) -/
def a (i : ℕ) : Vec := NORM.out P.n1 P.d (x i)
/-- (PL3) Aq = a Wq -/
def Aq (i c : ℕ) : ℤ := dot P.d (a P x i) fun j => w.Wq j c
/-- (PL3) Ak = a Wk -/
def Ak (i c : ℕ) : ℤ := dot P.d (a P x i) fun j => w.Wk j c
/-- (PL3) Av = a Wv -/
def Av (i c : ℕ) : ℤ := dot P.d (a P x i) fun j => w.Wv j c
/-- (PL4) "AY is Aq followed by Ak"; (h, n) is the index c = ch·h + n -/
def AY (i c : ℕ) : ℤ := if c < dq P then Aq P w x i c else Ak P w x i (c - dq P)
/-- (PL4) Y'_(h,2ȷ) = C AY_(h,2ȷ) − S AY_(h,2ȷ+1), Y'_(h,2ȷ+1) = S AY_(h,2ȷ) + C AY_(h,2ȷ+1), with C
= C[L][i][ȷ], S = S[L][i][ȷ] -/
def Y' (i c : ℕ) : ℤ :=
  let jj := (c % P.ch) / 2
  if (c % P.ch) % 2 = 0 then tb.C L i jj * AY P w x i c - tb.S L i jj * AY P w x i (c + 1)
  else tb.S L i jj * AY P w x i (c - 1) + tb.C L i jj * AY P w x i c
/-- (PL5) qkw_c = rhu(Y'_c, k) with k = kq for c < d_q and k = kk after. -/
def qkw (i c : ℕ) : ℤ := rhu (Y' P tb w L x i c) (if c < dq P then P.kq else P.kk)
/-- (PL5) vw_c = rhu(Av_c, kv) -/
def vw (i c : ℕ) : ℤ := rhu (Av P w x i c) P.kv
/-- (PL5) q_c = clamp_2047(qkw_c) -/
def q (i c : ℕ) : ℤ := clamp 2047 (qkw P tb w L x i c)
/-- (PL5) kx_c = clamp_2047(qkw_{d_q + c}) -/
def kx (i c : ℕ) : ℤ := clamp 2047 (qkw P tb w L x i (dq P + c))
/-- (PL5) v_c = clamp_2047(vw_c) -/
def v (i c : ℕ) : ℤ := clamp 2047 (vw P w x i c)
/-- "Query head h reads key/value head g = ⌊h/5⌋"; 5 is nq / nkv at `ppref`. -/
def kvOf (h : ℕ) : ℕ := h / (P.nq / P.nkv)
/-- (PA1) sc_ij = Σ_{n<ch} qry_i[h][n] key_j[g][n]; the paper's qry and key are `q` and `kx`, and g
is `kvOf h`. -/
def sc (h i j : ℕ) : ℤ := ∑ n ∈ Finset.range P.ch, q P tb w L x i (P.ch * h + n) * kx P tb w L x j
    (P.ch * kvOf P h + n)
/-- (PA2) mx_i = max_{j ≤ i} sc_ij -/
def mx (h i : ℕ) : ℤ := maxTo (sc P tb w L x h i) i
/-- (PA3) u_ij = ⌊(mx_i − sc_ij) / 2^sh⌋; sh = 8 at `ppref`. -/
def u (h i j : ℕ) : ℤ := (mx P tb w L x h i - sc P tb w L x h i j) / 2 ^ P.sh
/-- (PA4) wt_ij = Exp[u_ij] if u_ij < 2,307, and 0 otherwise; 2,307 is `expRows` at `ppref`. -/
def wt (h i j : ℕ) : ℤ := if u P tb w L x h i j < P.expRows then tb.Exp (u P tb w L x h i j) else 0
/-- (PA5) den_i = Σ_{j ≤ i} wt_ij -/
def den (h i : ℕ) : ℤ := ∑ j ∈ Finset.range (i + 1), wt P tb w L x h i j
/-- (PA6) ac_i[n] = Σ_{j ≤ i} wt_ij val_j[g][n]; the paper's val is `v`. -/
def ac (h i n : ℕ) : ℤ := ∑ j ∈ Finset.range (i + 1), wt P tb w L x h i j * v P w x j
    (P.ch * kvOf P h + n)
/-- (PA7) out_i[h][n] = ⌊(2 ac_i[n] + den_i) / (2 den_i)⌋; o_c is out_i[h][n] at c = ch·h + n -/
def o (i c : ℕ) : ℤ :=
  (2 * ac P tb w L x (c / P.ch) i (c % P.ch) + den P tb w L x (c / P.ch) i) /
      (2 * den P tb w L x (c / P.ch) i)
/-- (PL7) x'[c] = x[c] + rhu((o Wo)_c, ko) -/
def x' (i c : ℕ) : ℤ := x i c + rhu (dot (dq P) (o P tb w L x i) fun j => w.Wo j c) P.ko
/-- The range conditions of (PL2) and (PL5), at all positions. -/
def OK : Prop := ∀ i < P.T, NORM.OK P.n1 P.d (x i) ∧ (∀ c < dq P + P.nkv * P.ch, Fits16
    (qkw P tb w L x i c)) ∧
  ∀ c < P.nkv * P.ch, Fits16 (vw P w x i c)
end Att

/-! ### The feed-forward block of layer L: (PL8) to (PL13). x is the stream after the attention
block (the paper's x').
Steps (R1) to (R6) choose the routed expert e* and scale its input. The labels are not consecutive
here: (PL10) does not occur. -/
namespace FF
variable (x : ℕ → Vec)
/-- (PL8) mw is the quotient yw, step (N4), of NORM(x'). -/
def mw (i : ℕ) : Vec := NORM.yw P.n2 P.d (x i)
/-- (PL8) m = NORM(x') -/
def m (i : ℕ) : Vec := NORM.out P.n2 P.d (x i)
/-- (R1) lw_e = rhu((m Wr)_e, kr) -/
def lw (i e : ℕ) : ℤ := rhu (dot P.d (m P x i) fun j => w.Wr j e) P.kr
/-- (R2) l3_e = lw_e mod 8 -/
def l3 (i e : ℕ) : ℤ := lw P w x i e % 8
/-- (R2) ly_e = (lw_e − l3_e)/8 -/
def ly (i e : ℕ) : ℤ := (lw P w x i e - l3 P w x i e) / 8
/-- (R3) lr_e = 8 clamp_2047(ly_e) + l3_e -/
def lr (i e : ℕ) : ℤ := 8 * clamp 2047 (ly P w x i e) + l3 P w x i e
/-- (R4) e* is the least e with lr_e = max_{e'} lr_{e'}. -/
def es (i : ℕ) : ℕ := argTo (lr P w x i) (P.nexp - 1)
/-- (R4) mr = lr_{e*} -/
def mr (i : ℕ) : ℤ := lr P w x i (es P w x i)
/-- (R5) sc = SIGM[mr + 2^15] -/
def sc (i : ℕ) : ℤ := tb.SIGM (mr P w x i + 2 ^ 15)
/-- (R6) xr[j] = rhu(sc · m[j], 16) -/
def xr (i j : ℕ) : ℤ := rhu (sc P tb w x i * m P x i j) 16
/-- Unit j belongs to the routed expert: the layer has experts and j ≥ fe. -/
def routed (j : ℕ) : Prop := hasExperts L ∧ P.fe ≤ j
instance (j : ℕ) : Decidable (routed P L j) := by unfold routed; infer_instance
/-- `z`, `wg`, `wu`, `kG`, `kU` are the input, the two columns and the two shifts of the hidden unit
j: (PL9) in a dense layer; (PL11) in a layer with experts, where the
units below fe are those of the shared expert and the unit fe + j is unit j of the routed expert e*.
-/
def z (i j : ℕ) : Vec := if routed P L j then xr P tb w x i else m P x i
/-- See `z`. -/
def wg (i j : ℕ) : Vec := fun t => if routed P L j then w.Eg (es P w x i) t (j - P.fe) else w.Wg t j
/-- See `z`. -/
def wu (i j : ℕ) : Vec := fun t => if routed P L j then w.Eu (es P w x i) t (j - P.fe) else w.Wu t j
/-- See `z`. -/
def kG (j : ℕ) : ℕ := if routed P L j then P.kg' else P.kg
/-- See `z`. -/
def kU (j : ℕ) : ℕ := if routed P L j then P.ku' else P.ku
/-- (PL9), (PL11) hh_j = UNIT(...) -/
def hh (i j : ℕ) : ℤ := UNIT.hh tb P.d (z P tb w L x i j) (wg P w L x i j) (wu P w L x i j)
    (kG P L j) (kU P L j)
/-- The number of hidden units of the layer. -/
def units : ℕ := if hasExperts L then 2 * P.fe else P.f
/-- (PL12) Ad_c = Σ_j hh_j Wd[j][c]; in a layer with experts Σ_{j<fe} hh_j Wd[j][c] + Σ_{j<fe}
hh_{fe+j} Wd^{e*}[j][c] -/
def Ad (i c : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (units P L), hh P tb w L x i j * (if routed P L j then w.Ed (es P w x i)
      (j - P.fe) c else w.Wd j c)
/-- (PL13) x''[c] = x'[c] + rhu(Ad_c, kd) -/
def x'' (i c : ℕ) : ℤ := x i c + rhu (Ad P tb w L x i c) P.kd
/-- The range conditions of (PL8), (R2) and of every call of UNIT, at all positions. -/
def OK : Prop := ∀ i < P.T, NORM.OK P.n2 P.d (x i) ∧ (hasExperts L → ∀ e < P.nexp, Fits16
    (ly P w x i e)) ∧
  ∀ j < units P L, UNIT.OK P.d (z P tb w L x i j) (wg P w L x i j) (wu P w L x i j) (kG P L j)
      (kU P L j)
end FF
end Layer

/-! ### The whole program -/
section Program
variable (P : Params) (tb : Tables) (i : Weights) (prompt : Fin P.T → Fin P.V)

/-- "The residual stream": X_λ, λ = 0, ..., 2·layers. (PL1) X_0[i][j] = Emb[tok_i][j]; X_{2L} enters
layer L, X_{2L+1} follows its attention
block, X_{2L+2} follows its feed-forward block. -/
def X : ℕ → ℕ → Vec
  | 0 => fun pos j => if h : pos < P.T then i.Emb (prompt ⟨pos, h⟩) j else 0
  | l + 1 =>
      if l % 2 = 0 then Att.x' P tb (i.layer (l / 2)) (l / 2) (X l)
          else FF.x'' P tb (i.layer (l / 2)) (l / 2) (X l)

/-- (PH1) nw is the quotient yw, step (N4), of NORM(X_last[i]). -/
def nw (pos : ℕ) : Vec := NORM.yw P.nf P.d (X P tb i prompt (2 * P.layers) pos)
/-- (PH1) nrm_i = NORM(X_last[i]) -/
def nrm (pos : ℕ) : Vec := NORM.out P.nf P.d (X P tb i prompt (2 * P.layers) pos)
/-- (PH2) lg_i[ι] = Σ_j nrm_i[j] H[j][ι] -/
def lg (pos ι : ℕ) : ℤ := dot P.d (nrm P tb i prompt pos) fun j => i.H j ι

/-- No range condition fails: "those of (N1), (N4), (PL5), (U2), (U5) and (R2), at all positions, in
all layers and, for (N1)
and (N4), in the final normalisation". -/
def Runs : Prop :=
  (∀ L < P.layers, Att.OK P tb (i.layer L) L (X P tb i prompt (2 * L)) ∧ FF.OK P tb (i.layer L) L
      (X P tb i prompt (2 * L + 1))) ∧
  ∀ pos < P.T, NORM.OK P.nf P.d (X P tb i prompt (2 * P.layers) pos)

/-- (PH3) "y is the least ι with lg_1023[ι] = max_{ι'} lg_1023[ι']"; 1,023 is T − 1 at `ppref`. -/
def IsOutput (y : ℕ) : Prop :=
  y < P.V ∧ (∀ ι < P.V, lg P tb i prompt (P.T - 1) ι ≤ lg P tb i prompt (P.T - 1) y) ∧
  ∀ ι < y, lg P tb i prompt (P.T - 1) ι < lg P tb i prompt (P.T - 1) y

/-- Model_i(prompt) = y. Model_i is a partial function: `ModelIs` holds for at most one y
(`modelIs_unique`, Inst/Model/Sanity.lean), and for none if
a range condition fails. -/
def ModelIs (y : ℕ) : Prop := Runs P tb i prompt ∧ IsOutput P tb i prompt y

/-! ## Prompts that fit

Two further bounds on intermediate values. In the paper they describe the prompts on which the
honest prover can write these values in signed bytes. A value written as Σ_ȷ 256^ȷ b_ȷ with signed
bytes b_ȷ in [−128, 127] is at most 32,639 with two bytes and at most 547,599,908,735 with five
(Inst/Model/Widened.lean), while `Fits16` allows quotients up to 32,767.
No relation of this library uses them.
The labels are not consecutive here: (Fit1) does not occur. -/

/-- (Fit2) "every quotient yw of (N4) (that is, every aw and mw of all layers and every nw of the
head), every qkw and vw of (PL5), every up of (U5)
and every ly of (R2) is at most 32,639", at all positions -/
def Fit2 : Prop :=
  (∀ L < P.layers, ∀ pos < P.T,
    let w := i.layer L
    let x := X P tb i prompt (2 * L)
    let x1 := X P tb i prompt (2 * L + 1)
    (∀ j < P.d, Att.aw P x pos j ≤ 32639 ∧ FF.mw P x1 pos j ≤ 32639) ∧
    (∀ c < Att.dq P + P.nkv * P.ch, Att.qkw P tb w L x pos c ≤ 32639) ∧
        (∀ c < P.nkv * P.ch, Att.vw P w x pos c ≤ 32639) ∧
    (∀ j < FF.units P L, UNIT.up P.d (FF.z P tb w L x1 pos j) (FF.wu P w L x1 pos j) (FF.kU P L j) ≤
        32639) ∧
    (hasExperts L → ∀ e < P.nexp, FF.ly P w x1 pos e ≤ 32639)) ∧
  ∀ pos < P.T, ∀ j < P.d, nw P tb i prompt pos j ≤ 32639

/-- (Fit3) |X_λ[i][j]| ≤ 547,599,908,735 for all λ, i, j -/
def Fit3 : Prop := ∀ l ≤ 2 * P.layers, ∀ pos < P.T, ∀ j < P.d,
  -547599908735 ≤ X P tb i prompt l pos j ∧ X P tb i prompt l pos j ≤ 547599908735

end Program

/-! ## The relation -/

/-- An instance is a request: T tokens, the announced token y, and the two numbers r, e. The paper's
instance, "x = (prompt, y) ∈ [V]^(T+1)", is the request `Instance.nextOf prompt y` below. -/
structure Instance (P : Params) where
  prompt : Fin P.T → Fin P.V
  y : Fin P.V
  /-- The two numbers that bound the covered positions: r ≤ t < e, each at most T. "The next token
after T tokens" is r = T − 1, e = T. -/
  rF : Fin (P.T + 1)
  eF : Fin (P.T + 1)

/-- The request "the next token after these T tokens", with the answer y. -/
def Instance.nextOf {P : Params} (prompt : Fin P.T → Fin P.V) (y : Fin P.V) : Instance P :=
    ⟨prompt, y, ⟨P.T - 1, by omega⟩, ⟨P.T, by omega⟩⟩
/-- The number r, as a natural number. -/
def Instance.r {P : Params} (x : Instance P) : ℕ := x.rF.val
/-- The number e, as a natural number. -/
def Instance.e {P : Params} (x : Instance P) : ℕ := x.eF.val
/-- `x.e` is at most `P.T`. -/
theorem Instance.e_le {P : Params} (x : Instance P) : x.e ≤ P.T := Nat.lt_succ_iff.1 x.eF.isLt

/-- The type of indices: the well-formed weights. In the paper an index is any matrix and L(i) "is
empty unless WF(i)"; here WF is in the type, so
a statement "for every index" is about well-formed weights only. -/
def Index (P : Params) : Type := {i : Weights // i.WF P}

/-- R_inf := {(i, x, ⊥) : WF(i), Model_i(prompt) = y}. The witness is empty. It does not read r and
e: whatever they are, it states "y is the next token after the T tokens". It is the relation of a
request only at `Instance.nextOf`; the relations that read r and e are in Inst/Model/ProgramR.lean.
It matches the paper's relation where no division by 0 is reached. Inst/Model/Sanity.lean has two
lemmas on that: `sig_pos` (if 1 ≤ ϵ in the parameters of a normalisation, then 1 ≤ ς) and `den_pos`
(if `tb.OK P`,
Inst/Model/Tables.lean, and 0 < P.expRows, then 2^12 ≤ den). `tbRef.OK ppref` is `tbRef_ok`
(Inst/Model/TablesRef.lean). A theorem about R_inf should be stated at such P and tb. -/
def Rinf (P : Params) (tb : Tables) (i : Index P) (x : Instance P) : Prop :=
  ModelIs P tb i.val x.prompt x.y


/-! ## Scales that differ from layer to layer

A model whose scales are fitted to its weights has a set for each layer, and a separate final
normalisation.
Here is the same program, layer by layer, with the scales and the tables of that layer. The
definitions of a layer above are reused: layer L is evaluated at the parameters `P.at (κ L)` and the
tables `tbs L`, and the head at the final normalisation `nf`, a separate argument. The sizes are
those of P; `P.nf` is not read.
With the same scales and tables in all layers and nf = P.nf it is the program above: `XK_const` and
`RinfK_const` (Inst/Model/ProgramK.lean).
Difference from the paper: `Params` has the field sh, and (PA3) divides by 2 ^ P.sh where the paper
has 2^8. -/

/-- The scales of one layer. -/
structure LayerScale where
  kq : ℕ
  kk : ℕ
  kv : ℕ
  ko : ℕ
  kg : ℕ
  ku : ℕ
  kd : ℕ
  kr : ℕ
  kg' : ℕ
  ku' : ℕ
  n1 : NormPar
  n2 : NormPar
  expRows : ℤ
  sh : ℕ

/-- The scales that P has for all layers. -/
def Params.scale (P : Params) : LayerScale := ⟨P.kq, P.kk, P.kv, P.ko, P.kg, P.ku, P.kd, P.kr,
    P.kg', P.ku', P.n1, P.n2, P.expRows, P.sh⟩

/-- P with the scales of one layer in place of its scales; the sizes and the final normalisation are
unchanged. -/
def Params.at (P : Params) (s : LayerScale) : Params :=
  { P with
    kq := s.kq, kk := s.kk, kv := s.kv, ko := s.ko, kg := s.kg, ku := s.ku, kd := s.kd,
    kr := s.kr, kg' := s.kg', ku' := s.ku', n1 := s.n1, n2 := s.n2,
    expRows := s.expRows, sh := s.sh }

section ProgramK
variable (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (i : Weights)
    (prompt : Fin P.T → Fin P.V)

/-- The residual stream, with layer L at its scales and tables. -/
def XK : ℕ → ℕ → Vec
  | 0 => fun pos j => if h : pos < P.T then i.Emb (prompt ⟨pos, h⟩) j else 0
  | l + 1 =>
      if l % 2 = 0 then Att.x' (P.at (κ (l / 2))) (tbs (l / 2)) (i.layer (l / 2)) (l / 2) (XK l)
          else FF.x'' (P.at (κ (l / 2))) (tbs (l / 2)) (i.layer (l / 2)) (l / 2) (XK l)

/-- `nrm` with the scales and tables of each layer, at the final normalisation nf. -/
def nrmK (pos : ℕ) : Vec := NORM.out nf P.d (XK P κ tbs i prompt (2 * P.layers) pos)
/-- `lg` with the scales and tables of each layer. -/
def lgK (pos ι : ℕ) : ℤ := dot P.d (nrmK P κ nf tbs i prompt pos) fun j => i.H j ι

/-- `Runs` with the scales and tables of each layer. -/
def RunsK : Prop :=
  (∀ L < P.layers, Att.OK (P.at (κ L)) (tbs L) (i.layer L) L (XK P κ tbs i prompt (2 * L)) ∧ FF.OK
      (P.at (κ L)) (tbs L) (i.layer L) L (XK P κ tbs i prompt (2 * L + 1))) ∧
  ∀ pos < P.T, NORM.OK nf P.d (XK P κ tbs i prompt (2 * P.layers) pos)

/-- `IsOutput` with the scales and tables of each layer. -/
def IsOutputK (y : ℕ) : Prop :=
  y < P.V ∧ (∀ ι < P.V, lgK P κ nf tbs i prompt (P.T - 1) ι ≤ lgK P κ nf tbs i prompt (P.T - 1) y) ∧
  ∀ ι < y, lgK P κ nf tbs i prompt (P.T - 1) ι < lgK P κ nf tbs i prompt (P.T - 1) y

/-- `ModelIs` with the scales and tables of each layer. -/
def ModelIsK (y : ℕ) : Prop := RunsK P κ nf tbs i prompt ∧ IsOutputK P κ nf tbs i prompt y

end ProgramK

/-- R_inf with scales for each layer and the final normalisation nf. Like `Rinf` it does not read r
and e (`RinfR_next` and `ModelS_nextOf`, Inst/Model/ProgramR.lean, relate it to the relations on a
request).
It is "the model at these scales" for scales, a final normalisation and tables under which no
division by 0 is reached. For ς and den that holds if every ϵ is at least 1 and the tables of each
layer have `Tables.OK` (Inst/Model/Tables.lean) at `P.at (κ L)`, with 0 < expRows: `sig_pos`,
`den_pos` (Inst/Model/Sanity.lean). Every shift should be at least 1 (`rhu`). A shift of 16 or more,
which `site_sound` (Inst/Model/Common/Site.lean) asks, is not required of `P.at (κ L)`.
For the settings `ScalesAndPolicy` of Inst/Model/ProgTests.lean, at `ppref` and the tables `tbRef`, these
conditions follow from `Lawful` (Inst/Model/Scales.lean), by the lemmas of
Inst/Model/ScalesSanity.lean. A theorem about RinfK should be stated under such conditions. -/
def RinfK (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (i : Index P)
    (x : Instance P) : Prop := ModelIsK P κ nf tbs i.val x.prompt x.y

end Inst.Model
