-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/Trace.lean: the execution trace of a feed-forward segment and its field relation:
  the weights as the keys read them, the arrays as functions of the cells, further functions of the
  cells, the keys of the 34 families, the key vectors of the eight calls, the identities, the
  batches of looked-up values of the main lookup argument; what the statements on the field relation
  and the integer model conclude (`Part1` to `Part3`); and `Spec.honest`.
  Definitions, and statements `Spec.*` proved in other files: `honest`, for valid scales only
  (`[Lawful]`, Inst/Model/FF/Lawful.lean), in Inst/Model/FF/Honest.lean, `keyVecAt` in
  Inst/Model/FF/IndexFacts.lean.

  Words of this library: lean/GLOSSARY.md.
  A cell is one small integer of the witness; a key is a looked-up value, which must be an entry of
  the table of its call (one of eight lookups). Labels such as (PL7), (U2), (J1), (FL14) link one
  docstring to another ((PL..), (PA..), (N..), (U..), (R..): the doc comments of
  Inst/Model/Program.lean; (J1) to (J9): `idn`, Inst/Model/Common/Ledger.lean; (J10), (J11): `Idn`,
  below; (FL..): Inst/Model/Common/Site.lean, Inst/Model/Common/TableKeys.lean,
  Inst/Model/Common/Unit.lean, Inst/Model/Common/Router.lean, Inst/Model/Common/LedgerSound.lean and
  `Part1`, below; (FA12): `OBound`, (FL19): `LastBound`, below).
  * A trace is a function on the names of cells (`Cell`, Inst/Model/FF/Index.lean); the field
    relation reads only valid names, if f = 2 fe (Inst/Model/FF/CastValid.lean; f, fe: "Hidden units
    of a feed-forward block; of one expert; ..", `Params`, Inst/Model/Program.lean).
  * Every array, every function of the cells and every key is defined over an arbitrary commutative
    ring R, from t : Cell → R and weights over R. With R = ℤ these are the integer quantities, with
    R = F or E those of the protocol.
  * The weights of a layer are a record `LW R` of matrices over R. `layerR` reads them from the
    matrix W by the layout of Inst/Model/Layout.lean, with the formulas of `Layout.layerOf`, which
    is the case R = ℤ.
  * ℓ is the number of a layer in the segment; the layer of the model is L0 + ℓ. Of L0 the
    statements ask only that it is even and that L0 + 4 ≤ layers (`Setting`). An array of the router
    has the instance ℓ′ = ⌊ℓ/2⌋.
  * The array o is an input of the segment, like the stream: the attention segment of the group
    proves it. The arrays q, kx, v, o are in the matrix qa, which that segment borrows. In a segment
    that is not the first, the cells of x0 are those of x8 of the segment before (`Trace.vFF`,
    Inst/Model/All/Trace.lean).
  * `trace` takes all valid names as its cells, those of x0 too where they are borrowed. The two
    names of such a cell are identified where the segments are put together
    (Inst/Model/All/Trace.lean). A count of places or hidden cells from "trace" has to leave out the
    names of x0 where they are borrowed.
  * The ledger of a normalisation is that of Inst/Model/Common/Ledger.lean, which the head segment
    shares; the two keys of a rounding are those of Inst/Model/Common/Site.lean.
  * The honest trace is a term, `hon`: the value of every array from the definitions of
    Inst/Model/Program.lean (`hv`), written in the digits of Inst/Model/Widened.lean.
  The quantization scales are the instance argument `[scl : Scl]` (Inst/Model/Scl.lean;
  Inst/Model/FF/Index.lean says how they are read).
  Notation:
    `tb`, `W`, `L0`, `tok`, `first`, `t`: a `Tables` ("The five table functions that the program
      reads."); a `Mat`, the matrix W; "L0 the first layer of the segment" (`trace`); the prompt,
      `ℕ → ℕ` ("the instance is the prompt"); a `Bool` (whether the segment is the first: (J11)); in
      `Part1` to `Part3`: a function on the names of cells, with integer values.
    `Layout.kRef`, `Layout.hRef`: "rows and columns of W: h; 2^k" (h is `hRef`, k is `kRef`;
      Inst/Model/Layout.lean); `ppref`: "The reference parameters." (Inst/Model/Program.lean).
    `rhu a k`: "rhu(a, k) = ⌊(a + 2^(k−1)) / 2^k⌋, the quotient by 2^k rounded to the nearest
      integer, halves up"; k ≥ 1; `lowByte a`: "the balanced low byte of a is ((a + 128) mod 256) −
      128" (Inst/Model/Program.lean).
    `tb.OK P`: `Tables.OK`, "The bounds" on the table functions (Inst/Model/Tables.lean);
      `Dim.ref.Pl l`: the parameters of layer l of the segment: the sizes of `Dim.ref` with the
      scales `scl.κ l` (Inst/Model/FF/Index.lean).
    the arrays aw, a, ra, .., xr, D: `Arr` (Inst/Model/FF/Index.lean); most have the names of values
      of the integer program (`NORM`, `UNIT`, `Att`, `FF`, Inst/Model/Program.lean), whose doc
      comments tell them.
    the families G, U, UT, .., CG: "The families of keys." (`Fam`, Inst/Model/FF/Index.lean); the
      key of each: `key`, below.
-/
import Inst.Model.FF.Index
import Inst.Model.Common.LedgerHonest
import Inst.Model.Common.Site
import Inst.Model.LayoutBridge
import Inst.Model.Widened
import Blocks.Segment

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset

/-! ## The weights of a layer, over a ring -/

/-- the matrices of one layer, as in `Inst.Model.LayerW` -/
structure LW (R : Type) where
  Wq : ℕ → ℕ → R
  Wk : ℕ → ℕ → R
  Wv : ℕ → ℕ → R
  Wo : ℕ → ℕ → R
  Wg : ℕ → ℕ → R
  Wu : ℕ → ℕ → R
  Wd : ℕ → ℕ → R
  Wr : ℕ → ℕ → R
  Eg : ℕ → ℕ → ℕ → R
  Eu : ℕ → ℕ → ℕ → R
  Ed : ℕ → ℕ → ℕ → R

/-- integer weights, mapped into R -/
def LW.ofInt (R : Type) [CommRing R] (w : LayerW) : LW R :=
  ⟨fun j x => (w.Wq j x : R), fun j x => (w.Wk j x : R), fun j x => (w.Wv j x : R),
    fun j x => (w.Wo j x : R), fun j x => (w.Wg j x : R), fun j x => (w.Wu j x : R),
    fun j x => (w.Wd j x : R), fun j x => (w.Wr j x : R), fun e j x => (w.Eg e j x : R),
    fun e j x => (w.Eu e j x : R), fun e j x => (w.Ed e j x : R)⟩

section Read
variable {R : Type} [CommRing R] (P : Params) (k : ℕ) (W : ℕ → ℕ → R)

open Layout in
/-- the entry i of the unit U, which has the number n: Σ_ȷ 256^ȷ W[row][column] at the rows and
columns that the layout gives -/
def entryR (n : ℕ) (U : UnitS) (i : List ℕ) : R :=
  ∑ jj ∈ range U.nU, 256 ^ jj * W (place k (units P) n U jj i).1 (place k (units P) n U jj i).2

/-- a matrix with r rows and c columns, and 0 outside -/
def matR (r c : ℕ) (f : ℕ → ℕ → R) : ℕ → ℕ → R := fun j x => if j < r ∧ x < c then f j x else 0

open Layout in
/-- The weights of layer L, read from W (the formulas of `Layout.layerOf`). -/
def layerR (L : ℕ) : LW R :=
  let n := first P L
  let ex := hasExperts L
  { Wq := matR P.d (P.nq * P.ch) fun j c => entryR P k W n (uQK P) [c / P.ch, c % P.ch, j]
    Wk := matR P.d (P.nkv * P.ch) fun j c => entryR P k W n (uQK P) [P.nq + c / P.ch, c % P.ch, j]
    Wv := matR P.d (P.nkv * P.ch) fun j x => entryR P k W (n + 1) (uV P) [j, x]
    Wo := matR (P.nq * P.ch) P.d fun j x => entryR P k W (n + 2) (uO P) [j, x]
    Wg := if ex then
      matR P.d P.fe fun j x =>
        entryR P k W (n + 3) (uGU P P.fe) [j, x]
        else matR P.d P.f fun j x => entryR P k W (n + 3) (uGU P P.f) [j, x]
    Wu := if ex then
      matR P.d P.fe fun j x =>
        entryR P k W (n + 4) (uGU P P.fe) [j, x]
        else matR P.d P.f fun j x => entryR P k W (n + 4) (uGU P P.f) [j, x]
    Wd := if ex then
      matR P.fe P.d fun j x =>
        entryR P k W (n + 7) (uD P P.fe) [j, x]
        else matR P.f P.d fun j x => entryR P k W (n + 5) (uD P P.f) [j, x]
    Wr := if ex then matR P.d P.nexp fun j e => entryR P k W (n + 9) (uR P) [j, e] else fun _ _ => 0
    Eg := fun e =>
      if ex ∧ e < P.nexp then
        matR P.d P.fe fun j x => entryR P k W (n + 5) (uGUr P) [j, e, x] else fun _ _ => 0
    Eu := fun e =>
      if ex ∧ e < P.nexp then
        matR P.d P.fe fun j x => entryR P k W (n + 6) (uGUr P) [j, e, x] else fun _ _ => 0
    Ed := fun e =>
      if ex ∧ e < P.nexp then
        matR P.fe P.d fun j x => entryR P k W (n + 8) (uDr P) [j, e, x] else fun _ _ => 0 }

open Layout in
/-- the embedding, read from W -/
def embR : ℕ → ℕ → R := matR P.V P.d fun t j => entryR P k W (first P P.layers) (uEmb P) [t, j]

end Read

/-! ## Arrays: a value with n cells c_0, .., c_(n-1) is Σ 256^k c_k plus the offset -/

section Arrays
variable {R : Type} [CommRing R] (D : Dim) (t : Cell → R)

/-- The read-out formula. -/
def val (X : Arr) (inst j i : ℕ) : R :=
  ∑ k ∈ range X.nCell, 256 ^ k * t ⟨X, k, inst, j, i⟩ + ((X.off : ℤ) : R)

/-- the array and the instance that hold state s of the stream -/
def streamAt (s : ℕ) : Arr × ℕ :=
  if s = 0 then (.x0, 0) else if s = 2 * D.nl then (.x8, 0) else (.xs, s - 1)

/-- x_s[j] at position i -/
def xS (s j i : ℕ) : R := val t (streamAt D s).1 (streamAt D s).2 j i

/-- b_l: cell l of x_s[j] at position i -/
def bS (s l j i : ℕ) : R := t ⟨(streamAt D s).1, l, (streamAt D s).2, j, i⟩

/-- the bytes of the ledger of the norm instance ν at position i, as values -/
def led (ν i : ℕ) : ℕ → R := fun n => val t .D ν n i

/-- the parameters of the norm instance ν = 2ℓ + n: the first normalisation of a layer for n = 0,
the second for n = 1 -/
def npOf (ν : ℕ) : NormPar := if ν % 2 = 0 then (D.Pl (ν / 2)).n1 else (D.Pl (ν / 2)).n2

/-! ## Quantities that are computed from the cells and are not stored in cells -/

variable (tb : Tables) (L0 : ℕ) (w : ℕ → LW R)

/-- gw = g0 + 256 gh -/
def gw (l x i : ℕ) : R := val t .g0 l x i + 256 * val t .gh l x i
/-- lw = 8 ly + l3 -/
def lw (l' e i : ℕ) : R := 8 * val t .ly l' e i + val t .l3 l' e i
/-- mr = Σ_e sel_e lr_e -/
def mr (l' i : ℕ) : R := ∑ e ∈ range D.nx, val t .sel l' e i * val t .lr l' e i
/-- hh_j = sl_j up_j -/
def hh (l j i : ℕ) : R := val t .sl l j i * val t .up l j i
/-- Aq = a W_q -/
def Aq (l x i : ℕ) : R := ∑ j ∈ range D.d, val t .a l j i * (w l).Wq j x
/-- Ak = a W_k -/
def Ak (l x i : ℕ) : R := ∑ j ∈ range D.d, val t .a l j i * (w l).Wk j x
/-- Av = a W_v -/
def Av (l x i : ℕ) : R := ∑ j ∈ range D.d, val t .a l j i * (w l).Wv j x
/-- AY is Aq on the query heads and Ak on the key heads -/
def AY (l x i : ℕ) : R := if x < D.dq then Aq D t w l x i else Ak D t w l (x - D.dq) i
/-- Y′_(h,2ȷ) = C AY_(h,2ȷ) − S AY_(h,2ȷ+1), Y′_(h,2ȷ+1) = S AY_(h,2ȷ) + C AY_(h,2ȷ+1), with the
public tables of layer L0 + ℓ at (i, ȷ) -/
def Y' (l x i : ℕ) : R :=
  let jj := (x % D.P.ch) / 2
  if (x % D.P.ch) % 2 = 0 then
    ((tb.C (L0 + l) i jj : ℤ) : R) * AY D t w l x i -
      ((tb.S (L0 + l) i jj : ℤ) : R) * AY D t w l (x + 1) i
  else
    ((tb.S (L0 + l) i jj : ℤ) : R) * AY D t w l (x - 1) i +
      ((tb.C (L0 + l) i jj : ℤ) : R) * AY D t w l x i
/-- the hidden unit x of layer ℓ belongs to the routed expert -/
def routed (l x : ℕ) : Bool := isExpL l && decide (D.fe ≤ x)
/-- Ag_x = (m W_g)_x; on the routed expert Ag_(fe+x) = Σ_e sel_e (xr W_g^e)_x -/
def Ag (l x i : ℕ) : R :=
  if routed D l x then
    ∑ e ∈ range D.nx,
      val t .sel (l / 2) e i * ∑ j ∈ range D.d, val t .xr (l / 2) j i * (w l).Eg e j (x - D.fe)
  else ∑ j ∈ range D.d, val t .m l j i * (w l).Wg j x
/-- Au: the same with W_u and W_u^e -/
def Au (l x i : ℕ) : R :=
  if routed D l x then
    ∑ e ∈ range D.nx,
      val t .sel (l / 2) e i * ∑ j ∈ range D.d, val t .xr (l / 2) j i * (w l).Eu e j (x - D.fe)
  else ∑ j ∈ range D.d, val t .m l j i * (w l).Wu j x
/-- Ad_x = Σ_j hh_j W_d[j][x]; in a layer with experts Σ_(j<fe) hh_j W_d[j][x] + Σ_e sel_e Σ_(j<fe)
hh_(fe+j) W_d^e[j][x] -/
def Ad (l x i : ℕ) : R :=
  if isExpL l then
    ∑ j ∈ range D.fe, hh t l j i * (w l).Wd j x +
      ∑ e ∈ range D.nx,
        val t .sel (l / 2) e i * ∑ j ∈ range D.fe, hh t l (D.fe + j) i * (w l).Ed e j x
  else ∑ j ∈ range D.f, hh t l j i * (w l).Wd j x
/-- the shift of the gate at the hidden unit x -/
def kG (l x : ℕ) : ℕ := if routed D l x then (D.Pl l).kg' else (D.Pl l).kg
/-- the shift of the up projection at the hidden unit x -/
def kU (l x : ℕ) : ℕ := if routed D l x then (D.Pl l).ku' else (D.Pl l).ku
/-- the shift of QK in layer ℓ at x -/
def kQK (l x : ℕ) : ℕ := if x < D.dq then (D.Pl l).kq else (D.Pl l).kk

/-! ## The keys -/

open Site (site high ssite shigh)

/-- The key of the family s at (ℓ, x, i). "site A q rh k" = A + 2^(k−1) − 2^k q − 2^16 rh is the low
key of a rounding q = rhu(A, k) with the high digit rh, and "high rh k top" = 2^(top−k) rh its high
key (Inst/Model/Common/Site.lean). For valid scales (`NormPar.OK`) the two normalisations have
shifts from 17 on. A matrix product may have any shift: "ssite A q rh k" = 2^dn(k) (A + 2^(k−1) −
2^k q) − 2^16 rh with dn(k) = max(0, 16 − k), and
"shigh rh k top" = 2^(top−max(k,16)) rh; from 16 on these are site and high. -/
def key : Fam → ℕ → ℕ → ℕ → R
  | .G, l, x, i => ssite (Ag D t w l x i) (gw t l x i) (val t .rg l x i) (kG D l x)
  | .U, l, x, i => ssite (Au D t w l x i) (val t .up l x i) (val t .ru l x i) (kU D l x)
  | .UT, l, x, i => val t .up l x i + 2 ^ 15
  | .QK, l, x, i => ssite (Y' D t tb L0 w l x i) (val t .qkw l x i) (val t .rqk l x i) (kQK D l x)
  | .N1, l, x, i =>
    site (xS D t (2 * l) x i * Ledger.R (led t (2 * l) i)) (val t .aw l x i)
      (val t .ra l x i) (D.Pl l).n1.K
  | .N2, l, x, i =>
    site (xS D t (2 * l + 1) x i * Ledger.R (led t (2 * l + 1) i)) (val t .mw l x i)
      (val t .rm l x i) (D.Pl l).n2.K
  | .O, l, x, i =>
    ssite (∑ j ∈ range D.dq, val t .o l j i * (w l).Wo j x)
      (xS D t (2 * l + 1) x i - xS D t (2 * l) x i) (val t .ro l x i) (D.Pl l).ko
  | .D, l, x, i =>
    ssite (Ad D t w l x i) (xS D t (2 * l + 2) x i - xS D t (2 * l + 1) x i)
      (val t .rd l x i) (D.Pl l).kd
  | .V, l, x, i => ssite (Av D t w l x i) (val t .vw l x i) (val t .rv l x i) (D.Pl l).kv
  | .LR, l, x, i =>
    ssite (∑ j ∈ range D.d, val t .m l j i * (w l).Wr j x) (lw t (l / 2) x i)
      (val t .rl (l / 2) x i) (D.Pl l).kr
  | .XR, l, x, i => val t .sc (l / 2) 0 i * val t .m l x i + 2 ^ 15 - 2 ^ 16 * val t .xr (l / 2) x i
  | .LT, l, x, i => 2 * (val t .lr (l / 2) x i + 2 ^ 14)
  | .DD, l, x, i =>
    mr D t (l / 2) i - val t .lr (l / 2) x i -
      ∑ e ∈ (range D.nx).filter (x < ·), val t .sel (l / 2) e i
  | .GH, l, x, i => shigh (val t .rg l x i) (kG D l x) 24
  | .UH, l, x, i => shigh (val t .ru l x i) (kU D l x) 24
  | .OH, l, x, i => shigh (val t .ro l x i) (D.Pl l).ko 24
  | .DH, l, x, i => shigh (val t .rd l x i) (D.Pl l).kd 24
  | .VH, l, x, i => shigh (val t .rv l x i) (D.Pl l).kv 24
  | .LH, l, x, i => shigh (val t .rl (l / 2) x i) (D.Pl l).kr 24
  | .QKH, l, x, i => shigh (val t .rqk l x i) (kQK D l x) 32
  | .N1H, l, x, i => high (val t .ra l x i) (D.Pl l).n1.K 32
  | .N2H, l, x, i => high (val t .rm l x i) (D.Pl l).n2.K 32
  | .ROW, l, x, i =>
    ((Ledger.mu (x % nLedger) : ℤ) : R) * led t (2 * l + x / nLedger) i (x % nLedger)
  | .SEL, l, x, i => 128 * val t .sel (l / 2) x i
  | .L3, l, x, i => 32 * val t .l3 (l / 2) x i
  | .G0, l, x, i => val t .g0 l x i + 128
  | .CN1, l, x, i => (val t .aw l x i + 2 ^ 15) + 2 ^ 28 * (val t .a l x i + 2 ^ 11)
  | .CN2, l, x, i => (val t .mw l x i + 2 ^ 15) + 2 ^ 28 * (val t .m l x i + 2 ^ 11)
  | .CQK, l, x, i =>
    (val t .qkw l x i + 2 ^ 15) +
      2 ^ 28 * ((if x < D.dq then val t .q l x i else val t .kx l (x - D.dq) i) + 2 ^ 11)
  | .CV, l, x, i => (val t .vw l x i + 2 ^ 15) + 2 ^ 28 * (val t .v l x i + 2 ^ 11)
  | .CLR, l, x, i =>
    (val t .ly (l / 2) x i + 2 ^ 15) +
      2 ^ 25 * (val t .lr (l / 2) x i - val t .l3 (l / 2) x i) + 2 ^ 39
  | .F, l, x, i =>
    (val t .g0 l x i + 256 * val t .gc l x i + 2 ^ 15) + 2 ^ 28 * (val t .sl l x i + 2 ^ 12)
  | .MR, l, _, i => (mr D t (l / 2) i + 2 ^ 14) + 2 ^ 17 * val t .sc (l / 2) 0 i
  | .CG, l, x, i => (val t .gh l x i + 49152) + 2 ^ 28 * (val t .gc l x i + 128) + 2 ^ 40

/-- The key vector of a call, at the index X = (ℓ | ȷ | i) < 2^(a_c): the key of the family that
takes the column ȷ; at a padding position the padding value of the table. -/
def keyVec (c : Fin 8) (X : ℕ) : R :=
  match famAt D c (X / D.T % 2 ^ lJ D c) with
  | some (s, x) =>
    if present s (X / D.T / 2 ^ lJ D c) then key D t tb L0 w s (X / D.T / 2 ^ lJ D c) x (X % D.T)
    else (((lut tb c).pad : ℤ) : R)
  | none => (((lut tb c).pad : ℤ) : R)

/-- key number i of batch θ of the main lookup argument -/
def forestKey (θ i : ℕ) : R :=
  keyVec D t tb L0 w (callOf D θ) ((θ - firstTree D (callOf D θ)) * 2 ^ Dk D + i)

/-- the entries of a table, in R -/
def lutSet (L : Lut) : Set R := {v | ∃ ι : ℕ, ι < L.rows ∧ v = ((L.row ι : ℤ) : R)}

/-! ## The further identities -/

/-- jn k ν i: number k < 17 of the identities of the ledger of the norm instance ν at position i
((J1) for s = k < 9; 9, .., 16 are (J2) to (J9)); j10 ℓ′ i; j11 j i -/
inductive Idn
  | jn (k ν i : ℕ)
  | j10 (l' i : ℕ)
  | j11 (j i : ℕ)

/-- which identities belong to the segment; (J11) to the first segment only -/
def Idn.Valid (first : Bool) : Idn → Prop
  | .jn k ν i => k < 17 ∧ ν < D.nNu ∧ i < D.T
  | .j10 l' i => l' < D.ne ∧ i < D.T
  | .j11 j i => first = true ∧ j < D.d ∧ i < D.T

/-- the polynomial that has to vanish. emb is the embedding, tok the prompt. -/
def idnVal (emb : ℕ → ℕ → R) (tok : ℕ → ℕ) : Idn → R
  | .jn k ν i => Ledger.idn (npOf D ν) (Ledger.Wsum D.d fun l j => bS D t ν l j i) (led t ν i) k
  | .j10 l' i => ∑ e ∈ range D.nx, val t .sel l' e i - 1
  | .j11 j i => xS D t 0 j i - emb (tok i) j

end Arrays

/-! ## The field relation -/

/-- a trace that is given on the valid names, as a function on all names with values in a ring R:
the integer of a valid name, mapped into R; 0 at a name that is not valid -/
def rd (D : Dim) {R : Type} [CommRing R] (t : {c : Cell // c.Valid D} → ℤ) : Cell → R := fun c =>
  if h : c.Valid D then ((t ⟨c, h⟩ : ℤ) : R) else 0

/-- the keys of the field relation: (s, ℓ, x, i) with s present in layer ℓ -/
def KeyName (D : Dim) : Type :=
  {q : Fam × ℕ × ℕ × ℕ //
    q.2.1 < D.nl ∧ present q.1 q.2.1 = true ∧ q.2.2.1 < len D q.1 ∧ q.2.2.2 < D.T}

/-- The part of the field relation that belongs to a feed-forward segment. kW is the number of
column bits of the matrix W, L0 the first layer of the segment; the instance is the prompt, which
only (J11) reads. -/
def trace (D : Dim) (tb : Tables) (kW L0 : ℕ) (first : Bool) (F : Type) [CommRing F] :
    Blocks.TraceSpec F (ℕ → ℕ) where
  Cell := {c : Cell // c.Valid D}
  β := 18
  Key := KeyName D
  key := fun _ W t q =>
    key D (rd D t) tb L0 (fun l => layerR D.P kW W (L0 + l))
      q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2
  table := fun q => lutSet (lut tb (call q.val.1))
  Idn := {j : Idn // j.Valid D first}
  idn := fun tok W t j => idnVal D (rd D t) (embR D.P kW W) tok j.val

/-! ## The relation and the integer model: what Cm/TargetInstFFK.lean's statements are about -/

section Program
variable (D : Dim) (tb : Tables) (w : ℕ → LayerW) (L0 : ℕ) (t : Cell → ℤ)

/-- state s of the stream, with the arguments in the integer model's order: the position first -/
def stream (s : ℕ) : ℕ → Vec := fun i j => xS D t s j i

/-- What the relation gives without a fact from another segment, for layer ℓ: both normalisations,
with their intermediate values and range conditions; the projections; on all hidden units the steps
(U2) to (U4) as functions of gw, and the range conditions of (U2) and (U5); on the units that are
not routed, (U1) and (U5). And the bound (FL14) on the two states of the stream that are
normalised. -/
structure Part1 (l : ℕ) : Prop where
  /-- (PL2), (PL5): no range condition fails -/
  att : Att.OK (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l))
  aw : ∀ i < D.T, ∀ j < D.d, val t .aw l j i = Att.aw (D.Pl l) (stream D t (2 * l)) i j
  a : ∀ i < D.T, ∀ j < D.d, val t .a l j i = Att.a (D.Pl l) (stream D t (2 * l)) i j
  qkw : ∀ i < D.T,
    ∀ c < D.dqk, val t .qkw l c i = Att.qkw (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i c
  q : ∀ i < D.T,
    ∀ c < D.dq, val t .q l c i = Att.q (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i c
  kx : ∀ i < D.T,
    ∀ c < D.dkv, val t .kx l c i = Att.kx (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i c
  vw : ∀ i < D.T, ∀ c < D.dkv, val t .vw l c i = Att.vw (D.Pl l) (w l) (stream D t (2 * l)) i c
  v : ∀ i < D.T, ∀ c < D.dkv, val t .v l c i = Att.v (D.Pl l) (w l) (stream D t (2 * l)) i c
  /-- (PL8) -/
  n2 : ∀ i < D.T, NORM.OK (D.Pl l).n2 D.d (stream D t (2 * l + 1) i)
  mw : ∀ i < D.T, ∀ j < D.d, val t .mw l j i = FF.mw (D.Pl l) (stream D t (2 * l + 1)) i j
  m : ∀ i < D.T, ∀ j < D.d, val t .m l j i = FF.m (D.Pl l) (stream D t (2 * l + 1)) i j
  /-- the intermediate values of both normalisations -/
  led : ∀ n < 2, ∀ i < D.T,
    Ledger.Vlo (led t (2 * l + n) i) + 2 ^ 48 * Ledger.Vhi (led t (2 * l + n) i) =
      NORM.V D.d (stream D t (2 * l + n) i) ∧
    Ledger.sig (led t (2 * l + n) i) =
      NORM.sig (npOf D (2 * l + n)) D.d (stream D t (2 * l + n) i) ∧
    Ledger.R (led t (2 * l + n) i) = NORM.R (npOf D (2 * l + n)) D.d (stream D t (2 * l + n) i)
  /-- (FL14) -/
  bound : ∀ n < 2, ∀ i < D.T, ∀ j < D.d, |xS D t (2 * l + n) j i| < 2 ^ 39
  /-- (U2) to (U4), and the range conditions of (U2) and (U5), on all hidden units -/
  g0 : ∀ i < D.T, ∀ x < D.f, val t .g0 l x i = lowByte (gw t l x i)
  ghR : ∀ i < D.T, ∀ x < D.f, -2 ^ 14 ≤ val t .gh l x i ∧ val t .gh l x i < 2 ^ 14
  gc : ∀ i < D.T, ∀ x < D.f, val t .gc l x i = clamp 127 (val t .gh l x i)
  sl : ∀ i < D.T,
    ∀ x < D.f, val t .sl l x i = tb.SILU (256 * val t .gc l x i + val t .g0 l x i + 2 ^ 15)
  upR : ∀ i < D.T, ∀ x < D.f, Fits16 (val t .up l x i)
  /-- (U1), (U5) on a dense layer and on the shared expert -/
  gwS : ∀ i < D.T, ∀ x < D.f, routed D l x = false →
    gw t l x i = rhu (dot D.d (fun j => val t .m l j i) fun j => (w l).Wg j x) (D.Pl l).kg
  upS : ∀ i < D.T, ∀ x < D.f, routed D l x = false →
    val t .up l x i = rhu (dot D.d (fun j => val t .m l j i) fun j => (w l).Wu j x) (D.Pl l).ku

/-- (FA12), a fact of the attention segment of the group: |o[j]| ≤ 2,047 -/
def OBound : Prop := ∀ l < D.nl, ∀ i < D.T, ∀ j < D.dq, |val t .o l j i| ≤ 2047

/-- (PL7): x_(2ℓ+1) is the value that the output projection computes from x_(2ℓ) and o. -/
def Part2 (l : ℕ) : Prop :=
  ∀ i < D.T, ∀ c < D.d, xS D t (2 * l + 1) c i =
    xS D t (2 * l) c i + rhu (dot D.dq (fun j => val t .o l j i) fun j => (w l).Wo j c) (D.Pl l).ko

/-- (FL19), a fact of the next feed-forward segment or of the head: |x_8[j]| < 2^39 -/
def LastBound : Prop := ∀ i < D.T, ∀ j < D.d, |xS D t (2 * D.nl) j i| < 2 ^ 39

/-- The feed-forward block, for layer ℓ: the router and the input of the routed expert in a layer
with experts; no range condition of (PL8) to (PL13) fails; x_(2ℓ+2) is the integer model's. -/
structure Part3 (l : ℕ) : Prop where
  ly : isExpL l = true →
    ∀ i < D.T, ∀ e < D.nx, val t .ly (l / 2) e i = FF.ly (D.Pl l) (w l) (stream D t (2 * l + 1)) i e
  l3 : isExpL l = true →
    ∀ i < D.T, ∀ e < D.nx, val t .l3 (l / 2) e i = FF.l3 (D.Pl l) (w l) (stream D t (2 * l + 1)) i e
  lr : isExpL l = true →
    ∀ i < D.T, ∀ e < D.nx, val t .lr (l / 2) e i = FF.lr (D.Pl l) (w l) (stream D t (2 * l + 1)) i e
  sel : isExpL l = true →
    ∀ i < D.T, ∀ e < D.nx,
      val t .sel (l / 2) e i = if e = FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i then 1 else 0
  sc : isExpL l = true →
    ∀ i < D.T, val t .sc (l / 2) 0 i = FF.sc (D.Pl l) tb (w l) (stream D t (2 * l + 1)) i
  xr : isExpL l = true →
    ∀ i < D.T,
      ∀ j < D.d, val t .xr (l / 2) j i = FF.xr (D.Pl l) tb (w l) (stream D t (2 * l + 1)) i j
  /-- sl and up of every hidden unit are those of the integer model -/
  slP : ∀ i < D.T, ∀ x < D.f, val t .sl l x i =
    UNIT.sl tb D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x)
      (FF.wg (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x) (FF.kG (D.Pl l) (L0 + l) x)
  upP : ∀ i < D.T, ∀ x < D.f, val t .up l x i =
    UNIT.up D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x)
      (FF.wu (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x) (FF.kU (D.Pl l) (L0 + l) x)
  ok : FF.OK (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1))
  /-- (PL13) -/
  out : ∀ i < D.T, ∀ c < D.d,
    xS D t (2 * l + 2) c i = FF.x'' (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i c

/-! ## The honest trace -/

variable (x : ℕ → ℕ → Vec) (o : ℕ → ℕ → Vec)

/-- The honest value of every array, from the integer model: x s is state s of the stream in the
segment, o ℓ the output of attention in layer ℓ. A high digit is the quotient by 2^16 of the
remainder of its rounding (`Site.hd`). The arrays of the router have the instance ℓ′, which is layer
2ℓ′ + 1. -/
def hv : Arr → ℕ → ℕ → ℕ → ℤ
  | .x0, _, j, i => x 0 i j
  | .x8, _, j, i => x (2 * D.nl) i j
  | .xs, s, j, i => x (s + 1) i j
  | .aw, l, j, i => Att.aw (D.Pl l) (x (2 * l)) i j
  | .a, l, j, i => Att.a (D.Pl l) (x (2 * l)) i j
  | .ra, l, j, i => Site.hd (x (2 * l) i j * NORM.R (D.Pl l).n1 D.d (x (2 * l) i)) (D.Pl l).n1.K
  | .mw, l, j, i => FF.mw (D.Pl l) (x (2 * l + 1)) i j
  | .m, l, j, i => FF.m (D.Pl l) (x (2 * l + 1)) i j
  | .rm, l, j, i =>
    Site.hd (x (2 * l + 1) i j * NORM.R (D.Pl l).n2 D.d (x (2 * l + 1) i)) (D.Pl l).n2.K
  | .D, ν, n, i => Ledger.hon (npOf D ν) D.d (fun l j => cellW 5 (x ν i j) l) n
  | .qkw, l, c, i => Att.qkw (D.Pl l) tb (w l) (L0 + l) (x (2 * l)) i c
  | .rqk, l, c, i => Site.hd (Att.Y' (D.Pl l) tb (w l) (L0 + l) (x (2 * l)) i c) (kQK D l c)
  | .q, l, c, i => Att.q (D.Pl l) tb (w l) (L0 + l) (x (2 * l)) i c
  | .kx, l, c, i => Att.kx (D.Pl l) tb (w l) (L0 + l) (x (2 * l)) i c
  | .vw, l, c, i => Att.vw (D.Pl l) (w l) (x (2 * l)) i c
  | .rv, l, c, i => Site.hd (Att.Av (D.Pl l) (w l) (x (2 * l)) i c) (D.Pl l).kv
  | .v, l, c, i => Att.v (D.Pl l) (w l) (x (2 * l)) i c
  | .o, l, j, i => o l i j
  | .ro, l, c, i => Site.hd (dot D.dq (o l i) fun j => (w l).Wo j c) (D.Pl l).ko
  | .rd, l, c, i => Site.hd (FF.Ad (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i c) (D.Pl l).kd
  | .g0, l, j, i =>
    UNIT.g0 D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i j)
      (FF.wg (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i j) (FF.kG (D.Pl l) (L0 + l) j)
  | .gh, l, j, i =>
    UNIT.gh D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i j)
      (FF.wg (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i j) (FF.kG (D.Pl l) (L0 + l) j)
  | .gc, l, j, i =>
    UNIT.gc D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i j)
      (FF.wg (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i j) (FF.kG (D.Pl l) (L0 + l) j)
  | .sl, l, j, i =>
    UNIT.sl tb D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i j)
      (FF.wg (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i j) (FF.kG (D.Pl l) (L0 + l) j)
  | .up, l, j, i =>
    UNIT.up D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i j)
      (FF.wu (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i j) (FF.kU (D.Pl l) (L0 + l) j)
  | .rg, l, j, i =>
    Site.hd (dot D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i j)
        (FF.wg (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i j))
      (FF.kG (D.Pl l) (L0 + l) j)
  | .ru, l, j, i =>
    Site.hd (dot D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i j)
        (FF.wu (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i j))
      (FF.kU (D.Pl l) (L0 + l) j)
  | .ly, l', e, i => FF.ly (D.Pl (2 * l' + 1)) (w (2 * l' + 1)) (x (4 * l' + 3)) i e
  | .l3, l', e, i => FF.l3 (D.Pl (2 * l' + 1)) (w (2 * l' + 1)) (x (4 * l' + 3)) i e
  | .lr, l', e, i => FF.lr (D.Pl (2 * l' + 1)) (w (2 * l' + 1)) (x (4 * l' + 3)) i e
  | .rl, l', e, i =>
    Site.hd (dot D.d (FF.m (D.Pl (2 * l' + 1)) (x (4 * l' + 3)) i) fun j => (w (2 * l' + 1)).Wr j e)
      (D.Pl (2 * l' + 1)).kr
  | .sel, l', e, i =>
    if e = FF.es (D.Pl (2 * l' + 1)) (w (2 * l' + 1)) (x (4 * l' + 3)) i then 1 else 0
  | .sc, l', _, i => FF.sc (D.Pl (2 * l' + 1)) tb (w (2 * l' + 1)) (x (4 * l' + 3)) i
  | .xr, l', j, i => FF.xr (D.Pl (2 * l' + 1)) tb (w (2 * l' + 1)) (x (4 * l' + 3)) i j

/-- The honest trace: the value minus the offset of the array, in the digits of the widened cell
rule. -/
def hon (c : Cell) : ℤ := cellW c.X.nCell (hv D tb w L0 x o c.X c.inst c.j c.i - c.X.off) c.k

/-- The steps of the segment lead from state to state of the stream, and none of their range
conditions fails: (PL7) with the given outputs o of attention, which are at most 2,047 in absolute
value, and (PL13). -/
structure Runs : Prop where
  att : ∀ l < D.nl, Att.OK (D.Pl l) tb (w l) (L0 + l) (x (2 * l))
  ff : ∀ l < D.nl, FF.OK (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1))
  pl7 : ∀ l < D.nl, ∀ i < D.T, ∀ c < D.d,
    x (2 * l + 1) i c = x (2 * l) i c + rhu (dot D.dq (o l i) fun j => (w l).Wo j c) (D.Pl l).ko
  pl13 : ∀ l < D.nl,
    ∀ i < D.T, ∀ c < D.d, x (2 * l + 2) i c = FF.x'' (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i c
  o : ∀ l < D.nl, ∀ i < D.T, ∀ j < D.dq, |o l i j| ≤ 2047
  /-- every value of the stream can be written in five cells -/
  wr : ∀ s ≤ 2 * D.nl, ∀ i < D.T, ∀ j < D.d, Writable 5 (x s i j)

end Program

namespace Spec

/-- The key vector of a call holds the keys at the columns of the index map: the key of a family
that is present in layer ℓ, at x below its length and i < T. -/
def keyVecAt : Prop :=
  ∀ (R : Type) [CommRing R] (D : Dim) (t : Cell → R) (tb : Tables) (L0 : ℕ)
      (w : ℕ → LW R) (s : Fam) (l x i : ℕ),
    x < len D s → i < D.T → present s l = true →
    keyVec D t tb L0 w (call s) (keyIdx D (call s) l (pos D s x) i) = key D t tb L0 w s l x i

/-- The setting of the statements on the integer model: the reference sizes (the scales are those of
`scl`), tables with the ranges of `Tables.OK` (Inst/Model/Tables.lean), a well-formed
matrix W, a segment of four layers that starts at an even layer and ends within the model's layers,
tokens in the vocabulary. -/
structure Setting (tb : Tables) (W : Mat) (L0 : ℕ) (tok : ℕ → ℕ) : Prop where
  tab : tb.OK (Dim.ref.Pl 0)
  wf : Layout.WFW ppref Layout.kRef W Layout.hRef
  even : L0 % 2 = 0
  layers : L0 + Dim.ref.nl ≤ ppref.layers
  tok : ∀ i, tok i < ppref.V

/-- The honest trace, over the integers. The statement assumes `Setting` and `Runs`. If the steps of
the segment lead from state to state of the stream x, with the outputs o of attention: (a) every
cell of the honest trace is at most 128 in absolute value (128 included: the widened cell rule of
Inst/Model/Widened.lean), and the read-out of every array is its honest value at the array's own
indices; (b) every key is an entry of its table, as an integer; (c) the identities (J1) to (J10)
hold over the integers, and in the first segment (J11), if x 0 is the embedding of the prompt. (A
statement; proved for valid scales, `[Lawful]`, in Inst/Model/FF/Honest.lean.) -/
def honest : Prop :=
  ∀ (tb : Tables) (W : Mat) (L0 : ℕ) (tok : ℕ → ℕ), Setting tb W L0 tok →
    ∀ (x : ℕ → ℕ → Vec) (o : ℕ → ℕ → Vec),
      Runs Dim.ref tb (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o →
      (∀ c : Cell, c.Valid Dim.ref →
        |hon Dim.ref tb (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o c| ≤ 128) ∧
      (∀ (X : Arr) (n j i : ℕ), n < X.cnt Dim.ref → j < X.width Dim.ref → i < Dim.ref.T →
        val (hon Dim.ref tb (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o) X n j i =
          hv Dim.ref tb (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o X n j i) ∧
      (∀ q : KeyName Dim.ref,
        key Dim.ref (hon Dim.ref tb (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o)
            tb L0 (fun l => LW.ofInt ℤ (Layout.layerOf ppref Layout.kRef W (L0 + l))) q.val.1
            q.val.2.1 q.val.2.2.1 q.val.2.2.2 ∈
          lutSet (R := ℤ) (lut tb (call q.val.1))) ∧
      ∀ first : Bool,
        (first = true →
          ∀ i < Dim.ref.T,
            ∀ j < Dim.ref.d, x 0 i j = (Layout.weightsOf ppref Layout.kRef W).Emb (tok i) j) →
        ∀ j : Idn, j.Valid Dim.ref first →
          idnVal Dim.ref
              (hon Dim.ref tb (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 x o)
              (Layout.weightsOf ppref Layout.kRef W).Emb tok j = 0

end Spec

end Inst.Model.FFSeg
