-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/Index.lean: sizes and index maps of a feed-forward segment: how the cells of its
  trace are arranged in matrices, and how its looked-up values (keys in Lean names) are numbered.

  What each array holds of the integer program is said by `hv`, what each family looks up by `key`
  (both Inst/Model/FF/Trace.lean). A call's keys are in batches of at most 2^cap keys (trees in Lean
  names; trace, cell, call, key: lean/GLOSSARY.md). The sizes are a parameter, `Dim` (the parameters
  of the model, and the numbers of bits that the format adds), so that a small segment can be
  evaluated. `Dim.ref` holds the reference sizes.

  * `Arr`: the arrays other than B (the bits in the matrix b, `addrB`), each with the number of
    cells of a value, the number of instances, the width, the offset and the matrix. `feat`: the
    number of a feature, that is of an (array, cell of a value, instance, channel).
  * `Mx`, `addr`: the parts of af (three at `Dim.ref`) are one matrix here (`afPart`). `Fam`,
    `fams`: the 34 families of keys in their 8 calls.
  * `pos`: the index map of a call. A family is split into pieces by the binary digits of its
    length; the pieces of a call are sorted by size, largest first, keeping the order of pieces of
    equal size, and get consecutive columns. Here this is a formula (`bitOf`, `colBase`; a family
    has at most one piece of each size). `famAt` is the inverse of `pos`.
  * `ref_*` (but for `ref_qkOne`, below): the numerical values at the reference sizes, and `Dim.OK`
    there (`ref_ok`), proved by evaluation.
  * `Spec.*`: the facts on the index map and on addresses, proved in Inst/Model/FF/IndexFacts.lean.

  Sizes and scales are separate: of `Dim` only sizes are read (its field `P` is a `Params`, whose
  scales of a layer `Dim.Pl` replaces). The public quantization scales of the segment (ten shifts
  and the constants of two normalisations for each layer) are the field `κ` of the class `Scl`
  (Inst/Model/Scl.lean), the instance argument `[scl : Scl]`. `Dim.Pl D l`, the parameters of layer
  l of the segment, is the sizes of `D.P` with the scales `κ l`. It is the only function of this
  directory that reads the scales (the property `Lawful` is about them too): whatever reads a scale,
  for all scales, does so through `Dim.Pl` and has the argument `[scl : Scl]`. A definition without
  that argument either reads no scale (so all arrays, matrices, addresses, families, calls, batches
  and padding positions of this file) or is at the reference scales only.
  In a file that does not switch this default off (this one does), Lean takes the reference scales
  `Scl.ref` (the scales of `ppref` in every layer) where no instance of `Scl` is in scope. That is
  only a default, for the files that are about the reference parameters only: no claim is made that
  it suits the weights of any real model (where its numbers come from: lean/CREDITS.md, section 8).
  `Dim.QKOne`, `ref_qkOne`: queries and keys have one shift unless both shifts are 16 or more. At
  `Dim.ref` this holds for valid scales (`[Lawful]`, Inst/Model/FF/Lawful.lean).

  Notation (the signs of the doc comments, with their Lean names): n_X: `nCell`: the number of cells
  of a value; cnt_X: `cnt`: the number of instances; J_X: `width`: the width; OFF_X: `OFF`: the
  first feature of an array; n_s: `len`: the length of a family; J_c: 2^(`lJ` c); a_c: `aC`: call c
  has 2^(a_c) keys; D, where a number is meant: `Dk` (the variable `D` is a `Dim`); N_T: `NT`: the
  number of batches of all calls together; σ: `sg`; ϕ_θ: `padCount`: the number of padding positions
  of the batch θ; pre_c: `pre`: the prefix of a call; n_1: 2^(`lRow` μ), the number of rows; n_2:
  `nCol`: the number of columns of a matrix, filler included; m_Z: `mZ`: the rows of all matrices
  together, each part of af counted; B[ι, θ, π]: the bit whose row and column in the matrix b are
  `addrB ι θ π`.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Tables
import Inst.Model.FF.Lawful

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset

/-- The sizes of a feed-forward segment. -/
structure Dim where
  /-- the parameters of the model -/
  P : Params
  /-- 2^lT positions -/
  lT : ℕ
  /-- 2^lL layers in a segment; the odd ones have experts -/
  lL : ℕ
  /-- 2^fBig features in a column of af, qa, xin, xout -/
  fBig : ℕ
  /-- 2^fAd features in a column of ad -/
  fAd : ℕ
  /-- 2^fAr features in a column of ar -/
  fAr : ℕ
  /-- the number of parts of af -/
  parts : ℕ
  /-- a batch has at most 2^cap keys -/
  cap : ℕ
  /-- a table of the look-up argument has 2^r rows. The tables of Inst/Model/Tables.lean have 2^16
  or 2^8 rows, so only r = 16 fits them. -/
  r : ℕ
  /-- a multiplicity has 2^lp bits -/
  lp : ℕ

/-- the reference parameters -/
def Dim.ref : Dim := ⟨ppref, 10, 2, 6, 5, 3, 3, 28, 16, 5⟩

namespace Dim
variable (D : Dim)

/-- the parameters of layer ℓ of the segment: the sizes of P with the scales of that layer -/
def Pl (l : ℕ) : Params := D.P.at (Scl.κ l)

/-! the sizes of a layer's parameters are those of P -/
theorem Pl_T (l : ℕ) : (D.Pl l).T = D.P.T := rfl
theorem Pl_V (l : ℕ) : (D.Pl l).V = D.P.V := rfl
theorem Pl_layers (l : ℕ) : (D.Pl l).layers = D.P.layers := rfl
theorem Pl_d (l : ℕ) : (D.Pl l).d = D.P.d := rfl
theorem Pl_nq (l : ℕ) : (D.Pl l).nq = D.P.nq := rfl
theorem Pl_nkv (l : ℕ) : (D.Pl l).nkv = D.P.nkv := rfl
theorem Pl_ch (l : ℕ) : (D.Pl l).ch = D.P.ch := rfl
theorem Pl_f (l : ℕ) : (D.Pl l).f = D.P.f := rfl
theorem Pl_fe (l : ℕ) : (D.Pl l).fe = D.P.fe := rfl
theorem Pl_nexp (l : ℕ) : (D.Pl l).nexp = D.P.nexp := rfl

/-- positions i -/
def T : ℕ := 2 ^ D.lT
/-- layers ℓ of the segment -/
def nl : ℕ := 2 ^ D.lL
/-- layers with experts ℓ = 2ℓ′ + 1 -/
def ne : ℕ := D.nl / 2
/-- norm instances ν = 2ℓ + n -/
def nNu : ℕ := 2 * D.nl
/-- the width of the stream -/
def d : ℕ := D.P.d
/-- the width of all query heads together -/
def dq : ℕ := D.P.nq * D.P.ch
/-- the width of all key heads together, and of all value heads -/
def dkv : ℕ := D.P.nkv * D.P.ch
/-- the width of queries and keys together -/
def dqk : ℕ := D.dq + D.dkv
/-- the number of hidden units of a layer -/
def f : ℕ := D.P.f
/-- the number of hidden units of one expert -/
def fe : ℕ := D.P.fe
/-- the number of experts -/
def nx : ℕ := D.P.nexp

end Dim

/-- "Layers ℓ = 1, 3 have experts" -/
def isExpL (l : ℕ) : Bool := l % 2 == 1

/-- the number of bytes of the ledger of a norm instance at a position (the ledger holds the
intermediate values of a normalisation: Inst/Model/Common/Ledger.lean) -/
def nLedger : ℕ := 99

/-! ## Arrays, features, matrices -/

/-- the matrices of cells; `af` denotes all its parts together -/
inductive Mx
  | af | ad | ar | b | qa | xin | xout
  deriving DecidableEq, Repr

/-- The arrays other than B. xs holds the stream at the indices 1, .., 2 nl − 1; x0 and x8 hold it
at the first and the last index. By `hv` (Inst/Model/FF/Trace.lean: the honest value of every array,
from the integer model): aw, a, qkw, q, kx, vw, v: the functions of these names in `Att`
(Inst/Model/Program.lean); mw, m, ly, l3, lr, sc, xr: in `FF`; g0, gh, gc, sl, up: in `UNIT`; o: the
output of attention; ra, rm, rqk, rv, ro, rd, rg, ru, rl: high digits (`Site.hd`); sel: 1 at the
expert `FF.es`, else 0; D: the ledger of a norm instance (`Ledger.hon`). -/
inductive Arr
  | g0 | gc | sl | up | rg | ru | xs | ro | rd | aw | ra | mw | rm | qkw | rqk | vw | rv | gh
  | a | m | xr
  | lr | rl | sel | sc | D | ly | l3
  | q | kx | v | o
  | x0 | x8
  deriving DecidableEq, Repr

namespace Arr

/-- the matrix of an array -/
def mx : Arr → Mx
  | .g0 | .gc | .sl | .up | .rg | .ru | .xs | .ro | .rd | .aw | .ra | .mw | .rm | .qkw | .rqk | .vw | .rv | .gh => .af
  | .a | .m | .xr => .ad
  | .lr | .rl | .sel | .sc | .D | .ly | .l3 => .ar
  | .q | .kx | .v | .o => .qa
  | .x0 => .xin
  | .x8 => .xout

/-- n_X: the number of cells of a value -/
def nCell : Arr → ℕ
  | .xs | .x0 | .x8 => 5
  | .sc => 3
  | .sl | .up | .aw | .ra | .mw | .rm | .qkw | .rqk | .vw | .gh | .a | .m | .xr | .lr | .ly | .q | .kx | .v | .o => 2
  | .g0 | .gc | .rg | .ru | .ro | .rd | .rv | .rl | .sel | .D | .l3 => 1

/-- the offset in the formula of `val` (Inst/Model/FF/Trace.lean) -/
def off : Arr → ℤ
  | .ra | .rm | .rqk => 32896
  | .rg | .ru | .ro | .rd | .rv | .rl | .D => 128
  | _ => 0

variable (D : Dim)

/-- cnt_X: the number of instances -/
def cnt : Arr → ℕ
  | .xs => 2 * D.nl - 1
  | .x0 | .x8 => 1
  | .D => D.nNu
  | .xr | .lr | .rl | .sel | .sc | .ly | .l3 => D.ne
  | _ => D.nl

/-- J_X: the width -/
def width : Arr → ℕ
  | .g0 | .gc | .sl | .up | .rg | .ru | .gh => D.f
  | .xs | .x0 | .x8 | .ro | .rd | .aw | .ra | .mw | .rm | .a | .m | .xr => D.d
  | .qkw | .rqk => D.dqk
  | .q | .o => D.dq
  | .vw | .rv | .kx | .v => D.dkv
  | .lr | .rl | .sel | .ly | .l3 => D.nx
  | .sc => 1
  | .D => nLedger

/-- the number of features of an array -/
def nFeat (X : Arr) : ℕ := X.nCell * X.cnt D * X.width D

end Arr

/-- the arrays of a matrix, in their order -/
def arrs : Mx → List Arr
  | .af => [.g0, .gc, .sl, .up, .rg, .ru, .xs, .ro, .rd, .aw, .ra, .mw, .rm, .qkw, .rqk, .vw, .rv, .gh]
  | .ad => [.a, .m, .xr]
  | .ar => [.lr, .rl, .sel, .sc, .D, .ly, .l3]
  | .b => []
  | .qa => [.q, .kx, .v, .o]
  | .xin => [.x0]
  | .xout => [.x8]

variable (D : Dim)

/-- OFF_X: the first feature of an array -/
def OFF (X : Arr) : ℕ := (((arrs X.mx).takeWhile (· != X)).map (Arr.nFeat D)).sum

/-- feat_X(k, inst, j) = OFF_X + (k cnt_X + inst) J_X + j -/
def feat (X : Arr) (k inst j : ℕ) : ℕ := OFF D X + (k * X.cnt D + inst) * X.width D + j

/-- the features of a matrix, without filler -/
def nFeatMx (μ : Mx) : ℕ := ((arrs μ).map (Arr.nFeat D)).sum

/-- the number of bits of the features in a column -/
def lFeat : Mx → ℕ
  | .af | .qa | .xin | .xout => D.fBig
  | .ad => D.fAd
  | .ar => D.fAr
  | .b => 0

/-- log2 of n_1, the number of rows -/
def lRow : Mx → ℕ
  | .b => D.r
  | μ => lFeat D μ + D.lT

/-- the columns of one part of af: its features are filled up to whole columns, and to parts of
equal size -/
def afCols : ℕ := ((nFeatMx D .af + 2 ^ D.fBig - 1) / 2 ^ D.fBig + D.parts - 1) / D.parts

/-- the row and the column of the matrix b that hold the bit B[ι, θ, π]: with N = (θ 2^r + ι) 2^lp +
π these are N mod 2^r and ⌊N / 2^r⌋ -/
def addrB (ι θ π : ℕ) : ℕ × ℕ :=
  (((θ * 2 ^ D.r + ι) * 2 ^ D.lp + π) % 2 ^ D.r, ((θ * 2 ^ D.r + ι) * 2 ^ D.lp + π) / 2 ^ D.r)

/-- feature φ at position i is the cell in the row (φ mod 2^f) 2^lT + i and the column ⌊φ / 2^f⌋ -/
def featAt (μ : Mx) (φ i : ℕ) : ℕ × ℕ := ((φ % 2 ^ lFeat D μ) * D.T + i, φ / 2 ^ lFeat D μ)

/-- column c of af is column c mod afCols of part ⌊c / afCols⌋ -/
def afPart (c : ℕ) : ℕ × ℕ := (c / afCols D, c % afCols D)

/-- The names of the cells: the array, the number k of the cell in a value, the instance, the
channel j and the position i. -/
structure Cell where
  X : Arr
  k : ℕ
  inst : ℕ
  j : ℕ
  i : ℕ
  deriving DecidableEq, Repr

/-- which names are cells -/
def Cell.Valid (c : Cell) : Prop :=
  c.k < c.X.nCell ∧ c.inst < c.X.cnt D ∧ c.j < c.X.width D ∧ c.i < D.T

instance (c : Cell) : Decidable (c.Valid D) := by unfold Cell.Valid; infer_instance

/-- the matrix, the row and the column of a cell -/
def addr (c : Cell) : Mx × ℕ × ℕ := (c.X.mx, featAt D c.X.mx (feat D c.X c.k c.inst c.j) c.i)

/-! ## Families and calls -/

/-- The families of keys. By `key` (Inst/Model/FF/Trace.lean): G, U, QK, O, D, V, LR: the low key of
a rounding of a matrix product (`ssite`); GH, UH, QKH, OH, DH, VH, LH: its high key (`shigh`); N1,
N2 and N1H, N2H: the same for the two normalisations (`site`, `high`); the other sixteen: see `key`.
-/
inductive Fam
  | G | U | UT | QK | N1 | N2 | O | D | V | LR | XR | LT | DD | GH | UH | OH | DH | VH | LH | QKH | N1H | N2H | ROW | SEL | L3 | G0
  | CN1 | CN2 | CQK | CV | CLR | F | MR | CG
  deriving DecidableEq, Repr

/-- n_s: the length of a family -/
def len : Fam → ℕ
  | .G | .U | .UT | .GH | .UH | .G0 | .F | .CG => D.f
  | .QK | .QKH | .CQK => D.dqk
  | .N1 | .N2 | .O | .D | .XR | .OH | .DH | .N1H | .N2H | .CN1 | .CN2 => D.d
  | .V | .VH | .CV => D.dkv
  | .LR | .LT | .DD | .LH | .SEL | .L3 | .CLR => D.nx
  | .ROW => 2 * nLedger
  | .MR => 1

/-- the family has keys only in the layers with experts -/
def isExp : Fam → Bool
  | .LR | .XR | .LT | .DD | .LH | .SEL | .L3 | .CLR | .MR => true
  | _ => false

/-- the family is present in layer ℓ -/
def present (s : Fam) (l : ℕ) : Bool := !isExp s || isExpL l

/-- The eight calls: their families, in order. The calls are counted from 0. -/
def fams : Fin 8 → List Fam
  | 0 => [.G, .U]
  | 1 => [.N1, .N1H, .N2, .N2H, .O, .D, .V]
  | 2 => [.QK, .QKH, .XR, .LR, .LT, .DD]
  | 3 => [.GH, .UH, .OH, .DH, .VH, .ROW, .LH, .SEL, .L3, .G0]
  | 4 => [.CN1, .CN2, .CQK, .CV, .CLR]
  | 5 => [.MR, .CG]
  | 6 => [.F]
  | 7 => [.UT]

/-- the call of a family -/
def call : Fam → Fin 8
  | .G | .U => 0
  | .N1 | .N1H | .N2 | .N2H | .O | .D | .V => 1
  | .QK | .QKH | .XR | .LR | .LT | .DD => 2
  | .GH | .UH | .OH | .DH | .VH | .ROW | .LH | .SEL | .L3 | .G0 => 3
  | .CN1 | .CN2 | .CQK | .CV | .CLR => 4
  | .MR | .CG => 5
  | .F => 6
  | .UT => 7

/-- the table of a call -/
def lut (tb : Tables) : Fin 8 → Lut
  | 0 | 1 | 2 | 7 => R16
  | 3 => R8
  | 4 => FC
  | 5 => FS tb
  | 6 => FL tb

/-! ## The index map of the calls -/

/-- the exponent of the piece of a family of length n that contains the index x < n: the highest bit
in which x and n differ -/
def bitOf (n x : ℕ) : ℕ := Nat.log2 (n ^^^ x)

/-- the first index of the piece of size 2^b of a family of length n -/
def pieceStart (n b : ℕ) : ℕ := n / 2 ^ (b + 1) * 2 ^ (b + 1)

/-- the position of a family in the list of its call -/
def ord (s : Fam) : ℕ := (fams (call s)).idxOf s

/-- the first column of the piece of size 2^b of the family s: the sizes of all pieces of the call
that are larger, or as large and of an earlier family -/
def colBase (s : Fam) (b : ℕ) : ℕ :=
  ((fams (call s)).map fun s' =>
    ∑ b' ∈ range (Nat.size (len D s')), if (len D s').testBit b' ∧
    (b < b' ∨ (b' = b ∧ ord s' < ord s)) then 2 ^ b'
    else 0).sum

/-- pos_s[x]: the column of the index x of the family s -/
def pos (s : Fam) (x : ℕ) : ℕ := colBase D s (bitOf (len D s) x) + x % 2 ^ bitOf (len D s) x

/-- the pieces of a call: family and exponent -/
def pieces (c : Fin 8) : List (Fam × ℕ) :=
  (fams c).flatMap fun s =>
    ((List.range (Nat.size (len D s))).filter (len D s).testBit).map fun b => (s, b)

/-- the family and the index that take the column ȷ of the call c, if any -/
def famAt (c : Fin 8) (jj : ℕ) : Option (Fam × ℕ) :=
  (pieces D c).findSome? fun p =>
    if colBase D p.1 p.2 ≤ jj ∧ jj < colBase D p.1 p.2 + 2 ^ p.2 then
      some (p.1, pieceStart (len D p.1) p.2 + (jj - colBase D p.1 p.2))
    else none

/-- the number of columns that the families of a call take -/
def used (c : Fin 8) : ℕ := ((fams c).map (len D)).sum
/-- the number of columns that they take in layer ℓ -/
def usedIn (c : Fin 8) (l : ℕ) : ℕ := (((fams c).filter (present · l)).map (len D)).sum

/-- log2 of J_c, "the least power of two that holds the columns used" -/
def lJ (c : Fin 8) : ℕ := Nat.clog 2 (used D c)

/-- a_c: call c has 2^(a_c) keys, with the index (ℓ | ȷ | i) -/
def aC (c : Fin 8) : ℕ := D.lL + lJ D c + D.lT

/-- the index (ℓ | ȷ | i) of a key, as a number -/
def keyIdx (c : Fin 8) (l jj i : ℕ) : ℕ := (l * 2 ^ lJ D c + jj) * D.T + i

/-! ## Batches and padding positions -/

/-- D = min(cap, min_c a_c) -/
def Dk : ℕ := (List.finRange 8).foldl (fun m c => min m (aC D c)) D.cap

/-- the number of batches of a call -/
def trees (c : Fin 8) : ℕ := 2 ^ (aC D c - Dk D)

/-- the first batch of a call: "the largest calls first; calls of equal size keep the order of the
table" (their order in `fams`) -/
def firstTree (c : Fin 8) : ℕ :=
  ∑ c' : Fin 8, if aC D c < aC D c' ∨ (aC D c' = aC D c ∧ c' < c) then trees D c' else 0

/-- N_T: the number of batches of all calls together -/
def NT : ℕ := ∑ c : Fin 8, trees D c

/-- σ = ⌈log2 N_T⌉ -/
def sg : ℕ := Nat.clog 2 (NT D)

/-- the call of a batch -/
def callOf (θ : ℕ) : Fin 8 :=
  ((List.finRange 8).find? fun c => firstTree D c ≤ θ ∧ θ < firstTree D c + trees D c).getD 0

/-- the number of layers whose keys one batch of the call c holds -/
def layersIn (c : Fin 8) : ℕ := D.nl / trees D c

/-- the column ȷ of call c is padding in layer ℓ: no family takes it, or the family that takes it is
not present -/
def isPad (c : Fin 8) (l jj : ℕ) : Bool :=
  match famAt D c jj with
  | none => true
  | some (s, _) => !present s l

/-- ϕ_θ: the number of padding positions of the batch θ -/
def padCount (θ : ℕ) : ℕ :=
  let c := callOf D θ
  ∑ u ∈ range (layersIn D c),
    (2 ^ lJ D c - usedIn D c ((θ - firstTree D c) * layersIn D c + u)) * D.T

/-- pre_c: the prefix of a call, a number of σ − (a_c − D) bits -/
def pre (c : Fin 8) : ℕ := firstTree D c / trees D c

/-- n_2: the number of columns of a matrix, filler included; for af of all parts together -/
def nCol : Mx → ℕ
  | .af => D.parts * afCols D
  | .b => NT D * 2 ^ D.lp
  | μ => (nFeatMx D μ + 2 ^ lFeat D μ - 1) / 2 ^ lFeat D μ

/-- m_Z: the rows of all matrices together, each part of af counted -/
def mZ : ℕ :=
  D.parts * 2 ^ lRow D .af + ([Mx.ad, .ar, .b, .qa, .xin, .xout].map fun μ => 2 ^ lRow D μ).sum

/-! ## Numerical values at the reference sizes (`Dim.ref`) -/

omit scl in
/-- The first features. -/
theorem ref_OFF :
    (arrs .af).map (OFF Dim.ref) =
      [0, 65536, 131072, 262144, 393216, 458752, 524288, 703488, 723968, 744448, 785408, 826368,
        867328, 908288, 957440, 1006592, 1014784, 1018880] ∧
    (arrs .ad).map (OFF Dim.ref) = [0, 40960, 81920] ∧
    (arrs .ar).map (OFF Dim.ref) = [0, 512, 768, 1024, 1030, 1822, 2334] ∧
    (arrs .qa).map (OFF Dim.ref) = [0, 40960, 49152, 57344] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

omit scl in
/-- Features, without filler. -/
theorem ref_features :
    nFeatMx Dim.ref .af = 1149952 ∧
    nFeatMx Dim.ref .ad = 102400 ∧
    nFeatMx Dim.ref .ar = 2590 ∧
    nFeatMx Dim.ref .qa = 98304 ∧
    nFeatMx Dim.ref .xin = 25600 ∧
    nFeatMx Dim.ref .xout = 25600 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

omit scl in
/-- Rows and columns; filler: 128 features in af, 2 in ar; together the nine matrices have m_Z =
499,712 rows. -/
theorem ref_shapes :
    afCols Dim.ref = 5990 ∧
    nCol Dim.ref .af = 17970 ∧
    nCol Dim.ref .ad = 3200 ∧
    nCol Dim.ref .ar = 324 ∧
    nCol Dim.ref .b = 512 ∧
    nCol Dim.ref .qa = 1536 ∧
    nCol Dim.ref .xin = 400 ∧
    nCol Dim.ref .xout = 400 ∧
    [Mx.af, .ad, .ar, .b, .qa, .xin, .xout].map (lRow Dim.ref) = [16, 15, 13, 16, 16, 16, 16] ∧
    nCol Dim.ref .af * 64 - nFeatMx Dim.ref .af = 128 ∧
    nCol Dim.ref .ar * 8 - nFeatMx Dim.ref .ar = 2 ∧
    mZ Dim.ref = 499712 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

omit scl in
/-- Columns used, a_c, D, N_T, σ, the first batch and the prefix of each call. -/
theorem ref_calls :
    (List.finRange 8).map (used Dim.ref) =
      [32768, 31744, 17792, 60998, 17536, 16385, 16384, 16384] ∧
    (List.finRange 8).map (aC Dim.ref) = [27, 27, 27, 28, 27, 27, 26, 26] ∧
    Dk Dim.ref = 26 ∧ NT Dim.ref = 16 ∧ sg Dim.ref = 4 ∧
    (List.finRange 8).map (firstTree Dim.ref) = [4, 6, 8, 0, 10, 12, 14, 15] ∧
    (List.finRange 8).map (pre Dim.ref) = [2, 3, 4, 0, 5, 6, 14, 15] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

omit scl in
/-- The pieces of the eight calls: family, first index, first column. -/
theorem ref_pieces :
    [(Fam.G, 0), (.U, 0)].map (fun p => pos Dim.ref p.1 p.2) = [0, 16384] ∧
    [(Fam.N1, 0), (.N1H, 0), (.N2, 0), (.N2H, 0), (.O, 0), (.D, 0), (.N1, 4096), (.N1H, 4096),
          (.N2, 4096), (.N2H, 4096), (.O, 4096), (.D, 4096), (.V, 0)].map
        (fun p => pos Dim.ref p.1 p.2) =
      [0, 4096, 8192, 12288, 16384, 20480, 24576, 25600, 26624, 27648, 28672, 29696, 30720] ∧
    [(Fam.QK, 0), (.QKH, 0), (.XR, 0), (.QK, 4096), (.QKH, 4096), (.XR, 4096),
          (.LR, 0), (.LT, 0), (.DD, 0)].map
        (fun p => pos Dim.ref p.1 p.2) =
      [0, 4096, 8192, 12288, 14336, 16384, 17408, 17536, 17664] ∧
    [(Fam.GH, 0), (.UH, 0), (.G0, 0), (.OH, 0), (.DH, 0), (.OH, 4096), (.DH, 4096), (.VH, 0),
          (.ROW, 0), (.LH, 0), (.SEL, 0), (.L3, 0), (.ROW, 128), (.ROW, 192), (.ROW, 196)].map
        (fun p => pos Dim.ref p.1 p.2) =
      [0, 16384, 32768, 49152, 53248, 57344, 58368, 59392, 60416, 60544, 60672,
        60800, 60928, 60992, 60996] ∧
    [(Fam.CN1, 0), (.CN2, 0), (.CQK, 0), (.CQK, 4096), (.CN1, 4096), (.CN2, 4096),
          (.CV, 0), (.CLR, 0)].map
        (fun p => pos Dim.ref p.1 p.2) =
      [0, 4096, 8192, 12288, 14336, 15360, 16384, 17408] ∧
    [(Fam.CG, 0), (.MR, 0), (.F, 0), (.UT, 0)].map (fun p => pos Dim.ref p.1 p.2) =
      [0, 16384, 0, 0] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

omit scl in
/-- The call of each batch, and ϕ_θ. -/
theorem ref_trees :
    (List.range 16).map (callOf Dim.ref) = [3, 3, 3, 3, 0, 0, 1, 1, 2, 2, 4, 4, 5, 5, 6, 7] ∧
    (List.range 16).map (padCount Dim.ref) =
      [5040128, 4646912, 5040128, 4646912, 0, 0, 2097152, 2097152, 36306944, 36306944, 31326208,
        31326208, 33553408, 33553408, 0, 0] := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ## The statements -/

/-- The conditions on the sizes that the statements of this file need. The further conditions for
the panel QK are `Dim.ChOK` (Inst/Model/FF/Objects.lean). -/
structure Dim.OK : Prop where
  /-- the positions are those of the model -/
  T : D.P.T = D.T
  /-- there is a layer with experts -/
  lL : 1 ≤ D.lL
  /-- a layer with experts has as many hidden units as a dense one -/
  f : D.f = 2 * D.fe
  parts : 0 < D.parts
  /-- in the matrices that are read by block reads, a block is inside one (array, k, instance). A
  matrix counts as one of these if a column of it holds 2^fBig features; so this field cannot hold
  if fAr = fBig > 0 (the array sc of ar has width 1). -/
  blk : ∀ X : Arr, lFeat D X.mx = D.fBig → 2 ^ D.fBig ∣ X.width D
  /-- a batch holds whole layers -/
  whole : ∀ c, lJ D c + D.lT ≤ Dk D
  /-- a batch holds at least a block -/
  big : D.fBig + D.lT ≤ Dk D
  /-- all batch numbers are in use -/
  full : NT D = 2 ^ sg D

omit scl in
theorem ref_ok : Dim.ref.OK where
  T := by decide +kernel
  lL := by decide +kernel
  f := by decide +kernel
  parts := by decide +kernel
  blk := fun X h => by cases X <;> first | decide +kernel | exact absurd h (by decide +kernel)
  whole := by decide +kernel
  big := by decide +kernel
  full := by decide +kernel

/-- Queries and keys have one shift, unless both shifts are 16 or more (the implementation's check
"kq = kk unless both are >= 16"): their panel has one weight 2^max(0, 16 − k). -/
def Dim.QKOne : Prop := ∀ l, 16 - (D.Pl l).kq = 16 - (D.Pl l).kk

theorem ref_qkOne [Lawful] : Dim.ref.QKOne := fun l => by
  show 16 - (Scl.κ l).kq = 16 - (Scl.κ l).kk
  rcases (Lawful.all l).qk with h | h
  · rw [h]
  · omega

namespace Spec

/-- The index map of a call is injective. -/
def posInj : Prop :=
  ∀ (D : Dim) (s s' : Fam) (x x' : ℕ),
    call s = call s' → x < len D s → x' < len D s' → pos D s x = pos D s' x' → s = s' ∧ x = x'

/-- Its image is an initial range of the columns. -/
def posRange : Prop :=
  ∀ (D : Dim) (c : Fin 8) (jj : ℕ), jj < used D c ↔ ∃ s ∈ fams c, ∃ x < len D s, pos D s x = jj

/-- If 2^b divides n_s, an aligned run of 2^b indices takes 2^b consecutive columns, which start at
a multiple of 2^b. -/
def posAligned : Prop :=
  ∀ (D : Dim) (s : Fam) (b x' x'' : ℕ), 2 ^ b ∣ len D s → 2 ^ b * x' < len D s → x'' < 2 ^ b →
    pos D s (2 ^ b * x' + x'') = pos D s (2 ^ b * x') + x'' ∧ 2 ^ b ∣ pos D s (2 ^ b * x')

/-- `famAt` is the inverse of `pos`. -/
def famAtPos : Prop :=
  ∀ (D : Dim) (c : Fin 8) (jj : ℕ) (s : Fam) (x : ℕ),
    famAt D c jj = some (s, x) ↔ (call s = c ∧ x < len D s ∧ pos D s x = jj)

/-- Under `Dim.OK`, ϕ_θ counts the padding positions of a batch θ < N_T: the indices (ℓ | ȷ | i) of
its call that are in the batch and whose column is padding in the layer. -/
def padCountEq : Prop :=
  ∀ D : Dim, D.OK →
    ∀ θ < NT D, padCount D θ =
      ((range (2 ^ Dk D)).filter fun X =>
        isPad D (callOf D θ)
          (((θ - firstTree D (callOf D θ)) * 2 ^ Dk D + X) / D.T / 2 ^ lJ D (callOf D θ))
          (((θ - firstTree D (callOf D θ)) * 2 ^ Dk D + X) / D.T % 2 ^ lJ D (callOf D θ))).card

/-- The batches of the calls are the numbers below N_T, each call a block that starts at a multiple
of its number of batches. -/
def treesTile : Prop :=
  ∀ D : Dim,
    (∀ θ < NT D,
      firstTree D (callOf D θ) ≤ θ ∧ θ < firstTree D (callOf D θ) + trees D (callOf D θ)) ∧
    ∀ c, trees D c ∣ firstTree D c ∧ firstTree D c + trees D c ≤ NT D

/-- Under `Dim.OK`, every valid cell is inside its matrix. -/
def addrRange : Prop :=
  ∀ D : Dim, D.OK →
    ∀ c : Cell,
      c.Valid D → (addr D c).2.1 < 2 ^ lRow D (addr D c).1 ∧ (addr D c).2.2 < nCol D (addr D c).1

/-- Under `Dim.OK`, distinct valid cells have distinct addresses. -/
def addrInj : Prop :=
  ∀ D : Dim, D.OK → ∀ c c' : Cell, c.Valid D → c'.Valid D → addr D c = addr D c' → c = c'

/-- If lp ≤ r, the bits B[ι, θ, π] and the entries of the matrix b correspond one to one. -/
def addrBBij : Prop :=
  ∀ D : Dim, D.lp ≤ D.r →
    (∀ ι < 2 ^ D.r,
      ∀ θ < NT D, ∀ π < 2 ^ D.lp, (addrB D ι θ π).1 < 2 ^ D.r ∧ (addrB D ι θ π).2 < nCol D .b) ∧
    ∀ row < 2 ^ D.r, ∀ col < nCol D .b, ∃! q : ℕ × ℕ × ℕ,
      q.1 < 2 ^ D.r ∧ q.2.1 < NT D ∧ q.2.2 < 2 ^ D.lp ∧ addrB D q.1 q.2.1 q.2.2 = (row, col)

/-- Under `Dim.OK`, in a matrix that is read by block reads, a block holds 2^fBig consecutive
channels of one (array, k, instance): the feature of (k, inst, 2^fBig ȷ̄ + j″) is feature j″ of the
block feat(k, inst, 2^fBig ȷ̄) / 2^fBig. -/
def blocks : Prop :=
  ∀ D : Dim, D.OK →
    ∀ X : Arr, lFeat D X.mx = D.fBig →
      ∀ k inst jb j2 : ℕ, j2 < 2 ^ D.fBig →
        2 ^ D.fBig ∣ feat D X k inst (2 ^ D.fBig * jb) ∧
        feat D X k inst (2 ^ D.fBig * jb + j2) = feat D X k inst (2 ^ D.fBig * jb) + j2

end Spec

end Inst.Model.FFSeg
