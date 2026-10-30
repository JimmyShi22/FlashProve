-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Layout.lean: the layout of the weights in the matrix W (the matrix of
Blocks/Layout.lean), and the numbers and pairs of rows from which the lookup plan (`Plan.ofPairs`,
Blocks/RngPlan.lean) is built. To audit a relation whose index is `Cm.Idx` (Cm/RelBase.lean), read
this file too. Definitions only.

Defines the layout, the units (`UnitS`) with the matrix of the program that each holds, WF on the
matrix W, and the plan's numbers.
A matrix W is here its lift, a function from rows and columns to integers.
The tensors' sizes and the number of layers named in the comments are those at `ppref`
(Inst/Model/Program.lean).
Notation:
  (Lay): the label of the definition `Lay`.
  tensor claim: `TClaim` (Inst/Model/Common/TensorClaim.lean).
  `D`, `B` (fields of `PlanNums`): natural numbers; in `Plan` (Blocks/RngPlan.lean): the key
    hypercube has D coordinates, the last B of which are the class. `mu`: a natural number, the µ_m
    of the comment on `PlanNums`.
  call: a lookup plan lists the calls of a range reduction (the head of Blocks/RngPlan.lean); `n1`
    counts those of the first kind from the h rows, `n2` those of the second from the m_2 pairs.
  P_U: in `pairAux`, the sum of h_U' over the two-byte units before U.
-/
import Inst.Model.Program
import Mathlib.Data.Nat.Log

set_option autoImplicit false

namespace Inst.Model.Layout

/-! ## The layout -/

/-- for each coordinate one of three kinds: low, high, whole -/
inductive Kind
  | low
  | high
  | whole
  deriving DecidableEq

/-- a coordinate: its size R_g and its kind -/
structure Coord where
  R : ℕ
  kind : Kind

/-- A unit U is W[i_1, ..., i_n] with i_g < R_g, stored in n_U ∈ {2, 4} bytes (`nU`: by type any
natural number; 2 or 4 in `units`) -/
structure UnitS where
  coords : List Coord
  nU : ℕ

/-- Write R_g = o_g 2^{s_g} with o_g odd: s_g. (The first argument bounds the number of steps.) -/
def sAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, R => if R % 2 = 0 ∧ R ≠ 0 then sAux n (R / 2) + 1 else 0
def sOf (R : ℕ) : ℕ := sAux R R

/-- A coordinate of kind low or high takes t_g = min(s_g, left) bits. A coordinate of kind whole
takes t_g = ⌈log2 R_g⌉ bits if that many are left, and t_g = 0 otherwise. -/
def tOf (c : Coord) (left : ℕ) : ℕ :=
  match c.kind with
  | .low => min (sOf c.R) left
  | .high => min (sOf c.R) left
  | .whole => if Nat.clog 2 c.R ≤ left then Nat.clog 2 c.R else 0

/-- Go through the coordinates g = 1, ..., n with a counter of bits that are left, at first k: the
list t_1, ..., t_n -/
def bits : List Coord → ℕ → List ℕ
  | [], _ => []
  | c :: cs, left => tOf c left :: bits cs (left - tOf c left)

/-- Split: i_g ↦ (i^c_g, i^r_g). Low: i = i^r 2^t + i^c. High: with s' = s − t write i = a 2^s + b
2^s' + e; then i^c = b, i^r = a 2^s' + e.
Whole: (i, 0) if t > 0, and (0, i) otherwise. -/
def split (c : Coord) (t i : ℕ) : ℕ × ℕ :=
  match c.kind with
  | .low => (i % 2 ^ t, i / 2 ^ t)
  | .high =>
    ((i / 2 ^ (sOf c.R - t)) % 2 ^ t, (i / 2 ^ sOf c.R) * 2 ^ (sOf c.R - t) + i % 2 ^ (sOf c.R - t))
  | .whole => if 0 < t then (i, 0) else (0, i)

/-- l_g. Low and high: l_g = R_g / 2^{t_g}. Whole: l_g = 1 if t_g > 0, and l_g = R_g otherwise. -/
def lOf (c : Coord) (t : ℕ) : ℕ :=
  match c.kind with
  | .low => c.R / 2 ^ t
  | .high => c.R / 2 ^ t
  | .whole => if 0 < t then 1 else c.R

/-- col_U(i^c) = Σ_g i^c_g 2^{t_1 + ... + t_{g−1}}; the arguments are the coordinates, their bits
and the index tuple -/
def col : List Coord → List ℕ → List ℕ → ℕ
  | c :: cs, t :: ts, i :: is => (split c t i).1 + 2 ^ t * col cs ts is
  | _, _, _ => 0

/-- row_U(ȷ, i^r): the number with the digits ȷ, i^r_n, ..., i^r_1, most significant first, in the
mixed radix (n_U, l_n, ..., l_1) -/
def row (jj : ℕ) : List Coord → List ℕ → List ℕ → ℕ
  | c :: cs, t :: ts, i :: is => (split c t i).2 + lOf c t * row jj cs ts is
  | _, _, _ => jj

/-- h_U = Π_g l_g;  A unit has n_U Π_g l_g rows -/
def hU (k : ℕ) (U : UnitS) : ℕ :=
  ((U.coords.zip (bits U.coords k)).map fun ct => lOf ct.1 ct.2).prod
def rows (k : ℕ) (U : UnitS) : ℕ := U.nU * hU k U

/-- o_U: the number of rows of all earlier units; n is the number of the unit in the order of the
units -/
def off (k : ℕ) (us : List UnitS) (n : ℕ) : ℕ := ((us.take n).map (rows k)).sum

/-- the index tuple i is in the unit: i_g < R_g for all g -/
def InUnit : List Coord → List ℕ → Prop
  | c :: cs, i :: is => i < c.R ∧ InUnit cs is
  | [], [] => True
  | _, _ => False

/-- Byte ȷ of entry i is in row o_U + row_U(ȷ, i^r) and column col_U(i^c) -/
def place (k : ℕ) (us : List UnitS) (n : ℕ) (U : UnitS) (jj : ℕ) (i : List ℕ) : ℕ × ℕ :=
  (off k us n + row jj U.coords (bits U.coords k) i, col U.coords (bits U.coords k) i)

/-- W_{W'}[i] = Σ_{ȷ < n_U} 256^ȷ W'[o_U + row_U(ȷ, i^r)][col_U(i^c)] -/
def entry (k : ℕ) (us : List UnitS) (W : Mat) (n : ℕ) (U : UnitS) (i : List ℕ) : ℤ :=
  ∑ jj ∈ Finset.range U.nU, 256 ^ jj * W (place k us n U jj i).1 (place k us n U jj i).2

/-! ## The units -/

section Units
variable (P : Params)

/-- queries and keys: hd (64, whole), cd (128, whole), in (5,120, low) -/
def uQK : UnitS := ⟨[⟨64, .whole⟩, ⟨P.ch, .whole⟩, ⟨P.d, .low⟩], 2⟩
/-- values: in (5,120, low), out (1,024, high) -/
def uV : UnitS := ⟨[⟨P.d, .low⟩, ⟨P.nkv * P.ch, .high⟩], 2⟩
/-- output projection: in (5,120, low), out (5,120, high) -/
def uO : UnitS := ⟨[⟨P.nq * P.ch, .low⟩, ⟨P.d, .high⟩], 2⟩
/-- gate; up (dense): in (5,120, low), out (16,384, high); (shared): out (8,192, high). n is the
number of hidden units. -/
def uGU (n : ℕ) : UnitS := ⟨[⟨P.d, .low⟩, ⟨n, .high⟩], 2⟩
/-- down (dense): in (16,384, low), out (5,120, high); (shared): in (8,192, low) -/
def uD (n : ℕ) : UnitS := ⟨[⟨n, .low⟩, ⟨P.d, .high⟩], 2⟩
/-- gate; up (routed): in (5,120, low), ex (128, low), out (8,192, high) -/
def uGUr : UnitS := ⟨[⟨P.d, .low⟩, ⟨P.nexp, .low⟩, ⟨P.fe, .high⟩], 2⟩
/-- down (routed): in (8,192, low), ex (128, low), out (5,120, high) -/
def uDr : UnitS := ⟨[⟨P.fe, .low⟩, ⟨P.nexp, .low⟩, ⟨P.d, .high⟩], 2⟩
/-- router: in (5,120, low), out (128, high) -/
def uR : UnitS := ⟨[⟨P.d, .low⟩, ⟨P.nexp, .high⟩], 2⟩
/-- embedding: v (202,048, whole), out (5,120, high); n_U = 4 in the embedding -/
def uEmb : UnitS := ⟨[⟨P.V, .whole⟩, ⟨P.d, .high⟩], 4⟩
/-- output matrix: vocabulary (202,048, whole), in (5,120, low) -/
def uH : UnitS := ⟨[⟨P.V, .whole⟩, ⟨P.d, .low⟩], 2⟩

/-- for each layer: queries and keys, values, output projection; then gate, up, down in a dense
layer, and shared gate, shared up, routed gate, routed up, shared down, routed down, router in a
layer with experts -/
def layerUnits (L : ℕ) : List UnitS :=
  [uQK P, uV P, uO P] ++
    (if hasExperts L then [uGU P P.fe, uGU P P.fe, uGUr P, uGUr P, uD P P.fe, uDr P, uR P]
      else [uGU P P.f, uGU P P.f, uD P P.f])

/-- Order of the units: for each layer L = 0, ..., 47: its units (`layerUnits`); the embedding and
the output matrix come last. -/
def units : List UnitS := (List.range P.layers).flatMap (layerUnits P) ++ [uEmb P, uH P]

/-- the number, in this order, of the first unit of layer L -/
def first (L : ℕ) : ℕ := ((List.range L).map fun L' => (layerUnits P L').length).sum

end Units

/-! ## From the matrix W to the weights of the program -/

section Read
variable (P : Params) (k : ℕ) (W : Mat)

/-- the entry i of the unit U, which has the number n -/
def rd (n : ℕ) (U : UnitS) (i : List ℕ) : ℤ := entry k (units P) W n U i
/-- a matrix of the program with r rows and c columns, and 0 outside -/
def mat (r c : ℕ) (f : ℕ → ℕ → ℤ) : Mat := fun j x => if j < r ∧ x < c then f j x else 0

/-- The weights of layer L. W_q[j][128 h + n] is the entry (h, n, j), h < 40; W_k[j][128 g + n] the
entry (40 + g, n, j), g < 8; Where nothing else is said, the entry with the coordinates (in,
out) = (j, x) is the matrix entry [j][x]; routed: the entry (j, e, x); router: the entry (j,
e). -/
def layerOf (L : ℕ) : LayerW :=
  let n := first P L
  let ex := hasExperts L
  { Wq := mat P.d (P.nq * P.ch) fun j c => rd P k W n (uQK P) [c / P.ch, c % P.ch, j]
    Wk := mat P.d (P.nkv * P.ch) fun j c => rd P k W n (uQK P) [P.nq + c / P.ch, c % P.ch, j]
    Wv := mat P.d (P.nkv * P.ch) fun j x => rd P k W (n + 1) (uV P) [j, x]
    Wo := mat (P.nq * P.ch) P.d fun j x => rd P k W (n + 2) (uO P) [j, x]
    Wg := if ex then
      mat P.d P.fe fun j x =>
        rd P k W (n + 3) (uGU P P.fe) [j, x]
        else mat P.d P.f fun j x => rd P k W (n + 3) (uGU P P.f) [j, x]
    Wu := if ex then
      mat P.d P.fe fun j x =>
        rd P k W (n + 4) (uGU P P.fe) [j, x]
        else mat P.d P.f fun j x => rd P k W (n + 4) (uGU P P.f) [j, x]
    Wd := if ex then
      mat P.fe P.d fun j x =>
        rd P k W (n + 7) (uD P P.fe) [j, x]
        else mat P.f P.d fun j x => rd P k W (n + 5) (uD P P.f) [j, x]
    Wr := if ex then mat P.d P.nexp fun j e => rd P k W (n + 9) (uR P) [j, e] else fun _ _ => 0
    Eg := fun e =>
      if ex ∧ e < P.nexp then
        mat P.d P.fe fun j x => rd P k W (n + 5) (uGUr P) [j, e, x] else fun _ _ => 0
    Eu := fun e =>
      if ex ∧ e < P.nexp then
        mat P.d P.fe fun j x => rd P k W (n + 6) (uGUr P) [j, e, x] else fun _ _ => 0
    Ed := fun e =>
      if ex ∧ e < P.nexp then
        mat P.fe P.d fun j x => rd P k W (n + 8) (uDr P) [j, e, x] else fun _ _ => 0 }

/-- the layer beyond the last one: all zero -/
def noLayer : LayerW :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- The weights that the layout reads from W. Emb[tok][j]: the entry (tok, j); H[j][ι]: the entry
(ι, j). -/
def weightsOf : Weights where
  layer := fun L => if L < P.layers then layerOf P k W L else noLayer
  Emb := mat P.V P.d fun t j => rd P k W (first P P.layers) (uEmb P) [t, j]
  H := mat P.d P.V fun j v => rd P k W (first P P.layers + 1) (uH P) [v, j]

/-! ## WF, on the matrix W -/

/-- WF(i) (its i: the index, here the matrix W): the lifts of all entries lie in [−2^7, 2^7), and
b0 + 256 b1 ∈ [−2^12, 2^12) for the lifted entries b0, b1 in every column of every pair of rows that
holds the bytes of two-byte weights. The pairs of rows in the definition of WF are the pairs (o_U +
row_U(0, i^r), o_U + row_U(1, i^r)) of the units with n_U = 2.  h is the number of rows of W. -/
def WFW (h : ℕ) : Prop :=
  (∀ y < h, ∀ c < 2 ^ k, -2 ^ 7 ≤ W y c ∧ W y c < 2 ^ 7) ∧
  ∀ n < (units P).length, ∀ U, (units P)[n]? = some U → U.nU = 2 →
    ∀ i, InUnit U.coords i →
      ∀ c < 2 ^ k,
        -2 ^ 12 ≤ W (place k (units P) n U 0 i).1 c + 256 * W (place k (units P) n U 1 i).1 c ∧
        W (place k (units P) n U 0 i).1 c + 256 * W (place k (units P) n U 1 i).1 c < 2 ^ 12

end Read

/-! ## (Lay), as a statement about a list of units -/

/-- the layout's map from a weight and a byte number to a place (a row and a column) is injective,
and every place lies inside W; it says nothing on tensor claims -/
def Lay (k h : ℕ) (us : List UnitS) : Prop :=
  (∀ n U jj i, us[n]? = some U → jj < U.nU → InUnit U.coords i →
    (place k us n U jj i).1 < h ∧ (place k us n U jj i).2 < 2 ^ k) ∧
  ∀ n U jj i n' U' jj' i', us[n]? = some U → jj < U.nU → InUnit U.coords i →
    us[n']? = some U' → jj' < U'.nU → InUnit U'.coords i' →
    place k us n U jj i = place k us n' U' jj' i' → n = n' ∧ jj = jj' ∧ i = i'

/-! ## The plan of a layout -/

/-- the numbers of a look-up plan: fix D ≥ k, B ≤ k and m = 2^{µ_m} (the bounds are not fields) -/
structure PlanNums where
  D : ℕ
  B : ℕ
  mu : ℕ

section Plan
variable (k h : ℕ) (us : List UnitS) (N : PlanNums)

/-- R = 2^{D−k}: the rows of one call -/
def callRows : ℕ := 2 ^ (N.D - k)
/-- the units with n_U = 2, each with its number in the order of all units -/
def twoByte : List (ℕ × UnitS) := (us.zipIdx.map fun p => (p.2, p.1)).filter fun p => p.2.nU = 2
/-- m_2: the number of pairs of rows -/
def m2 : ℕ := ((twoByte us).map fun p => hU k p.2).sum
/-- The pair with number q = P_U + r, r < h_U, is (y_0(q), y_1(q)) = (o_U + r, o_U + h_U + r) -/
def pairAux : List (ℕ × UnitS) → ℕ → ℕ × ℕ
  | [], _ => (0, 0)
  | p :: ps, q =>
    if q < hU k p.2 then (off k us p.1 + q, off k us p.1 + hU k p.2 + q)
    else pairAux ps (q - hU k p.2)
def pair (q : ℕ) : ℕ × ℕ := pairAux k us (twoByte us) q
/-- n_1 = ⌈h/R⌉ calls of the first kind, ⌈m_2/R⌉ of the second -/
def n1 : ℕ := (h + callRows k N - 1) / callRows k N
def n2 : ℕ := (m2 k us + callRows k N - 1) / callRows k N

end Plan

/-! ## The reference parameters -/

/-- rows and columns of W: h; 2^k = 3,076,096; 2^18 (h is `hRef`, k is `kRef`) -/
def kRef : ℕ := 18
def hRef : ℕ := 3076096
/-- look-up plan of the range reduction: D; B; m = 32; 4; 32 (32 = 2^5; the fields `D`, `B`, `mu` of
`PlanNums`, with m = 2^`mu`) -/
def planRef : PlanNums := ⟨32, 4, 5⟩

end Inst.Model.Layout
