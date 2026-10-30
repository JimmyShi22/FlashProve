-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Weights.lean: the layout of the committed matrix of weights, and claims on it.

It follows the C++ verifier's header verifier/src/vf_weights_layout.h, routine by routine, except
that header's last type and routine (WsForkOut, wsForkEnd), which are in OnBytes/Model/Merge.lean.
It also follows three pieces of verifier/src/cp_verify.cpp that concern only the layout
(tokenFactorTaken, tokenFactorUnits, wsLayOf). A type or routine has the name of its C++
counterpart, and its docstring names it after "C++:". A definition without such a note is a helper
or a part of a C++ routine. The C++ spells the constants wsRowsLog as WS_ROWS_MOST_LOG2 and
wsSecondDigit as WS_SECOND_DIGIT.

The matrix. The model's weights are committed as one matrix W with 2^lk columns. A weight is
written in digits to the base 256, and each digit has a cell of its own. The rows of W come in
units: one unit for each kind of weight matrix of each layer, then one for the embedding and one for
the head. A cell of a unit is named by the number of a digit and by one index from each index group
of the unit. Each group gives some bits of its index to the number of the column and leaves
the rest to the number of the row. The layout follows from the model's shape and from lk, which the
parameter file gives.

The claims. A sub-proof of some layers or of the head ends with claims of this form: the weights of
unit u, each times a product of factors, one factor for each index group, sum to a hidden value.
The merge (OnBytes/Model/Merge.lean) batches the claims and binds the column bits at one point.
What is left of a claim is a scalar and its factors on the rows. Written out, these are
coefficients on the rows of W.

Main definitions: WsShape, wsSetMoe, WsGrp, WsUnit, WsLay, WsLay.build, wsLayOf, WsFac, WsClaim,
wsClaimShape, wsEpsT, WsRecClaim, wsRowPart, wsGammaAdd.

Refusals. No function here reads a message. Whether a function refuses depends on sizes, on numbers
of units and on public numbers alone, never on a field element. The field elements in a claim's
factors can depend on what the prover has sent: the head's claim has a factor on the reply's token.
A function that can refuse returns the refusal's name in Except.

What this file does not do: it tests no equation of a proof. How W is committed, opened and tested
is written elsewhere (OnBytes/Iop/Lin.lean). No theorem is stated here.
-/
import OnBytes.Model.Frame

namespace OnBytes.Model

/-! ## Small tools -/

/-- All products a[i] b[q], at the index i |b| + q. -/
def wsOuter (a b : Array E) : Array E :=
  a.foldl (fun out x => b.foldl (fun o y => o.push (mulE x y)) out)
    (Array.emptyWithCapacity (a.size * b.size))

/-- The sum of a[i] b[i] over the first n indices. An index beyond an array reads 0. -/
def wsDot (n : Nat) (a b : Array E) : E :=
  (List.range n).foldl (fun s i => maddE s (a.getD i zeroE) (b.getD i zeroE)) zeroE

/-! ## The model's shape -/

/-- The numbers of the model on which the layout depends. MOE is 0 or 1. Layer l is a mixture of
experts if MOE is 1 and l is odd. wsSetMoe fills both MOE and moe, and WsLay.build refuses if they
disagree. C++: WsShape. -/
structure WsShape where
  /-- the number of rows of W is rounded up to a multiple of D -/
  D : Nat := 0
  /-- the number of layers -/
  L : Nat := 0
  /-- the width of the residual stream -/
  d : Nat := 0
  /-- the width of an attention head -/
  dh : Nat := 0
  /-- the width of all value heads together -/
  dkv : Nat := 0
  /-- the width of all query heads together -/
  dq : Nat := 0
  /-- the inner width of a dense layer's feed-forward part -/
  f : Nat := 0
  /-- the inner width of an expert -/
  fe : Nat := 0
  /-- the number of experts -/
  NE : Nat := 0
  /-- the size of the vocabulary -/
  V : Nat := 0
  /-- 1 if W holds the embedding and the head, else 0 -/
  eh : Nat := 0
  /-- 1 if the model has layers that are mixtures of experts, else 0 -/
  MOE : Nat := 0
  /-- for each layer: true if it is a mixture of experts -/
  moe : Array Bool := #[]
  deriving Repr, Inhabited

/-- Sets MOE, and moe for each of the L layers. With more than 4096 layers moe stays empty, and
WsLay.build refuses. C++: wsSetMoe. -/
def wsSetMoe (s : WsShape) (MOE : Bool) : WsShape :=
  { s with
    MOE := if MOE then 1 else 0
    moe := Array.ofFn (n := if s.L ≤ 4096 then s.L else 0) fun l => MOE && l.val % 2 == 1 }

/-! ## The layout -/

/-- An index group of a unit's cells. There are two classes.
Class 'E': R = o 2^z with o odd, and an index is hi 2^z + lo. The group gives t bits of lo to the
columns: the lowest ones, or the highest ones if high is set.
Class 'A': the whole index goes to the columns (t is the number of its bits) or to the rows
(t = 0). For class 'E' a claim's factor on lo is an equality polynomial at a point (WsFac.pt). For
class 'A' it is any vector, written out (WsFac.AV). C++: WsGrp. -/
structure WsGrp where
  /-- a sub-proof picks a claim's factor for a group by this name -/
  name : String := ""
  /-- the number of indices -/
  R : Nat := 0
  /-- class 'E': the odd part of R -/
  o : Nat := 0
  /-- the number of values of the part of the index that is left to the rows -/
  left : Nat := 0
  /-- the class, 'E' or 'A' -/
  cls : Char := 'E'
  /-- class 'E': true if the highest bits of lo go to the columns -/
  high : Bool := false
  /-- class 'E': the number of bits of lo -/
  z : Nat := 0
  /-- the number of bits given to the columns -/
  t : Nat := 0
  /-- the group's first column bit -/
  cb0 : Nat := 0
  deriving Repr, Inhabited

namespace WsGrp

/-- True if bit b of lo is a column bit. C++: WsGrp::takenBit. -/
def takenBit (g : WsGrp) (b : Nat) : Bool :=
  if g.high then decide (g.z - g.t ≤ b) else decide (b < g.t)

/-- The bit of lo that is the i-th taken one, the lowest first. C++: WsGrp::takenAt. -/
def takenAt (g : WsGrp) (i : Nat) : Nat := if g.high then g.z - g.t + i else i

/-- True for a group of class 'A' whose index went to the columns. A group of class 'A' with R = 1
has t = 0 and counts as not taken: its one element is a factor on the rows. C++: WsGrp::aTaken. -/
def aTaken (g : WsGrp) : Bool := g.cls == 'A' && decide (0 < g.t)

end WsGrp

/-- A unit: the rows of W that hold one weight matrix. C++: WsUnit. -/
structure WsUnit where
  /-- the kind of weight matrix, 0 to 13 -/
  X : Nat := 0
  /-- the layer; the number of layers for the embedding and the head -/
  l : Nat := 0
  /-- the number of digits of a weight -/
  nlw : Nat := 2
  /-- the number of column bits that the groups take -/
  ncb : Nat := 0
  /-- the index groups -/
  g : List WsGrp := []
  /-- the number of the unit's rows -/
  rows : Nat := 0
  /-- the unit's first row in W -/
  off : Nat := 0
  deriving Repr, Inhabited

/-- W has at most 2^22 rows: a constant of the format. C++: WS_ROWS_MOST_LOG2. -/
def wsRowsLog : Nat := 22

/-- The layout of W, which has 2^lk columns. C++: WsLay. -/
structure WsLay where
  /-- the number of column bits -/
  lk : Nat := 0
  /-- the number of all rows -/
  m0 : Nat := 0
  /-- the units -/
  U : Array WsUnit := #[]
  deriving Repr, Inhabited

namespace WsLay

/-- Divides o by 2 as long as it is even and counts the steps on top of z. The first argument
bounds the number of steps. -/
def oddPart : Nat → Nat → Nat → Nat × Nat
  | 0, o, z => (o, z)
  | k + 1, o, z => if o % 2 == 0 then oddPart k (o / 2) (z + 1) else (o, z)

/-- A group of class 'E' with R indices, before the layout places it. The fields o and z are right
for R from 1 to 2^64. C++: WsLay::E_. -/
def E_ (n : String) (R : Nat) (high : Bool) : WsGrp :=
  let p := oddPart 64 R 0
  { name := n, R := R, cls := 'E', high := high, o := p.1, z := p.2 }

/-- A group of class 'A' with R indices, before the layout places it. C++: WsLay::A_. -/
def A_ (n : String) (R : Nat) : WsGrp := { name := n, R := R, cls := 'A' }

/-- Gives each group its column bits. left: the number of column bits not yet given; cb: the next
column bit; rows: the product of what the digits and the groups so far leave to the rows. Returns
the placed groups, the number of column bits taken and the unit's number of rows. Class 'E' takes as
many of its z bits as are free. Class 'A' takes all its bits if that many are free, and none
otherwise. A product of more than 2^22 rows is refused as "w-shape-mW". -/
def place : List WsGrp → Nat → Nat → Nat → Except String (List WsGrp × Nat × Nat)
  | [], _, cb, rows => pure ([], cb, rows)
  | x :: g, left, cb, rows =>
    let t :=
      if x.cls == 'E' then min x.z left
      else if clog2 x.R ≤ left then clog2 x.R else 0
    let y := { x with t := t, cb0 := cb }
    let l := if x.cls == 'E' then x.R / 2 ^ t else if y.aTaken then 1 else x.R
    if 2 ^ wsRowsLog < rows * l then throw "w-shape-mW"
    else do
      let r ← place g (left - t) (cb + t) (rows * l)
      pure ({ y with left := l } :: r.1, r.2)

/-- Appends a unit: gives each group its column bits, counts the unit's rows and sets its
offset. More than 2^22 rows, in the unit or in all, are refused as "w-shape-mW".
C++: WsLay::add. -/
def add (lay : WsLay) (X l nlw : Nat) (g : List WsGrp) : Except String WsLay := do
  let r ← place g lay.lk 0 nlw
  if 2 ^ wsRowsLog < lay.m0 + r.2.2 then throw "w-shape-mW"
  pure { lay with
    m0 := lay.m0 + r.2.2
    U := lay.U.push { X := X, l := l, nlw := nlw, ncb := r.2.1, g := r.1, rows := r.2.2,
                      off := lay.m0 } }

/-- Appends the units of layer l, in the order of their kinds. A dense layer has the kinds 0, 1, 2,
3, 4, 9, which the C++ calls qk v o g u dn. A mixture of experts has the kinds 0, 1, 2, 5, 6, 7, 8,
9, 10, 11, which it calls qk v o gs us gr ur dn dnr r. The group "hd" of kind 0 has room for 64
heads, the query heads and then the key heads. The layout of a layer sub-proof refuses more
("shape-heads"). -/
def addLayer (s : WsShape) (lay : WsLay) (l : Nat) : Except String WsLay := do
  let lay ← lay.add 0 l 2 [A_ "hd" 64, A_ "cd" s.dh, E_ "kk" s.d false]
  let lay ← lay.add 1 l 2 [E_ "kk" s.d false, E_ "x" s.dkv true]
  let lay ← lay.add 2 l 2 [E_ "kk" s.dq false, E_ "x" s.d true]
  if s.moe.getD l false then do
    let lay ← lay.add 5 l 2 [E_ "kk" s.d false, E_ "x" s.fe true]
    let lay ← lay.add 6 l 2 [E_ "kk" s.d false, E_ "x" s.fe true]
    let lay ← lay.add 7 l 2 [E_ "kk" s.d false, E_ "e" s.NE false, E_ "x" s.fe true]
    let lay ← lay.add 8 l 2 [E_ "kk" s.d false, E_ "e" s.NE false, E_ "x" s.fe true]
    let lay ← lay.add 9 l 2 [E_ "kk" s.fe false, E_ "x" s.d true]
    let lay ← lay.add 10 l 2 [E_ "kk" s.fe false, E_ "e" s.NE false, E_ "x" s.d true]
    lay.add 11 l 2 [E_ "kk" s.d false, E_ "x" s.NE true]
  else do
    let lay ← lay.add 3 l 2 [E_ "kk" s.d false, E_ "x" s.f true]
    let lay ← lay.add 4 l 2 [E_ "kk" s.d false, E_ "x" s.f true]
    lay.add 9 l 2 [E_ "kk" s.f false, E_ "x" s.d true]

/-- True if v is from 1 to 2^24. -/
def inWords (v : Nat) : Bool := decide (1 ≤ v) && decide (v ≤ 2 ^ 24)

/-- The layout for a shape and a number lkW of column bits. Every number that reaches a power, a
loop or a product is tested here first, so the function relies on no test of its caller.
C++: WsLay::build. -/
def build (s : WsShape) (lkW : Nat) : Except String WsLay := do
  if lkW < 1 || 20 < lkW then throw "w-shape-lk"
  if s.D != 2048 && s.D != 32 then throw "shape-D"
  if s.L == 0 || 4096 < s.L || s.moe.size != s.L || 1 < s.MOE then throw "shape-words"
  if !((List.range s.L).all fun l => s.moe.getD l false == (s.MOE != 0 && l % 2 == 1)) then
    throw "internal-shape-moe"
  if !([s.d, s.dh, s.dkv, s.dq, s.f].all inWords) then throw "shape-words"
  -- No layer but a mixture of experts reads fe and NE.
  if s.moe.any id && !([s.fe, s.NE].all inWords) then throw "shape-words"
  if 1 < s.eh || (s.eh != 0 && !inWords s.V) then throw "shape-words"
  let lay ← (List.range s.L).foldlM (addLayer s) { lk := lkW }
  let lay ←
    if s.eh != 0 then do
      let lay ← lay.add 12 s.L 4 [A_ "v" s.V, E_ "x" s.d true]
      lay.add 13 s.L 2 [A_ "x" s.V, E_ "kk" s.d false]
    else pure lay
  let m0 := (lay.m0 + s.D - 1) / s.D * s.D
  if 2 ^ wsRowsLog < m0 then throw "w-shape-mW"
  pure { lay with m0 := m0 }

/-- The number of the first unit of kind X of layer l; nothing if there is none. A layout from
build has at most one: build calls addLayer once for each layer, addLayer adds each kind at most
once, and the kinds 12 and 13 are added once, after the layers. The C++ layer sub-proof looks a unit
up in a map (uiOf, verifier/src/vf_layers_check.inc) that would keep the last of several. -/
def unitOf (lay : WsLay) (X l : Nat) : Option Nat :=
  lay.U.findIdx? fun u => u.X == X && u.l == l

end WsLay

/-- True if the whole index of a vocabulary of V tokens can go to the columns: it has from 1 to lkW
bits. The factor on that index depends on the tokens of the request and of the reply. If it did not
go to the columns, it would be passed on whole, element by element (WsRowFac.AV). wsLayOf refuses
where this is false, and tokenFactorUnits tests that the index did go to the columns.
C++: tokenFactorTaken, verifier/src/cp_verify.cpp. -/
def tokenFactorTaken (V lkW : Nat) : Bool := decide (1 ≤ clog2 V) && decide (clog2 V ≤ lkW)

/-- Tests the layout as built: each unit of kind 12 or 13 (embedding, head) has a group of class
'A', and each such group gives its index to the columns.
C++: tokenFactorUnits, verifier/src/cp_verify.cpp. -/
def tokenFactorUnits (lay : WsLay) : Except String Unit :=
  if lay.U.all fun u =>
      !(u.X == 12 || u.X == 13) ||
        (u.g.any (·.cls == 'A') &&
          u.g.all fun g => g.cls != 'A' || (tokenFactorTaken g.R lay.lk && g.aTaken)) then
    pure ()
  else throw "w-list-token-factor"

/-- The layout of W as a request's check makes it. s holds the fields D to V, which are numbers of
the parameter file or, as dkv and dq, follow from them; p3 says whether the model has layers that
are mixtures of experts; lkW is the last number of the parameter file's line "table". W holds the
embedding and the head.
C++: the block that fills wsLay in runStage, verifier/src/cp_verify.cpp. -/
def wsLayOf (s : WsShape) (p3 : Bool) (lkW : Nat) : Except String WsLay := do
  if lkW < clog2 s.V then throw "hid-vocab-cols"
  if !tokenFactorTaken s.V lkW then throw "w-list-token-factor"
  let lay ← WsLay.build (wsSetMoe { s with eh := 1 } p3) lkW
  tokenFactorUnits lay
  pure lay

/-! ## Claims -/

/-- eq on one bit: p x + (1 - p) (1 - x). C++: wsEq1. -/
def wsEq1 (p x : E) : E := addE (mulE p x) (mulE (subE oneE p) (subE oneE x))

/-- A claim's factor for one index group. Class 'E': HV has o elements, one for each value of hi,
and pt has z elements; pt[i] is the coordinate of bit z - 1 - i of lo. Class 'A': AV has R
elements. C++: WsFac. -/
structure WsFac where
  /-- class 'E': one element for each value of hi -/
  HV : Array E := #[]
  /-- class 'E': one coordinate for each bit of lo, the highest bit first -/
  pt : Array E := #[]
  /-- class 'A': one element for each index -/
  AV : Array E := #[]
  deriving Inhabited

/-- A claim on a unit: the number ui of the unit in the layout and one factor for each of the
unit's groups. C++: WsClaim. -/
structure WsClaim where
  /-- the number of the unit in WsLay.U -/
  ui : Nat := 0
  /-- the factors, in the order of the unit's groups -/
  f : List WsFac := []
  deriving Inhabited

/-- A claim's factor on the rows, for one index group. Class 'E': HV, and pl, the coordinates of
the bits of lo that were not taken, the highest bit first. Class 'A', not taken: AV. Class 'A',
taken: nothing. C++: WsRowFac. -/
structure WsRowFac where
  /-- class 'E': one element for each value of hi -/
  HV : Array E := #[]
  /-- class 'E': one coordinate for each bit of lo that was not taken, the highest bit first -/
  pl : Array E := #[]
  /-- class 'A', not taken: one element for each index -/
  AV : Array E := #[]
  deriving Inhabited

/-- What is left of a claim when the columns are bound: the unit, a scalar ka and the factors on
the rows. C++: WsRecClaim. -/
structure WsRecClaim where
  /-- the number of the unit in WsLay.U -/
  ui : Nat := 0
  /-- the scalar -/
  ka : E := zeroE
  /-- the factors on the rows, in the order of the unit's groups -/
  f : List WsRowFac := []
  deriving Inhabited

/-- True if the factor has the sizes that the group asks for. -/
def WsFac.fits (x : WsFac) (g : WsGrp) : Bool :=
  if g.cls == 'E' then x.HV.size == g.o && x.pt.size == g.z && x.AV.isEmpty
  else x.AV.size == g.R && x.HV.isEmpty && x.pt.isEmpty

/-- Tests a claim's sizes against the layout. C++: wsClaimShape. -/
def wsClaimShape (lay : WsLay) (c : WsClaim) : Except String Unit :=
  match lay.U[c.ui]? with
  | none => throw "internal-claim-unit"
  | some u =>
    if c.f.length == u.g.length && ((c.f.zip u.g).all fun y => y.1.fits y.2) then pure ()
    else throw "internal-claim-factors"

/-- The value of one factor on its group's column bits. X b is the coordinate of column bit b. -/
def WsFac.onColumns (x : WsFac) (g : WsGrp) (X : Nat → E) : E :=
  if g.cls == 'E' then
    (List.range g.t).foldl
      (fun p i => mulE p (wsEq1 (x.pt.getD (g.z - 1 - g.takenAt i) zeroE) (X (g.cb0 + i)))) oneE
  else if g.aTaken then
    -- The table's first coordinate belongs to the top bit of the index: column bit cb0 + t - 1.
    wsDot g.R x.AV (eqTab (Array.ofFn (n := g.t) fun s => X (g.cb0 + g.t - 1 - s.val)))
  else oneE

/-- The value of a claim's factors on the columns at the point rm. rm[i] is the coordinate of
column bit lk - 1 - i. The value is the product of the groups' factors on their column bits, times
1 - (the coordinate) for each column bit that no group of the unit takes. The caller has tested the
claim with wsClaimShape and passes lk coordinates. Without that test the function is still
defined: it gives 0 if the layout has no unit ui, and reads 0 beyond the end of an array.
C++: wsEpsT. -/
def wsEpsT (lay : WsLay) (c : WsClaim) (rm : Array E) : E :=
  match lay.U[c.ui]? with
  | none => zeroE
  | some u =>
    let X := fun b => rm.getD (lay.lk - 1 - b) zeroE
    let p := (c.f.zip u.g).foldl (fun p y => mulE p (y.1.onColumns y.2 X)) oneE
    (List.range (lay.lk - u.ncb)).foldl (fun p i => mulE p (subE oneE (X (u.ncb + i)))) p

/-- The part of a factor that is left to the rows. -/
def WsFac.onRows (x : WsFac) (g : WsGrp) : WsRowFac :=
  if g.cls == 'E' then
    { HV := x.HV
      pl := ((List.range g.z).filterMap fun i =>
        if g.takenBit (g.z - 1 - i) then none else some (x.pt.getD i zeroE)).toArray }
  else if g.aTaken then {}
  else { AV := x.AV }

/-- What is left of claim c when the columns are bound, under the scalar ka. The caller has tested
the claim with wsClaimShape. If the layout has no unit ui, the result has no factors, and
wsGammaAdd refuses it. C++: wsRowPart. -/
def wsRowPart (lay : WsLay) (c : WsClaim) (ka : E) : WsRecClaim :=
  match lay.U[c.ui]? with
  | none => { ui := c.ui, ka := ka }
  | some u => { ui := c.ui, ka := ka, f := (c.f.zip u.g).map fun y => y.1.onRows y.2 }

/-- The base of the digits: a number in the committed matrix is the sum of digit l times 256^l.
C++: WS_SECOND_DIGIT. -/
def wsSecondDigit : F := 256

/-- A row factor written out: one element for each value of the part of the index that is left to
the rows. For class 'E' that part is hi 2^(z - t) + (the bits of lo not taken, in their order). -/
def WsRowFac.table (x : WsRowFac) (g : WsGrp) : Array E :=
  if g.cls == 'E' then wsOuter x.HV (eqTab x.pl)
  else if g.aTaken then #[oneE]
  else x.AV

/-- The scalars s, 256 s, 256^2 s, and so on: one for each of n digits. -/
def wsDigits : Nat → E → List E
  | 0, _ => []
  | n + 1, s => s :: wsDigits n (scaleE wsSecondDigit s)

/-- A claim's coefficients on the rows of its unit, times wgt. The number of a row within the unit
is a number of mixed radix. Its places are, the most significant first: the number of the digit of
the model's weight, then the groups in reversed order, each with the part of its index that is left
to the rows. -/
def wsGamma (u : WsUnit) (c : WsRecClaim) (wgt : E) : Array E :=
  (c.f.zip u.g).reverse.foldl (fun v y => wsOuter v (y.1.table y.2))
    (wsDigits u.nlw (mulE wgt c.ka)).toArray

/-- Adds a claim's coefficients, times wgt, to Gam, a vector of coefficients on the rows of W from
row 0 on. Refused as "internal-gamma-rows": a unit that is not in the layout; a number of factors
that differs from the unit's number of groups; a number of coefficients that differs from the unit's
number of rows; a unit whose rows do not all lie within Gam. C++: wsGammaAdd. -/
def wsGammaAdd (Gam : Array E) (lay : WsLay) (c : WsRecClaim) (wgt : E) :
    Except String (Array E) :=
  match lay.U[c.ui]? with
  | none => throw "internal-gamma-rows"
  | some u =>
    let v := wsGamma u c wgt
    if v.size != u.rows || c.f.length != u.g.length || Gam.size < u.off + u.rows then
      throw "internal-gamma-rows"
    else
      pure (v.foldl (fun (s : Array E × Nat) x => (s.1.modify s.2 fun y => addE y x, s.2 + 1))
        (Gam, u.off)).1

/-- The names under which the functions of this file refuse. -/
def Weights.names : List String :=
  ["w-shape-mW", "w-shape-lk", "shape-D", "shape-words", "internal-shape-moe",
   "w-list-token-factor", "hid-vocab-cols", "internal-claim-unit", "internal-claim-factors",
   "internal-gamma-rows"]

end OnBytes.Model
