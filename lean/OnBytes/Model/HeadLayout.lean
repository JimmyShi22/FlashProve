-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/HeadLayout.lean: the layout of the sub-proof of the output head, from public numbers.

The last sub-proof of a request's proof is about the final norm, the output head and the acceptance
policy. This file holds what public numbers fix about it: where its tensors lie in its committed
matrices, the sizes of these matrices, its list of lookup calls, its table of exponentials, and the
tests on all these numbers. The caller takes the numbers from the parameter file. The file also
holds what the request fixes: which positions are covered and which token is checked at each.

The C++ counterparts are all in verifier/src/cp_verify.cpp: the part of runStage that fills the
object HLy, the tests on the vocabulary's size and on the two widths before it, stFromCall, and
the part of runStage that opens the request. A failed test is reported by the name under which
cp_verify refuses. One name, internal-head-shape, is this file's own.

Blocks. Some claims read S2 = 2^ls neighbouring features of a matrix at once, at all T positions: a
block of 2^la rows, where la = ls + lt. An entry of a long table of reads stands for one such block
(OnBytes/Model/Tensors.lean).

The tensors. The matrix hf holds, feature by feature: aw (the normalized activations before the
clamp, 2 limbs of d features), ra (a remainder, 2 limbs of d), d1 (the middle digit of a margin, 2
limbs of JV), d2 (its low digit, JV), ex (a value of the table of exponentials, 3 cells of JV). A
margin belongs to a position t and a vocabulary entry v. JV is the size of the vocabulary rounded up
to a multiple of S2. The matrix hd holds the clamped activations. The matrix hr holds one row of
digits for each position, the ledger (OnBytes/Model/Ledger.lean): the final norm's digits, then the
digits of six hidden numbers of the acceptance policy. Hidden is the name of their part in the
protocol: the prover commits to them and does not send them. Nothing here claims that they stay
hidden. The exponentials' seven factors (`tauFEFactors`) are plain mathematics, from no file.

Main definitions: `Layout.names`, `Shape`, `vocabulary`, `HL`, `policy`, `numbers`, `tauFEOf`,
`segments`, `callsOf`, `lookups`, `pubOf`, `h9`, `layout`, `StOwn`, `stFromCall`, `Covered`,
`Covered.sized`, `coveredOf`.
What is not claimed: no theorem is stated here.
-/
import OnBytes.Model.Calls
import OnBytes.Model.Ledger
import OnBytes.Model.Forest
import OnBytes.Model.Tensors

namespace OnBytes.Model.Head

/-- The names of the refusals that this file raises. Where cp_verify appends the name of a call to
a name, the name here ends before it. A call's name comes from the parameter file, and no name here
contains anything that was read from a file. -/
def Layout.names : List String :=
  ["shape-V", "policy-weight-kind", "policy-weight-width-emb", "policy-norm-F", "policy-toksrc",
   "policy-gap-words", "shape-request-matrix-H", "policy-call-list-H", "shape-call-H",
   "internal-table-FE", "internal-forest-place", "forest-depth-H", "header-absent-call-H",
   "internal-head-shape", "no-wrap-H-U-NF", "no-wrap-H-W-NF", "no-wrap-H-W-HD0",
   "no-wrap-H-three-digits", "no-wrap-H-HE", "no-wrap-H-Z", "no-wrap-H-E2", "no-wrap-H-E3",
   "no-wrap-H-E4", "no-wrap-H-J-E", "no-wrap-H-guard-radix", "statement-required",
   "statement-range", "token-range", "token-length"]

/-- Fails with the given name unless ok is true. -/
def needed (ok : Bool) (name : String) : Except String Unit :=
  if ok then .ok () else .error name

/-- The public numbers on which the head's sub-proof depends. The caller takes them from the
parameter file, except lPd, which the layers' layout derives from d. The fields' names are those of
the C++ source, except wbEmb and wbHead (wbH[0], wbH[1]) and XL (residualStreamLimbs). A docstring
names the parameter file's line where the line has another name. The reader of the parameter file
refuses a value of 2^32 or more; epsF is made of two values. -/
structure Shape where
  /-- the logarithm of the number T of positions -/
  lt : Nat
  /-- the logarithm of the number of rows of a block -/
  la : Nat
  /-- the model's width -/
  d : Nat
  /-- the logarithm of the width, rounded up -/
  lPd : Nat
  /-- the size of the vocabulary -/
  V : Nat
  /-- the final norm: its reciprocal is scaled by 2^MF -/
  MF : Nat
  /-- the final norm: its product is shifted right by KF bits -/
  KF : Nat
  /-- the final norm's epsilon, as an integer -/
  epsF : Nat
  /-- 1: the tokens come from the request file -/
  toksrc : Nat
  /-- the line wb_emb: the width of a weight of the embedding -/
  wbEmb : Nat
  /-- the line wb_head: the width of a weight of the head -/
  wbHead : Nat
  /-- the line C: the clip on a position's cost -/
  clipC : Nat
  /-- the line theta: the bound on the average cost -/
  theta : Nat
  /-- the line cap: the largest allowed number of positions above the clip -/
  cap : Nat
  /-- the line s: an integer logit is a real logit times 2^s; it enters no equation -/
  logS : Nat
  /-- the line sh: the weight of a margin's middle digit is 2^sh -/
  digSh : Nat
  /-- the line sT: the exponent of the table of exponentials -/
  tabS : Nat
  /-- the line F: the scale of the table of exponentials is 2^F -/
  famF : Nat
  /-- the logarithm of the rows of a part of hf -/
  lmhf : Nat
  /-- the number of parts of hf -/
  NHf : Nat
  /-- the logarithm of the rows of hd -/
  lmhd : Nat
  /-- the logarithm of the rows of hr -/
  lmhr : Nat
  /-- the logarithm of the rows of bH, the matrix of the lookup's planes -/
  lmbH : Nat
  /-- the six lines iotaH_0 to iotaH_5; `layout` refuses a list of another length. They carry no
  freedom: line q must be the logarithm of the number of trees of call q, and 0 where there is no
  call -/
  iotaH : List Nat
  /-- the least allowed logarithm of a call's number of keys -/
  nmin : Nat
  /-- the line nminH: the least allowed logarithm of the number of keys of a call of the head; 0 if
  the line is absent -/
  NMINH : Nat
  /-- the line lidb, or 22 if it is absent: a tree of a lookup holds at most 2^LIDB keys -/
  LIDB : Nat
  /-- the limbs of a value of the residual stream: 5 with the line xl, 4 without it -/
  XL : Nat
  /-- the lines callH of the parameter file: name, kind, segments -/
  polCallsH : List (List String)
  deriving Repr, Inhabited

namespace Shape

/-- The number of positions. -/
def T (h : Shape) : Nat := 2 ^ h.lt

/-- The logarithm of S2. -/
def ls (h : Shape) : Nat := h.la - h.lt

/-- The number of neighbouring features of a block. -/
def S2 (h : Shape) : Nat := 2 ^ h.ls

end Shape

/-- The width of every weight but the embedding's. It is a constant of the format and is not fitted
to the weights. C++: WEIGHT_WIDTH_BITS. -/
def weightBits : Nat := 13

/-- The tests on the size of the vocabulary and on the widths of the weights of embedding and head.
In cp_verify they come after the tests on the widths of the layers' weights and before the layout
of the committed matrix of weights. `layout` does not run them. -/
def vocabulary (h : Shape) : Except String Unit := do
  needed (!(h.V < 2 || h.V > 2 ^ 24)) "shape-V"
  needed (!(h.wbEmb < 2 || h.wbEmb > 31 || h.wbHead != weightBits)) "policy-weight-kind"
  needed (h.wbEmb == 21) "policy-weight-width-emb"

/-- The tests that need no layout: on the final norm's lines, on the line toksrc and on the seven
lines of the acceptance policy. -/
def policy (h : Shape) : Except String Unit := do
  needed (!(h.MF < 24 || h.MF > 47 || h.KF + 14 < h.MF)) "policy-norm-F"
  needed (!(h.KF < 17 || h.KF > 32 || h.epsF < 1 || h.epsF ≥ 2 ^ 59)) "policy-norm-F"
  needed (h.toksrc == 1) "policy-toksrc"
  -- A cost clipped at C is at most C, and there are at most T positions: larger values say no more.
  -- cap minus the number of positions above the clip is written in two byte digits, so cap is below
  -- 2^16.
  needed (!(h.theta > h.clipC || h.cap > h.T || h.cap ≥ 2 ^ 16)) "policy-gap-words"
  needed (!(h.famF != 24 || h.logS > 63)) "policy-gap-words"
  needed (!(h.digSh < 7 || h.digSh > 8 ||
    (h.tabS + 4 != h.digSh && (h.tabS < h.digSh + 4 || h.tabS > h.digSh + 10)))) "policy-gap-words"

/-- The layout of the head's matrices. -/
structure HL where
  /-- the size of the vocabulary, rounded up to a multiple of S2 -/
  JV : Nat := 0
  /-- the number of entries of HE0, the first of the two segments of table values -/
  JVa : Nat := 0
  /-- the first feature of ex in hf -/
  oE : Nat := 0
  /-- the features of hf -/
  feat : Nat := 0
  /-- the features of hf, rounded up so that every part has whole columns -/
  filled : Nat := 0
  /-- the columns of a part of hf -/
  k : Nat := 0
  /-- the rows of a part of hf -/
  m : Nat := 0
  /-- the first feature of aw in hf -/
  oAw : Nat := 0
  /-- the first feature of ra in hf -/
  oRa : Nat := 0
  /-- the first feature of d1 in hf -/
  oD1 : Nat := 0
  /-- the first feature of d2 in hf -/
  oD2 : Nat := 0
  /-- the features of hd, rounded up to whole columns -/
  fillD : Nat := 0
  /-- the columns of hd -/
  kD : Nat := 0
  /-- the rows of hd -/
  mD : Nat := 0
  /-- the features of hr, rounded up to whole columns -/
  fillR : Nat := 0
  /-- the columns of hr -/
  kR : Nat := 0
  /-- the rows of hr -/
  mR : Nat := 0
  /-- the columns of bH, the matrix of the lookup's planes -/
  kb : Nat := 0
  /-- the calls, each with its segments placed in columns -/
  calls : Array CallD := #[]
  /-- the lookup's record of each call, in the same order -/
  cl : Array Call := #[]
  /-- the numbers of the lookup of all calls together, with the padding keys of each tree -/
  fs : Forest.Shape := {}

/-- The layout with all numbers 0 and no call. -/
instance : Inhabited HL := ⟨{}⟩

/-- The numbers of the layout, with the tests on them. `layout` runs `policy` first. -/
def numbers (h : Shape) : Except String HL := do
  let JV := roundUp h.V h.S2
  let JVa := 2 ^ (ceilLog2 JV - 1)
  -- 2 V ≤ 2^F: a position whose middle digits are all above 0 can then have a sum of at most 2^F.
  needed (!(JVa % h.S2 != 0 || 2 * h.V > 2 ^ h.famF)) "policy-gap-words"
  needed (!(h.lmhf < h.la || h.lmhf > 24 || h.NHf == 0 || h.NHf > 64 || h.lmhd < h.lt ||
    h.lmhd > 24 || h.lmhr < h.lt || h.lmhr > 24 || h.lmbH > 24)) "shape-request-matrix-H"
  let feat := 4 * h.d + (3 + exc) * JV
  let m := 2 ^ h.lmhf
  let unit := h.NHf * (m / h.T)
  let filled := roundUp feat unit
  let mD := 2 ^ h.lmhd
  let fillD := roundUp (2 * h.d) (mD / h.T)
  let mR := 2 ^ h.lmhr
  let fillR := roundUp (ledNRH h.XL) (mR / h.T)
  pure { JV := JV, JVa := JVa, oE := 4 * h.d + 3 * JV, feat := feat, filled := filled,
         k := filled / unit, m := m, oAw := 0, oRa := 2 * h.d, oD1 := 4 * h.d,
         oD2 := 4 * h.d + 2 * JV, fillD := fillD, kD := fillD / (mD / h.T), mD := mD,
         fillR := fillR, kR := fillR / (mR / h.T), mR := mR }

/-! ## The table of exponentials -/

/-- For q = 4 to 10: 2^32 exp(- 2^-q), rounded up. C++: NQ, where runStage fills the object HLy. -/
def tauFEFactors : List Nat :=
  [4034748383, 4162825045, 4228380000, 4261543596, 4278222806, 4286586875, 4290775040]

/-- The rows from u on, `left` of them. G is the running value of the recurrence and N its
factor: see `tauFEOf`. -/
def tauFELoop (N : Nat) : Nat → Nat → Nat → Array F → Array F
  | 0, _, _, a => a
  | left + 1, u, G, a =>
    tauFELoop N left (u + 1) ((G * N + 0xFFFFFFFF) >>> 32)
      (a.push (UInt64.ofNat (u + (((G + 131071) >>> 17) <<< 16))))

/-- The table FE of 65536 rows. Row u is u + 2^16 EX[u]. EX[u] stands for 2^F exp(- u 2^-q) with q =
sT - sh, rounded up by a recurrence on integers: G_0 = 2^(F + 17), G_(u+1) = ceil(G_u N / 2^32),
EX[u] = ceil(G_u / 2^17). N is 2^32 exp(- 2^-q) rounded up, which is 484 at q = -4. `policy` allows
q = -4 and q = 4 to 10 only. The policy's argument needs only EX[u] ≥ 2^F exp(- u 2^-q), EX[0] = 2^F
and EX[u] ≥ 1. None of this is shown here. -/
def tauFEOf (famF digSh tabS : Nat) : Array F :=
  let N := if tabS < digSh then 484 else tauFEFactors.getD (tabS - digSh - 4) 0
  tauFELoop N 65536 0 (2 ^ (famF + 17)) (Array.mkEmpty 65536)

/-! ## The calls -/

/-- The nine segments of the head: name, kind of table, number of entries. -/
def segments (h : Shape) (L : HL) : List (String × String × Nat) :=
  [("NF", "R16", h.d), ("NFH", "R16", h.d), ("HD0", "R16", L.JV), ("HD1", "R16", L.JV),
   ("ROW", "R8", ledNRH h.XL), ("HD2", "R8", L.JV), ("CNF", "FC", h.d),
   ("HE0", "FE", L.JVa), ("HE1", "FE", L.JV - L.JVa)]

/-- The list of calls that applies if the parameter file has no line callH. -/
def defaultLines : List (List String) :=
  [["R16a", "R16", "NF", "NFH", "HD0"], ["R16b", "R16", "HD1"], ["R8", "R8", "ROW", "HD2"],
   ["FEa", "FE", "HE0"], ["FEb", "FE", "HE1"], ["FC", "FC", "CNF"]]

/-- The list of calls in use. -/
def callLines (h : Shape) : List (List String) :=
  if h.polCallsH.isEmpty then defaultLines else h.polCallsH

/-- The segments that one line names, each with its number of entries. `seen` holds the names
met so far. Fails if a name is not a segment's, occurs twice, or belongs to a segment of another
kind than the line's. -/
def lineSegs (sd : List (String × String × Nat)) (kind : String) :
    List String → List String → Option (List SegAsk × List String)
  | [], seen => some ([], seen)
  | n :: ns, seen =>
    match sd.find? fun x => x.1 == n with
    | none => none
    | some x =>
      if seen.contains n || x.2.1 != kind then none
      else (lineSegs sd kind ns (n :: seen)).map fun r => ((n, x.2.2, false) :: r.1, r.2)

/-- The lines as calls, each placed in its columns. `names` holds the calls' names so far and `seen`
the segments' names so far. Fails where `lineSegs` fails, if a line has fewer than three words, and
if two lines have the same name. -/
def callsFrom (sd : List (String × String × Nat)) (floorLg : Nat) :
    List (List String) → List String → List String → Option (List CallD × List String)
  | [], _, seen => some ([], seen)
  | (name :: kind :: s :: ss) :: rest, names, seen =>
    if names.contains name then none
    else
      match lineSegs sd kind (s :: ss) seen with
      | none => none
      | some (asks, seen') =>
        (callsFrom sd floorLg rest (name :: names) seen').map fun r =>
          (place name kind asks floorLg :: r.1, r.2)
  | _ :: _, _, _ => none

/-- The least allowed logarithm of the number of keys of a call of the head. -/
def keyFloor (h : Shape) : Nat := if h.NMINH != 0 then h.NMINH else h.nmin

/-- The head's calls. Refused (policy-call-list-H) unless all of this holds. There are at most six
lines. Each line has a name, a kind and at least one segment. No two lines share a name. Each of the
nine segments occurs in exactly one line, and that line has the segment's kind. -/
def callsOf (h : Shape) (L : HL) : Except String (List CallD) := do
  let lines := callLines h
  needed (lines.length ≤ 6) "policy-call-list-H"
  let sd := segments h L
  match callsFrom sd (keyFloor h - h.lt) lines [] [] with
  | none => .error "policy-call-list-H"
  | some (calls, seen) =>
    needed (sd.all fun x => seen.contains x.1) "policy-call-list-H"
    pure calls

/-- The logarithm of the number of keys of a call: one key for each column and position. -/
def callBits (h : Shape) (c : CallD) : Nat := c.lJ + h.lt

/-- The tests on the size of each call. -/
def callSizes (h : Shape) : List CallD → Except String Unit
  | [] => pure ()
  | c :: cs => do
    let n := callBits h c
    needed (!(n < 10 || n < keyFloor h || n > 44)) "shape-call-H"
    needed (!(n < h.la || c.lJ < h.ls)) "shape-call-H"
    callSizes h cs

/-! ## No-overflow conditions -/

/-- A weight lies from -weightBound to weightBound - 1. `h9` takes this constant and not wbHead, so
it is the right bound only if `vocabulary` has tested wbHead = weightBits. C++: WEIGHT_BOUND. -/
def weightBound : Nat := 2 ^ 12

/-- The bound on a cell that a request's no-overflow conditions assume. C++: TyReq. -/
def cellBound : Nat := 2 ^ (1 + lbz)

/-- The head's no-overflow conditions on public numbers, as cp_verify tests them. Their purpose:
every relation of the sub-proof, read on integers with cells bounded by Ty, stays below 2^60, so
that an identity in the field is one on integers. That the conditions suffice for this is not shown
here. The condition J-E also assumes that each of the four limbs of a weight of the embedding is
below 2^(lbzw + 1) in size. A request's proof shows nothing of that; a key's proof of the ranges
shows more: each limb is a signed byte. The C++ source computes in 128 bits, and here the numbers
are unbounded. The two agree because no sum reaches 2^128: C, theta and cap are below 2^32 by the
reader of the parameter file, d is at most 2^20 and lt at most 16 by `admitted`, V is at most 2^23
by `numbers`, and `policy` bounds the rest. -/
def h9 (h : Shape) (L : HL) (Ty : Nat) : Except String Unit := do
  let P2 := 2 ^ 60
  let Ty2 := Ty * 257
  let TyX := Ty * (if h.XL == 5 then 4311810305 else 16843009)
  needed (2 ^ 16 * 2 ^ h.KF ≤ P2) "no-wrap-H-U-NF"
  needed (2 ^ h.MF + 2 ^ (if h.XL == 5 then 38 else 29) + 2 ^ (h.KF - 1) + 2 ^ 15 * 2 ^ h.KF +
    2 ^ 16 * (Ty2 + 32896) < P2) "no-wrap-H-W-NF"
  let SH := 2 * h.d * clampBound * weightBound + 1
  needed (2 ^ 8 + 2 ^ (h.digSh + 16) + 2 ^ (h.digSh + 31) ≤ 2 ^ 40) "no-wrap-H-W-HD0"
  needed (SH + 2 ^ 40 + 2 ^ 8 * bigH + 2 ^ h.digSh * (Ty2 + 32896) + (Ty + 128) < P2)
    "no-wrap-H-W-HD0"
  needed (SH ≤ bigH && SH + bigH + 2 ^ 32 ≤ (2 ^ 16 + 1) * 2 ^ (h.digSh + 15))
    "no-wrap-H-three-digits"
  needed (bigH ≥ SH + 2 ^ (h.digSh + 15)) "no-wrap-H-three-digits"
  let r256 := (2 ^ (8 * exc) - 1) / 255
  let Be := Ty * r256 + 128 * r256 + 1
  needed (2 ^ 16 * (Be + 2 ^ h.famF + 1) + 2 ^ 16 < P2) "no-wrap-H-HE"
  needed (L.JV * 2 ^ h.famF + 2 ^ (8 * exc) + (L.JV - h.V + 1) * 2 ^ h.famF < P2) "no-wrap-H-Z"
  needed (h.T * (2 ^ 40 + 2 ^ 8 * h.clipC + 2 ^ 40) + h.theta * h.T < P2) "no-wrap-H-E2"
  needed (h.T * (2 ^ 8 + 2 ^ 16) + h.cap < P2) "no-wrap-H-E3"
  needed (2 ^ 40 + 2 ^ 40 + h.clipC < P2) "no-wrap-H-E4"
  needed (TyX + 2 ^ (lbzw + 1) * 16843009 < P2) "no-wrap-H-J-E"
  needed ((Ty2 + 32768) + (Ty2 + max clampBound 4096) * 2 ^ 28 < P2 / 2 &&
    Ty2 + 32768 + 65536 < 2 ^ 28) "no-wrap-H-guard-radix"

/-! ## The lookup's records and the whole layout -/

/-- The lookup's record of each call. tauFC is the layers' table of the clamp, tauFE the head's
table of exponentials. -/
def lookups (h : Shape) (tauFC tauFE : Array F) (calls : List CallD) : Array Call :=
  (calls.map fun c =>
    let base : Call :=
      { name := c.name, n := callBits h c, kappa := 5, k := if c.kind == "R8" then 8 else 16 }
    if c.kind == "FC" then { base with fn := 1, t0 := 32768, tau := some tauFC }
    else if c.kind == "FE" then { base with fn := 1, t0 := 0, tau := some tauFE }
    else base).toArray

/-- True for the five segments that have one entry for each entry of the vocabulary. -/
def perEntry (name : String) : Bool :=
  name == "HD0" || name == "HD1" || name == "HD2" || name == "HE0" || name == "HE1"

/-- The vocabulary entry for which entry 0 of a segment stands. -/
def firstEntry (L : HL) (name : String) : Nat := if name == "HE1" then L.JVa else 0

/-- The number of padding keys in each tree of the lookup. Padding fills whole columns: those that
no segment takes, and in the five segments with one entry for each vocabulary entry the columns of
the entries from V on. A key at a position that is not covered is an ordinary key, so the counts do
not depend on the request. The key at column j and position t has the index j T + t, so, since dT ≥
lt, column j lies whole in tree j / 2^(dT - lt) of its call. -/
def pubOf (h : Shape) (L : HL) (fs : Forest.Shape) (calls : List CallD) :
    Except String (Array Nat) := do
  let cs := fs.dT - h.lt
  let mut pub := Array.replicate fs.NT 0
  for (cd, q) in calls.zipIdx do
    let base := fs.first.getD q 0
    needed (cd.J / 2 ^ cs == 2 ^ fs.iota.getD q 0) "internal-forest-place"
    for j in List.range cd.J do
      if cd.used.getD j 0 == 0 then pub := pub.modify (base + j / 2 ^ cs) (· + h.T)
    for g in cd.segs do
      if perEntry g.name then
        let real := h.V - firstEntry L g.name
        for x in List.range (g.n - real) do
          pub := pub.modify (base + g.pos.getD (real + x) 0 / 2 ^ cs) (· + h.T)
  pure pub

/-- What the caller must have tested before it calls `layout`. cp_verify makes these tests earlier,
under the names in brackets: 4 ≤ lt ≤ 16 and 1 ≤ d ≤ 2^20 (shape-words), lt < la ≤ 16 (shape-la),
nmin ≤ 28 (shape-words), nminH is 0 or from 2 to 28 (policy-nminH), 22 ≤ lidb ≤ 30 (policy-lidb,
plan-identity-cap), XL is 4 or 5 (policy-xl admits the line xl with the value 5 alone), 2 ≤ V ≤ 2^24
(shape-V, in `vocabulary`), S2 divides d (shape-la). lPd is the logarithm of d, rounded up, as the
layers' layout makes it. This function tests all of this once more. It also tests that there are six
values iotaH. The reason: outside these ranges the divisions and differences in `layout` would mean
something else than in the C++ source, and a large nmin or nminH would make `place` build a call of
more than 2^28 keys. -/
def admitted (h : Shape) : Bool :=
  decide (4 ≤ h.lt) && decide (h.lt ≤ 16) && decide (1 ≤ h.d) && decide (h.d ≤ 2 ^ 20) &&
    decide (h.lt < h.la) && decide (h.la ≤ 16) && decide (h.nmin ≤ 28) &&
    h.NMINH != 1 && decide (h.NMINH ≤ 28) && decide (22 ≤ h.LIDB) && decide (h.LIDB ≤ 30) &&
    (h.XL == 4 || h.XL == 5) && decide (2 ≤ h.V) && decide (h.V ≤ 2 ^ 24) &&
    h.iotaH.length == 6 && h.lPd == ceilLog2 h.d && h.d % h.S2 == 0

/-- The whole layout of the head's sub-proof, with the tests on its public numbers in the order of
the C++ source. tauFC is the layers' table of the clamp. If the caller left out a test that
`admitted` lists and it would have failed, `layout` refuses with internal-head-shape, a name that
marks a fault of the program. cp_verify ends this part with a test that every call has kappa = 5. It
has no line here: `lookups` sets 5, and `Forest.shape` tests it. The tests of the plan are in
OnBytes/Model/HeadPlan.lean. -/
def layout (h : Shape) (tauFC : Array F) : Except String HL := do
  needed (admitted h) "internal-head-shape"
  policy h
  let L ← numbers h
  let calls ← callsOf h L
  let tauFE := tauFEOf h.famF h.digSh h.tabS
  -- Without a stored table a call would use the closed form tau(t) = t, whatever the value of fn.
  needed (tauFE.size == 65536) "internal-table-FE"
  callSizes h calls
  let cl := lookups h tauFC tauFE calls
  let fs ← Forest.shape cl h.LIDB
  needed (h.la ≤ fs.dT) "forest-depth-H"
  let kb ← Forest.planeCols fs h.lmbH
  for q in List.range calls.length do
    needed (h.iotaH.getD q 0 == fs.iota.getD q 0) "shape-call-H"
  let cl := cl.mapIdx fun q c => { c with iota := fs.iota.getD q 0 }
  let pub ← pubOf h L fs calls
  let fs := { fs with calls := cl, pub := pub }
  Forest.pubAsk fs pub
  needed ((h.iotaH.drop calls.length).all (· == 0)) "header-absent-call-H"
  h9 h L cellBound
  pure { L with kb := kb, calls := calls.toArray, cl := cl, fs := fs }

/-! ## The request -/

/-- What the verifier keeps of the caller's request and reply. -/
structure StOwn where
  /-- all words of the request file: the T tokens, then r and e -/
  req : Array UInt32
  /-- the first covered position -/
  r : Nat
  /-- the position after the last covered one -/
  e : Nat
  /-- the reply: the token that the caller was given -/
  y : Nat
  deriving Inhabited

/-- Reads the request P and the reply Q. P must have exactly T + 2 words and Q one, and r < e ≤ T.
If e < T no covered position reads the reply, and it must be 0. T must come from the parameter file.
The caller refuses a file whose length is not a multiple of 4 bytes. The two digests that
the C++ stFromCall also forms are not formed here. -/
def stFromCall (P Q : Array UInt32) (T : Nat) : Except String StOwn := do
  needed (!(P.isEmpty || Q.isEmpty)) "statement-required"
  needed (!(P.size != T + 2 || Q.size != 1)) "statement-range"
  let r := (P.getD T 0).toNat
  let e := (P.getD (T + 1) 0).toNat
  let y := (Q.getD 0 0).toNat
  needed (!(r ≥ e || e > T || (e < T && y != 0))) "statement-range"
  pure { req := P, r := r, e := e, y := y }

/-- The covered positions of a request. -/
structure Covered where
  /-- the T tokens of the request -/
  tokv : Array Nat
  /-- for each position: whether it is covered -/
  hOn : Array Bool
  /-- for each covered position the token that is checked there: the next token of the request,
  or the reply at the last position; 0 at a position that is not covered -/
  hWin : Array Nat
  /-- for each position: whether it is covered and its checked token is one of the request's. Only
  such a position has a cost. The reply at the last position has none: by the margins it is meant to
  have the largest logit, the lowest index on ties -/
  hOnC : Array Bool
  /-- the number of positions with a cost -/
  hRC : Nat
  deriving Inhabited

/-- True if each of the four arrays has one entry for each of T positions. -/
def Covered.sized (c : Covered) (T : Nat) : Bool :=
  c.tokv.size == T && c.hOn.size == T && c.hWin.size == T && c.hOnC.size == T

/-- The covered positions. Tests that every token and the reply are entries of the vocabulary, and
once more the request's length and r < e ≤ T. The tokens and the positions r and e are all taken
from `so.req`, the words of the request file. cp_verify does the same, because it hashes these words
into the statement. -/
def coveredOf (so : StOwn) (T V : Nat) : Except String Covered := do
  needed (so.y < V) "token-range"
  needed (so.req.size == T + 2) "token-length"
  let tokv := (so.req.extract 0 T).map (·.toNat)
  let rowR := (so.req.getD T 0).toNat
  let rowE := (so.req.getD (T + 1) 0).toNat
  needed (tokv.all fun v => decide (v < V)) "token-range"
  needed (!(rowR ≥ rowE || rowE > T)) "statement-range"
  let on := fun t => decide (rowR ≤ t) && decide (t < rowE)
  pure {
    tokv := tokv
    hOn := (Array.range T).map on
    hWin := (Array.range T).map fun t =>
      if on t then (if t + 1 < T then tokv.getD (t + 1) 0 else so.y) else 0
    hOnC := (Array.range T).map fun t => on t && decide (t + 1 < T)
    hRC := ((List.range T).filter fun t => on t && decide (t + 1 < T)).length }

end OnBytes.Model.Head
