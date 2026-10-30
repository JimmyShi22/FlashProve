-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/LayerLayout.lean: the layout of a layer sub-proof, from public numbers alone.

A proof takes the model's layers in groups of 2^ll. One sub-proof covers one group. All groups
have the same layout. It says which tensors lie where in the matrices that the prover commits to,
which lookup calls there are and on which columns their segments lie, and which kinds of weight
matrices occur. It follows from the model's lines of the parameter file and from the lines "call".

The matrices. A feature is a run of T rows in one column of a matrix, one row for each token. af, ad
and ar hold the group's tensors; af and ad are cut into parts of equal size. qa holds q, k and v
and, at profile 4, the attention output; attention's sub-proof reads it too. b holds the
planes of the lookup's counts. Two more matrices hold the residual stream that comes into the group
and the one that goes out. The number of features is rounded up so that every column of every part
is full.

This file follows the C++ routine named layout (verifier/src/cp_verify.cpp) and makes its tests in
the same order. A failed test ends the computation with the name under which the C++ verifier
refuses. One name is shorter here: the C++ verifier appends the call's name to shape-call. Three
tests of the routine that can never fail are left out. One test on the number of limbs is added (see
layoutBase). It has the name of one of the three, internal-layout-words.

It also holds the tests on the file of quantization scales and the conditions under which no sum
of a layer sub-proof can wrap around in the field (C++: q9 in runStage).

The order of the tests. The functions here are called one by one, and the C++ verifier makes tests
of other parts between them. Its order is: layout; scalesOf; scalesHeld; the digests of the tables
SILU and FS; noWrap; weightWidthsHeld; the layout of the committed weights; ropeOf; the digest of
the rotary table; the head's and attention's layouts; readsOf. noWrap must not run before
scalesHeld has passed.

Main definitions: Shape, Ten, KindD, Lay, layoutBase, layoutLook, layout, ropeOf,
Reads, readsOf, Scales, scalesOf, scalesHeld, noWrap, weightWidthsHeld, layoutNames.

What is not claimed: nothing is proved here.
-/
import OnBytes.Model.LayerTables
import OnBytes.Model.Calls
import OnBytes.Model.Tensors
import OnBytes.Model.Forest
import OnBytes.Model.Ledger

namespace OnBytes.Model.Layer

/-- True if x is neither 0 nor a power of two. -/
def manyBits (x : Nat) : Bool := x &&& (x - 1) != 0

/-! ## The public numbers -/

/-- The numbers of the parameter file on which a layer sub-proof depends. Each field has the name of
its line, or of the statement's word that holds it. The caller must make sure that eps1, eps2, epsF,
theta0 and seed are below 2^64, all other numbers below 2^32, eg from 4 to 8 and smax at most 4095
(the reader of the parameter file tests eg and smax: OnBytes/Model/Config.lean). The functions of
this file do not test that. -/
structure Shape where
  /-- the profile: 3, or 4 (see Shape.p4); the statement's word is this number plus 16 -/
  prof : Nat
  /-- the logarithm of the number of tokens -/
  lt : Nat
  /-- the number of layers -/
  L : Nat
  /-- the logarithm of the number of layers in a group -/
  ll : Nat
  /-- the model's width -/
  d : Nat
  /-- the number of query heads -/
  H : Nat
  /-- the number of key heads -/
  Gk : Nat
  /-- the width of a head -/
  dh : Nat
  /-- the inner width of the feed-forward part -/
  f : Nat
  /-- the inner width of one expert -/
  fe : Nat
  /-- the number of routed experts; 0 if there are none -/
  NE : Nat
  /-- the constant that is added to the sum of squares in a layer's first norm -/
  eps1 : Nat
  /-- the constant that is added to the sum of squares in a layer's second norm -/
  eps2 : Nat
  /-- the constant that is added to the sum of squares in the final norm -/
  epsF : Nat
  /-- the exponent of the rotary table's scale -/
  cs : Nat
  /-- the base of the rotary angles -/
  theta0 : Nat
  /-- the digit form of the rounding sites of q and k: 0, 1 or 2, the limbs of their tensor of high
  digits. The shift of such a site is at most 16, 24 or 32 (shiftHeld) -/
  hq : Nat
  /-- the digit form of the sites of v -/
  hv : Nat
  /-- the digit form of the sites of the attention output's product -/
  ho : Nat
  /-- the digit form of the gate's sites -/
  hgD : Nat
  /-- the digit form of the sites of the up product -/
  huD : Nat
  /-- the digit form of the sites of the down product -/
  hdD : Nat
  /-- the digit form of the router's sites -/
  hr : Nat
  /-- 1: the up product has a range segment of its own -/
  ut : Nat
  /-- the logarithm of the rows of a block in a long read -/
  la : Nat
  /-- the least logarithm of a call's number of keys -/
  nmin : Nat
  /-- the line D, a power of two from 2 to 4096, which the layout of the committed weights reads -/
  D : Nat
  /-- the number of combinations of the smallness test -/
  tau : Nat
  /-- the logarithm of the rows of a part of matrix af -/
  lmaf : Nat
  /-- the number of parts of matrix af -/
  NAf : Nat
  /-- the logarithm of the rows of a part of matrix ad -/
  lmad : Nat
  /-- the number of parts of matrix ad -/
  NAd : Nat
  /-- the logarithm of the rows of matrix ar -/
  lmar : Nat
  /-- the logarithm of the rows of matrix b -/
  lmb : Nat
  /-- the logarithm of the rows of matrix qa -/
  lmq : Nat
  /-- the logarithm of the rows of a matrix of the residual stream -/
  lmx : Nat
  /-- the widths of the twelve kinds of weights -/
  wb : Array Nat
  /-- the eight words iota, one for each possible call: the call's keys are split into 2^iota trees.
  The word of a call that is absent is 0 -/
  iota : Array Nat
  /-- the seed of the public numbers that take the place of the attention output below profile 4 -/
  seed : Nat
  /-- the line gcl: the key of table SILU is clamped -/
  gcl : Bool
  /-- the line rcl: the router's logits are clamped -/
  rcl : Bool
  /-- the number of limbs of a value of the residual stream: 5 with the line xl, 4 without it -/
  xl : Nat
  /-- the line lidb, or 22 without it: a tree of a lookup holds at most 2^lidb keys -/
  lidb : Nat
  /-- the line eg (4 to 7), or 8 without it: the step between the keys of table SILU is 2^-eg -/
  eg : Nat := 8
  /-- the line smax, or 4095 without it: the values of table SILU are clamped to -smax .. smax -/
  smax : Nat := 4095
  deriving Inhabited

/-- True at profile 4: a proof then has an attention sub-proof for each group of layers. -/
def Shape.p4 (h : Shape) : Bool := h.prof == 4

/-- True if every second layer has routed experts: at profile 3, or at profile 4 if NE is not 0. -/
def Shape.p3 (h : Shape) : Bool := h.prof == 3 || (h.prof == 4 && decide (0 < h.NE))

/-! ## Tensors -/

/-- One tensor: a named family of values in a committed matrix. C++: Ten. -/
structure Ten where
  /-- the tensor's name -/
  name : String
  /-- the matrix that holds it: 0 af, 1 ad, 2 ar, 3 qa -/
  mat : Nat
  /-- the limbs -/
  nl : Nat
  /-- the instances of each limb, that is how often it occurs: once for each layer of the group, or
  for each layer with routed experts; in xs once for each write to the stream except the group's
  last; in row once for each norm -/
  cnt : Nat
  /-- the features of one instance of one limb -/
  J : Nat
  /-- the first feature -/
  OFF : Nat
  deriving Repr, Inhabited

/-- The tensor's place. C++: Ten::at. -/
def Ten.place (t : Ten) : TenAt := ⟨t.OFF, t.nl, t.cnt, t.J⟩

/-- Tests that the two lists name the same tensors in the same order at the same places. One list
is that of the sub-proof that owns a matrix, the other that of a sub-proof that reads it.
C++: tensorsAgree. -/
def tensorsAgree (owner reader : List (String × TenAt)) : Except String Unit :=
  refuseIf (owner != reader) "plan-tensor-layout"

/-- The runs of features of a list of tensors: for each limb of each layer the first feature and
the number of features. -/
def tensorRuns (ten : List (String × TenAt)) : List (Nat × Nat) :=
  ten.flatMap fun t =>
    (List.range t.2.nl).flatMap fun l =>
      (List.range t.2.cnt).map fun i => (tenCell t.2 l i 0, t.2.J)

/-- The feature after the last run if the runs, in their order, follow each other from feature
"first" on without a gap; none otherwise. -/
def runsEnd : List (Nat × Nat) → Nat → Option Nat
  | [], first => some first
  | r :: rs, first => if r.1 == first then runsEnd rs (first + r.2) else none

/-- Tests that the tensors cover each feature below feat exactly once, and that in each tensor J,
the features of one limb of one layer, is not 0 and is a multiple of S2: some reads take S2 features
at a time. arr names the matrix in the refusal. C++: tensorsFill. -/
def tensorsFill (ten : List (String × TenAt)) (feat S2 : Nat) (arr : String) :
    Except String Unit := do
  let name := "plan-tensor-layout-fill-" ++ arr
  refuseIf (ten.any fun t => t.2.J == 0 || t.2.J % S2 != 0) name
  let runs := (tensorRuns ten).mergeSort fun a b => decide (a.1 ≤ b.1)
  refuseIf (runsEnd runs 0 != some feat) name

/-- A kind of weight matrix that is present. C++: KindD. -/
structure KindD where
  /-- the kind's number -/
  idx : Nat
  /-- its name -/
  name : String
  /-- the length of a run of weights of this kind (not a segment of a lookup call) -/
  L : Nat
  /-- the number of runs of weights of this kind, limbs included -/
  segs : Nat
  deriving Repr, Inhabited

/-! ## The layout -/

/-- Everything about a layer sub-proof that follows from the public numbers and the lines "call".
C++: Lay. -/
structure Lay where
  /-- the public numbers -/
  h : Shape
  /-- the number of tokens -/
  T : Nat := 0
  /-- the layers of a group -/
  Lam : Nat := 0
  /-- the number of groups -/
  NGr : Nat := 0
  /-- d rounded up to a power of two -/
  Pd : Nat := 0
  /-- f rounded up to a power of two -/
  Pf : Nat := 0
  /-- the features of a block of a long read -/
  S2 : Nat := 0
  /-- the writes to the residual stream in a layer -/
  NW : Nat := 2
  /-- the norms of a layer -/
  NN : Nat := 2
  /-- the norms of a group -/
  NI : Nat := 0
  /-- the features of q -/
  dq : Nat := 0
  /-- the features of k, and of v -/
  dkv : Nat := 0
  /-- the features of q and k together -/
  nqk : Nat := 0
  /-- the logarithm of Pf -/
  lPf : Nat := 0
  /-- the logarithm of fe; 0 without routed experts -/
  lfe : Nat := 0
  /-- the logarithm of Pd -/
  lPd : Nat := 0
  /-- the logarithm of S2 -/
  ls : Nat := 0
  /-- the logarithm of dh -/
  ldh : Nat := 0
  /-- the tensors -/
  ten : List Ten := []
  /-- for each of the matrices af, ad, ar, qa: the features in use -/
  feat : Array Nat := #[]
  /-- for each of af, ad, ar, qa: the features in use, rounded up to whole columns in all parts -/
  filled : Array Nat := #[]
  /-- for each of af, ad, ar, qa: the columns of a part -/
  kcol : Array Nat := #[]
  /-- for each of af, ad, ar, qa: the rows of a part -/
  mrow : Array Nat := #[]
  /-- for each of af, ad, ar, qa: the number of parts -/
  parts : Array Nat := #[]
  /-- the features of a matrix of the residual stream, rounded up to whole columns -/
  xbFilled : Nat := 0
  /-- the columns of a matrix of the residual stream -/
  kxb : Nat := 0
  /-- the rows of a matrix of the residual stream -/
  mxb : Nat := 0
  /-- where the one tensor of the residual stream lies in its matrix -/
  xb : TenAt := {}
  /-- the kinds of weight matrices that are present -/
  kinds : List KindD := []
  /-- the lookup calls, with their segments placed in columns -/
  calls : Array CallD := #[]
  /-- table SILU as words: entry t is 4096 plus the table's value at t -/
  silu : Array Nat := #[]
  /-- table FS as words; empty without routed experts -/
  fs : Array Nat := #[]
  /-- the rows of the clamp's table -/
  tauFC : Array F := #[]
  /-- the rows of the lookup table that holds SILU -/
  tauFL : Array F := #[]
  /-- the rows of the lookup table that holds FS -/
  tauFS : Array F := #[]
  /-- the layers of a group that have routed experts -/
  LamM : Nat := 0
  /-- the lookup's record of each call, in the order of calls -/
  cl : Array Call := #[]
  /-- the numbers of the lookup of all calls together, with the padding keys of each tree -/
  fo : Forest.Shape := {}
  /-- the columns of the matrix b, which holds the planes of the lookup's counts -/
  kbm : Nat := 0

/-- The tensor with the name n, if there is one. C++: Lay::T_, which refuses otherwise. -/
def Lay.T_ (y : Lay) (n : String) : Option Ten := y.ten.find? fun t => t.name == n

/-- The number of the call with the name n, if there is one. -/
def Lay.callNo (y : Lay) (n : String) : Option Nat := y.calls.findIdx? fun c => c.name == n

/-- The tensors in the order of the layout: name, matrix, limbs, instances (see Ten.cnt), features.
A tensor with no limb is absent and leaves no gap. What the check asks of each tensor is said by the
keys and claims that read it (line in OnBytes/Model/LayerForms.lean; OnBytes/Model/Layer.lean). C++:
the calls of add in layout. -/
def tensorAsks (h : Shape) (Lam LamM nqk dq dkv : Nat) : List (String × Nat × Nat × Nat × Nat) :=
  let d := h.d
  let f := h.f
  let NE := h.NE
  (if h.gcl then [("g0", 0, 1, Lam, f), ("gc", 0, 1, Lam, f)] else [("gi", 0, 2, Lam, f)]) ++
  [("s", 0, 2, Lam, f), ("u", 0, 2, Lam, f), ("rg", 0, h.hgD, Lam, f), ("ru", 0, h.huD, Lam, f),
   ("xs", 0, h.xl, 2 * Lam - 1, d), ("ro", 0, h.ho, Lam, d), ("rd", 0, h.hdD, Lam, d),
   ("aw", 0, 2, Lam, d), ("ra", 0, 2, Lam, d), ("mw", 0, 2, Lam, d), ("rm", 0, 2, Lam, d),
   ("qkw", 0, 2, Lam, nqk), ("rqk", 0, h.hq, Lam, nqk), ("vw", 0, 2, Lam, dkv),
   ("rv", 0, h.hv, Lam, dkv)] ++
  (if h.gcl then [("gh", 0, 2, Lam, f)] else []) ++
  [("a", 1, 2, Lam, d), ("m", 1, 2, Lam, d)] ++
  (if h.p3 then
    [("xr", 1, 2, LamM, d), ("lr", 2, 2, LamM, NE), ("rl", 2, h.hr, LamM, NE),
     ("sel", 2, 1, LamM, NE), ("sc", 2, 3, LamM, 1)]
   else []) ++
  [("row", 2, 1, 2 * Lam, ledNR h.xl)] ++
  (if h.rcl then [("ly", 2, 2, LamM, NE), ("l3", 2, 1, LamM, NE)] else []) ++
  [("q", 3, 2, Lam, dq), ("kx", 3, 2, Lam, dkv), ("v", 3, 2, Lam, dkv)] ++
  (if h.p4 then [("o", 3, 2, Lam, dq)] else [])

/-- Places the tensors one after the other in their matrices. off holds the first free feature of
each of the four matrices. Returns the tensors and the features in use. C++: add in layout. -/
def layTensors : List (String × Nat × Nat × Nat × Nat) → Array Nat → List Ten × Array Nat
  | [], off => ([], off)
  | (n, mat, nl, cnt, J) :: rest, off =>
    if nl == 0 then layTensors rest off
    else
      let r := layTensors rest (off.modify mat (· + nl * cnt * J))
      (⟨n, mat, nl, cnt, J, off.getD mat 0⟩ :: r.1, r.2)

/-- The segments that are present: name, kind of table, length, and whether the segment exists only
on layers with routed experts. The keys of each segment: line in OnBytes/Model/LayerForms.lean. C++:
the calls of sg and hi in layout. -/
def segmentList (h : Shape) (nqk dkv : Nat) : List (String × String × Nat × Bool) :=
  let d := h.d
  let f := h.f
  let NE := h.NE
  let p3 := h.p3
  let hi (n : String) (form len : Nat) (moe : Bool) : List (String × String × Nat × Bool) :=
    if form == 0 then [] else [(n, if form == 1 then "R8" else "R16", len, moe)]
  [("G", "R16", f, false), ("U", "R16", f, false), ("UT", "R16", f, false),
   ("QK", "R16", nqk, false)] ++ hi "QKH" h.hq nqk false ++
  [("N1", "R16", d, false), ("N1H", "R16", d, false), ("N2", "R16", d, false),
   ("N2H", "R16", d, false), ("O", "R16", d, false), ("D", "R16", d, false),
   ("V", "R16", dkv, false)] ++
  (if p3 then
    [("XR", "R16", d, true), ("LR", "R16", NE, true), ("LT", "R16", NE, true),
     ("DD", "R16", NE, true)]
   else []) ++
  hi "GH" h.hgD f false ++ hi "UH" h.huD f false ++ hi "OH" h.ho d false ++
  hi "DH" h.hdD d false ++ hi "VH" h.hv dkv false ++
  [("ROW", "R8", ledNR h.xl * 2, false)] ++
  (if p3 then
    hi "LH" h.hr NE true ++ [("SEL", "R8", NE, true)] ++
    (if h.rcl then [("L3", "R8", NE, true)] else [])
   else []) ++
  (if h.gcl then [("G0", "R8", f, false)] else []) ++
  [("CN1", "FC", d, false), ("CN2", "FC", d, false), ("CQK", "FC", nqk, false),
   ("CV", "FC", dkv, false)] ++
  (if h.rcl then [("CLR", "FC", NE, true)] else []) ++
  (if p3 then [("MR", "FS", 1, true)] else []) ++
  (if h.gcl then [("CG", "FS", f, false)] else []) ++
  [("F", "FL", f, false)]

/-- The list of calls that is used if the parameter file has no line "call". It lacks the segment
UT, so the test on the list refuses it. Kept because the C++ routine has it. -/
def builtInCalls (p3 : Bool) : List (List String) :=
  if !p3 then
    [["R16a", "R16", "G", "U"],
     ["R16b", "R16", "N1", "N1H", "N2", "N2H", "O", "D", "V"],
     ["R16c", "R16", "QK", "QKH"],
     ["R8a", "R8", "GH", "UH"],
     ["R8b", "R8", "OH", "DH", "VH", "ROW"],
     ["FC", "FC", "CN1", "CN2", "CQK", "CV"],
     ["FL", "FL", "F"]]
  else
    [["R16a", "R16", "G", "U"],
     ["R16b", "R16", "N1", "N1H", "N2", "N2H", "O", "D", "V"],
     ["R16c", "R16", "QK", "QKH", "XR", "LR", "LT", "DD"],
     ["R8", "R8", "GH", "UH", "OH", "DH", "VH", "ROW", "LH", "SEL"],
     ["FC", "FC", "CN1", "CN2", "CQK", "CV"],
     ["FS", "FS", "MR"],
     ["FL", "FL", "F"]]

/-- The segments that one line names, each with its length. seen: the names of the segments that
earlier lines or earlier words of this line have taken. Refuses a name that is not present, is
taken already, or is not of the call's kind. -/
def takeSegments (sd : List (String × String × Nat × Bool)) (kind : String) :
    List String → List String → Except String (List SegAsk × List String)
  | [], seen => pure ([], seen)
  | n :: ns, seen =>
    match sd.find? fun s => s.1 == n with
    | none => throw "policy-call-list"
    | some s => do
      refuseIf (seen.contains n || s.2.1 != kind) "policy-call-list"
      let r ← takeSegments sd kind ns (n :: seen)
      pure ((s.1, s.2.2.1, s.2.2.2) :: r.1, r.2)

/-- Reads the lines "call": for each call its name, its kind and its segments. names: the names of
the calls so far. Every line names at least one segment, no two calls share a name, and no call is
named V, a, b or E: the sub-proof's own points have the names Z_V, Z_a, Z_b and Z_E. -/
def takeCalls (sd : List (String × String × Nat × Bool)) :
    List (List String) → List String → List String →
    Except String (List (String × String × List SegAsk) × List String)
  | [], _, seen => pure ([], seen)
  | ln :: rest, names, seen =>
    match ln with
    | name :: kind :: s :: more => do
      refuseIf (names.contains name) "policy-call-list"
      refuseIf (["V", "a", "b", "E"].contains name) "policy-call-list"
      let a ← takeSegments sd kind (s :: more) seen
      let r ← takeCalls sd rest (name :: names) a.2
      pure ((name, kind, a.1) :: r.1, r.2)
    | _ => throw "policy-call-list"

/-- The kinds of weight matrices that are present. -/
def kindList (h : Shape) (Lam LamM dq dkv : Nat) : List KindD :=
  let d := h.d
  let f := h.f
  let fe := h.fe
  let NE := h.NE
  let p3 := h.p3
  let nd := if p3 then LamM else Lam
  [⟨0, "qk", 64, 2 * Lam * d * h.dh⟩, ⟨1, "v", dkv, 2 * Lam * d⟩, ⟨2, "o", d, 2 * Lam * dq⟩,
   ⟨3, "g", f, 2 * nd * d⟩, ⟨4, "u", f, 2 * nd * d⟩] ++
  (if p3 then
    [⟨5, "gs", fe, 2 * LamM * d⟩, ⟨6, "us", fe, 2 * LamM * d⟩, ⟨7, "gr", fe, 2 * LamM * NE * d⟩,
     ⟨8, "ur", fe, 2 * LamM * NE * d⟩]
   else []) ++
  [⟨9, "dn", d, if p3 then 2 * (LamM * f + LamM * fe) else 2 * Lam * f⟩] ++
  (if p3 then [⟨10, "dnr", d, 2 * LamM * NE * fe⟩, ⟨11, "r", NE, 2 * LamM * d⟩] else [])

/-- Row t of table FC: t, and from bit 28 on the clamp of t - 2^15, shifted to be positive. -/
def rowFC (t : Nat) : Nat :=
  let c := if t + clamp < 32768 then 0 else min (t + clamp - 32768) (2 * clamp)
  t + (c + 1) * 2 ^ 28

/-- Row t of table FS. With the gate's clamp a row of the upper half holds the clamp from bit 28 on
and a flag at bit 40. Every other row holds the table's value from bit 17 on. -/
def rowFS (gcl : Bool) (fs : Array Nat) (t : Nat) : Nat :=
  if gcl && decide (32768 ≤ t) then t + fs.getD t 0 * 2 ^ 28 + 2 ^ 40 else t + fs.getD t 0 * 2 ^ 17

/-- The sizes of one of the four matrices: features in use, features with the fill, columns of a
part, rows of a part, parts. -/
def matrixSizes (T off lm na : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let mrow := 2 ^ lm
  let unit := na * (mrow / T)
  let filled := roundUp off unit
  (off, filled, filled / unit, mrow, na)

/-- Refuses more than 28 groups of layers. Beyond that the prover's random streams for a sub-proof
and for the opening would share numbers. C++: groupsBaseHeld. -/
def groupsBaseHeld (NGr : Nat) : Except String Unit :=
  refuseIf (2 + 2 * NGr > 59) "plan-groups-base"

/-- The first half of the layout. Tests the shape and the other public numbers, in the order of the
C++ routine, and derives from them all but the lookup's numbers. pc: the lines "call" of the
parameter file, each as its words after "call". The test that xl is 4 or 5 has no counterpart in the
C++ routine, whose number of limbs is 4 or 5 by the way it is set. -/
def layoutBase (h : Shape) (pc : List (List String)) : Except String Lay := do
  let d := h.d
  let f := h.f
  let fe := h.fe
  refuseIf (h.prof < 3 || h.prof > 4) "policy-profile"
  let p3 := h.p3
  refuseIf (h.lt < 4 || h.lt > 16 || h.ll < 1 || h.ll > 6 || d == 0 || f == 0 || d > 2 ^ 20 ||
    f > 2 ^ 20 || (p3 && (manyBits fe || f != 2 * fe || (h.ll == 1 && fe == 1)))) "shape-words"
  let T := 2 ^ h.lt
  let Lam := 2 ^ h.ll
  refuseIf (h.L == 0 || h.L % Lam != 0) "shape-L"
  let NGr := h.L / Lam
  -- A matrix has the label 256 s + its number, where s, its sub-proof's number, is at most
  -- 1 + 2 NGr. Under this bound all labels are below 2^24, where the weight matrices' labels begin.
  refuseIf (2 + 2 * NGr ≥ 2 ^ 16) "shape-groups"
  groupsBaseHeld NGr
  let lPd := ceilLog2 d
  let lPf := ceilLog2 f
  let lfe := if p3 then ceilLog2 fe else 0
  refuseIf (h.la ≤ h.lt || h.la > 16) "shape-la"
  let ls := h.la - h.lt
  let S2 := 2 ^ ls
  refuseIf (d % S2 != 0 || f % S2 != 0 || (p3 && fe % S2 != 0)) "shape-la"
  refuseIf ([h.eps1, h.eps2].any fun e => e < 1 || e ≥ 2 ^ 59) "policy-norm"
  refuseIf (h.H == 0 || h.Gk == 0 || h.dh == 0 || manyBits h.dh || h.dh < 2 || h.H * h.dh != d ||
    h.H + h.Gk > 64) "shape-heads"
  let dq := h.H * h.dh
  let dkv := h.Gk * h.dh
  let nqk := dq + dkv
  refuseIf (dkv % S2 != 0 || nqk % S2 != 0) "shape-la"
  refuseIf (h.cs != 12) "policy-cs"
  -- The classes of rounding sites, in the order of their numbers: q, k, v, o, gate, up, down, then
  -- the router's, then those of the layers with experts, which share the dense classes' forms.
  refuseIf ([h.hq, h.hq, h.hv, h.ho, h.hgD, h.huD, h.hdD].any (· > 2)) "policy-forms"
  refuseIf (!p3 && h.hr != 0) "header-absent-class"
  refuseIf (p3 && h.hr > 2) "policy-forms"
  refuseIf (h.ut != 1) "policy-ut"
  refuseIf (h.D < 2 || h.D > 4096 || manyBits h.D) "shape-D"
  refuseIf (h.xl != 4 && h.xl != 5) "internal-layout-words"
  let NE := h.NE
  let LamM := Lam / 2
  refuseIf (p3 && (NE < 2 || NE > 4096 || manyBits NE)) "shape-NE"
  refuseIf (h.gcl && !p3) "policy-gcl"
  refuseIf (h.rcl && !p3) "policy-rcl"
  let laid := layTensors (tensorAsks h Lam LamM nqk dq dkv) #[0, 0, 0, 0]
  let lm := [h.lmaf, h.lmad, h.lmar, h.lmq]
  let na := [h.NAf, h.NAd, 1, 1]
  refuseIf (h.lmq < h.la) "shape-la"
  refuseIf ((lm.zip na).any fun x => x.1 < h.lt || x.1 > 24 || x.2 == 0 || x.2 > 64)
    "shape-request-matrix"
  let sizes := ((laid.2.toList.zip lm).zip na).map fun x => matrixSizes T x.1.1 x.1.2 x.2
  refuseIf (h.lmaf < h.la) "shape-la"
  refuseIf (h.lmx < h.la || h.lmx > 24) "shape-request-matrix"
  let mxb := 2 ^ h.lmx
  let unit := mxb / T
  let xbFilled := roundUp (h.xl * d) unit
  let xb : TenAt := ⟨0, h.xl, 1, d⟩
  tensorsFill [("x", xb)] (h.xl * d) S2 "stream"
  tensorsFill ((laid.1.filter fun t => t.mat == 3).map fun t => (t.name, t.place))
    (laid.2.getD 3 0) S2 "qa"
  let sd := segmentList h nqk dkv
  let cl := if pc.isEmpty then builtInCalls p3 else pc
  refuseIf (cl.length > 8) "policy-call-list"
  let taken ← takeCalls sd cl [] []
  refuseIf (sd.any fun s => !taken.2.contains s.1) "policy-call-list"
  refuseIf (h.lmb > 24) "shape-lmb"
  -- place makes 2^(nmin - ll - lt) columns before any test on a call's size, so a large nmin must
  -- be refused here.
  refuseIf (h.nmin > 28) "shape-words"
  let calls := taken.1.map fun c => place c.1 c.2.1 c.2.2 (h.nmin - h.ll - h.lt)
  let (silu, fs) := gateTables h.eg h.smax p3 h.gcl
  pure {
    h := h, T := T, Lam := Lam, NGr := NGr, Pd := 2 ^ lPd, Pf := 2 ^ lPf, S2 := S2,
    NI := 2 * Lam, dq := dq, dkv := dkv, nqk := nqk, lPf := lPf, lfe := lfe, lPd := lPd, ls := ls,
    ldh := ceilLog2 h.dh, ten := laid.1,
    feat := (sizes.map (·.1)).toArray, filled := (sizes.map (·.2.1)).toArray,
    kcol := (sizes.map (·.2.2.1)).toArray, mrow := (sizes.map (·.2.2.2.1)).toArray,
    parts := (sizes.map (·.2.2.2.2)).toArray,
    xbFilled := xbFilled, kxb := xbFilled / unit, mxb := mxb, xb := xb,
    kinds := kindList h Lam LamM dq dkv, calls := calls.toArray,
    tauFC := (Array.range 65536).map fun t => (rowFC t).toUInt64,
    silu := silu, fs := fs,
    tauFL := (Array.range 65536).map fun t => (t + silu.getD t 0 * 2 ^ 28).toUInt64,
    tauFS := if p3 then (Array.range 65536).map fun t => (rowFS h.gcl fs t).toUInt64 else #[],
    LamM := LamM }

/-! ## The lookup's numbers -/

/-- The rows of the table of a kind; none for a range table, whose row t has the value t.
C++: setTau. -/
def Lay.tauOf (y : Lay) (kind : String) : Option (Array F) :=
  if kind == "FC" then some y.tauFC
  else if kind == "FL" then some y.tauFL
  else if kind == "FS" then some y.tauFS
  else none

/-- The lookup's record of call number q. -/
def Lay.callRecord (y : Lay) (q : Nat) (cd : CallD) : Call :=
  let fn := cd.kind == "FC" || cd.kind == "FL" || cd.kind == "FS"
  { name := cd.name, n := y.h.ll + cd.lJ + y.h.lt, iota := y.h.iota.getD q 0, kappa := 5,
    k := if cd.kind == "R8" then 8 else 16, fn := if fn then 1 else 0,
    t0 := if fn then 32768 else 0, tau := y.tauOf cd.kind }

/-- The tests on the size of one call. -/
def Lay.callHeld (y : Lay) (cd : CallD) (c : Call) : Except String Unit := do
  -- The C++ verifier appends the call's name. Here a refusal's name holds no word of a file.
  let name := "shape-call"
  refuseIf (c.iota ≥ 2 ^ 31) name
  refuseIf (c.n < 10 || c.n < y.h.nmin || c.n > 44) name
  refuseIf (c.n < y.h.la || cd.lJ < y.ls) name

/-- Adds the padding keys of call number q to the count of each tree. A column (lam, j) lies in one
tree of its call. It counts if it holds padding on layer lam. -/
def Lay.pubOfCall (y : Lay) (fo : Forest.Shape) (q : Nat) (cd : CallD) (pub : Array Nat) :
    Except String (Array Nat) :=
  (List.range (y.Lam * cd.J)).foldlM
    (fun pub x =>
      if cd.padding (x / cd.J) (x % cd.J) then do
        let b := x / 2 ^ (fo.dT - y.h.lt)
        refuseIf (b / 2 ^ fo.iota.getD q 0 != 0) "internal-forest-pub"
        pure (pub.modify (fo.first.getD q 0 + b) (· + y.T))
      else pure pub)
    pub

/-- The second half of the layout: the calls' sizes, and the numbers of the one lookup that proves
all calls. -/
def layoutLook (y : Lay) : Except String Lay := do
  let h := y.h
  let cl := y.calls.mapIdx fun q cd => y.callRecord q cd
  (y.calls.zip cl).forM fun x => y.callHeld x.1 x.2
  let fo ← Forest.shape cl h.lidb
  refuseIf (fo.dT < h.la) "forest-depth-G"
  let kbm ← Forest.planeCols fo h.lmb
  (cl.zip fo.iota).forM fun x => refuseIf (x.1.iota != x.2) "shape-call"
  let pub ← (y.calls.toList.zipIdx).foldlM (fun pub x => y.pubOfCall fo x.2 x.1 pub)
    (Forest.noPub fo)
  Forest.pubAsk fo pub
  refuseIf ((List.range 8).any fun q => q ≥ y.calls.size && h.iota.getD q 0 != 0)
    "header-absent-call"
  pure { y with cl := cl, fo := { fo with pub := pub }, kbm := kbm }

/-- The layout of a layer sub-proof. pc: the lines "call" of the parameter file, each as its words
after "call". C++: layout. -/
def layout (h : Shape) (pc : List (List String)) : Except String Lay := do
  layoutLook (← layoutBase h pc)

/-- The rotary table of a layer with rotary embeddings, as words in the order in which its digest
takes them. A base of 0 is refused. The shape must have passed layout. -/
def ropeOf (h : Shape) : Except String (Array Nat) := do
  refuseIf (h.theta0 == 0) "shape-theta0"
  pure (ropeTable h.cs h.theta0 h.dh h.lt)

/-! ## Which tables of reads exist

A table of reads is not a lookup table. It belongs to one committed matrix and one point. Each of
its entries is the sum of a block of rows of one column, under public weights that follow from the
point (OnBytes/Model/LayerForms.lean). A block has 2^la rows in a long table, and T rows, that is
one feature, in a short table. The three tables of matrix b sum over all its rows. -/

/-- The matrices that the expression for a segment's keys (line in OnBytes/Model/LayerForms.lean)
reads at the lookup's point. Letters: f af, d ad, r ar, q qa, Q a short table of qa, i the stream
that comes in, o the stream that goes out. -/
def readsZ (p4 : Bool) (s : String) : List Char :=
  if ["G", "U", "V", "CN1", "CN2"].contains s then ['d', 'f']
  else if s == "O" then (if p4 then ['f', 'i', 'Q'] else ['f', 'i'])
  else if s == "D" then ['f', 'o']
  else if s == "XR" then ['d']
  else if s == "LR" then ['d', 'r']
  else if ["LT", "DD", "ROW", "LH", "SEL", "MR", "L3", "CLR"].contains s then ['r']
  else if s == "CQK" || s == "CV" then ['f', 'q']
  else ['f']

/-- The matrices that a segment's terms read at the end point of the second token sumcheck. An
empty list means that the segment has no such term. -/
def readsR (p3 : Bool) (s : String) : List Char :=
  if s == "N1" then ['r', 'f', 'i']
  else if s == "N2" then ['r', 'f']
  else if s == "QK" then ['d']
  else if p3 && ["G", "U", "XR"].contains s then ['r', 'd']
  else if p3 && ["D", "DD", "MR"].contains s then ['r']
  else []

/-- Which tables of reads a layer sub-proof has: for each matrix the names of the points at which
it is read, in the tables' order; the calls that have terms in the second token sumcheck; and the
numbers of variables of the three product layers. -/
structure Reads where
  /-- the names of the calls that have terms in the second token sumcheck -/
  tscCalls : List String := []
  /-- the points of the long tables of matrix af -/
  rdAF : List String := []
  /-- the points of the long tables of matrix qa -/
  rdQA : List String := []
  /-- the points of the long tables of the stream that comes in -/
  rdXI : List String := []
  /-- the points of the long tables of the stream that goes out -/
  rdXO : List String := []
  /-- the points of the short tables of matrix ad -/
  rdAD : List String := []
  /-- the points of the short tables of matrix ar -/
  rdAR : List String := []
  /-- the points of the short tables of matrix qa -/
  rdQS : List String := []
  /-- the logarithm of the number of norms of a group -/
  lNI : Nat := 0
  /-- the variables of the product layer of the squares -/
  muV : Nat := 0
  /-- the variables of the product layer of the gated products -/
  muH : Nat := 0
  /-- the variables of the product layer of the routed experts' gated products -/
  muH2 : Nat := 0
  /-- the entries of all tables together, in a group that is not the first; the first group has one
  table more (planG in OnBytes/Model/LayerPlan.lean) -/
  nW : Nat := 0
  deriving Repr, Inhabited

/-- The tables of reads for a layout. All calls share the lookup's point (named Z for long tables,
zt for short ones) and the end point of the second token sumcheck (Y, rt). A matrix has a table
at such a point if some segment reads it there (readsZ, readsR). The tables at the sub-proof's own
points are there in any case: af at Z_V, Z_a and, with routed experts, Z_b; the stream that comes in
at Z_V; ar at P_V and r_tV. Refuses under shape-product-layer if a product layer has fewer than 9
variables. -/
def readsOf (y : Lay) : Except String Reads := do
  let h := y.h
  let p3 := h.p3
  let zs := y.calls.toList.map fun c => c.segs.flatMap fun s => readsZ h.p4 s.name
  let rs := y.calls.toList.map fun c => c.segs.flatMap fun s => readsR p3 s.name
  let anyZ (c : Char) : Bool := zs.any (·.contains c)
  let anyR (c : Char) : Bool := rs.any (·.contains c)
  let long (c : Char) (zv zab : Bool) : List String :=
    (if anyZ c then ["Z"] else []) ++ (if zv then ["Z_V"] else []) ++
    (if anyR c then ["Y"] else []) ++
    (if zab then ["Z_a"] ++ (if p3 then ["Z_b"] else []) else [])
  let short (c : Char) (pv : Bool) : List String :=
    (if anyZ c then ["zt"] else []) ++ (if pv then ["P_V", "r_tV"] else []) ++
    (if anyR c then ["rt"] else [])
  let rdAF := long 'f' true true
  let rdQA := long 'q' false false
  let rdXI := long 'i' true false
  let rdXO := long 'o' false false
  let rdAD := short 'd' false
  let rdAR := short 'r' true
  let rdQS := short 'Q' false
  let lNI := ceilLog2 y.NI
  let muV := lNI + y.lPd + h.lt
  let muH := h.ll + y.lPf + h.lt
  let muH2 := h.ll - 1 + y.lfe + h.lt
  refuseIf (muV < 9 || muH < 9 || (p3 && muH2 < 9)) "shape-product-layer"
  let GSaf := y.filled.getD 0 0 * y.T / 2 ^ h.la
  let GSxb := y.xbFilled * y.T / 2 ^ h.la
  let GSqa := y.filled.getD 3 0 * y.T / 2 ^ h.la
  pure {
    tscCalls := ((y.calls.toList.zip rs).filter fun x => !x.2.isEmpty).map (·.1.name)
    rdAF := rdAF, rdQA := rdQA, rdXI := rdXI, rdXO := rdXO, rdAD := rdAD, rdAR := rdAR,
    rdQS := rdQS, lNI := lNI, muV := muV, muH := muH, muH2 := muH2,
    nW := rdAF.length * GSaf + rdQA.length * GSqa + (rdXI.length + rdXO.length) * GSxb +
      rdAD.length * y.filled.getD 1 0 + rdAR.length * y.filled.getD 2 0 +
      rdQS.length * y.filled.getD 3 0 + 3 * y.kbm }

/-! ## The quantization scales -/

/-- The file of quantization scales, as words, with what is needed to find a layer's record. -/
structure Scales where
  /-- the file's words -/
  KL : Array Nat
  /-- the words of a layer's record: 13 at profile 4, else 12 -/
  KW : Nat
  /-- the number of layers -/
  L : Nat
  deriving Inhabited

/-- The place in a layer's record of the shift of q. -/
def Lkq : Nat := 0
/-- The place in a layer's record of the shift of k. -/
def Lkk : Nat := 1
/-- The place in a layer's record of the shift of v. -/
def Lkv : Nat := 2
/-- The place in a layer's record of the shift of the attention output's product. -/
def Lko : Nat := 3
/-- The place in a layer's record of the gate's shift. -/
def Lkg : Nat := 4
/-- The place in a layer's record of the shift of the up product. -/
def Lku : Nat := 5
/-- The place in a layer's record of the shift of the down product. -/
def Lkd : Nat := 6
/-- The place in a layer's record of the exponent M of the first norm's reciprocal. -/
def LM1 : Nat := 7
/-- The place in a layer's record of the first norm's shift. -/
def LK1 : Nat := 8
/-- The place in a layer's record of the exponent M of the second norm's reciprocal. -/
def LM2 : Nat := 9
/-- The place in a layer's record of the second norm's shift. -/
def LK2 : Nat := 10

/-- Word i of the record of layer l. -/
def Scales.kl (s : Scales) (l i : Nat) : Nat := s.KL.getD (s.KW * l + i) 0

/-- Word i of the second record of layer l, which has routed experts: 0 the router's shift, 1 the
routed gate's, 2 the routed up product's. The second records, of three words each, come after the
records of all layers. -/
def Scales.klM (s : Scales) (l i : Nat) : Nat := s.KL.getD (s.KW * s.L + 3 * (l / 2) + i) 0

/-- The last word of the record of layer l: not 0 if the layer has rotary embeddings. -/
def Scales.klRp (s : Scales) (l : Nat) : Nat := s.KL.getD (s.KW * l + s.KW - 1) 0

/-- Word 11 of the record of layer l. At profile 4 it is the word sh. At profile 3 the record has
no sh, and word 11 is its last word (klRp). scalesHeld does not test sh. -/
def Scales.klSh (s : Scales) (l : Nat) : Nat := s.KL.getD (s.KW * l + 11) 0

/-- The scales for a shape. Refuses a file whose length is not the one that the shape asks for. -/
def scalesOf (h : Shape) (KL : Array Nat) : Except String Scales := do
  let KW := if h.p4 then 13 else 12
  refuseIf (KL.size != KW * h.L + 3 * (if h.p3 then h.L / 2 else 0)) "KL-length"
  pure ⟨KL, KW, h.L⟩

/-- True if layer l, counted over the whole model, has routed experts. -/
def Shape.isMoeL (h : Shape) (l : Nat) : Bool := h.p3 && l % 2 == 1

/-- Tests a shift against the range of its digit form. C++: rng in runStage. -/
def shiftHeld (k form : Nat) : Except String Unit :=
  refuseIf (k < 1 || k > (if form == 0 then 16 else if form == 1 then 24 else 32)) "KL-shift-range"

/-- The tests on the record of layer l. -/
def scalesHeldAt (h : Shape) (s : Scales) (l : Nat) : Except String Unit := do
  shiftHeld (s.kl l Lkg) h.hgD
  shiftHeld (s.kl l Lku) h.huD
  shiftHeld (s.kl l Lkd) h.hdD
  shiftHeld (s.kl l Lkq) h.hq
  shiftHeld (s.kl l Lkk) h.hq
  shiftHeld (s.kl l Lkv) h.hv
  shiftHeld (s.kl l Lko) h.ho
  refuseIf (s.kl l Lkq != s.kl l Lkk && (s.kl l Lkq < 16 || s.kl l Lkk < 16)) "KL-kq-kk"
  for (M, K) in [(s.kl l LM1, s.kl l LK1), (s.kl l LM2, s.kl l LK2)] do
    refuseIf (M < 24 || M > 47 || K + 14 < M || K < 17 || K > 32) "KL-norm"
  refuseIf (s.klRp l > 1) "KL-rp"
  if h.isMoeL l then
    shiftHeld (s.klM l 0) h.hr
    shiftHeld (s.klM l 1) h.hgD
    shiftHeld (s.klM l 2) h.huD

/-- The tests on the words of the file of scales, layer by layer. -/
def scalesHeld (h : Shape) (s : Scales) : Except String Unit :=
  (List.range h.L).forM (scalesHeldAt h s)

/-! ## No sum wraps around -/

/-- The width of a weight, in bits. C++: WEIGHT_WIDTH_BITS. -/
def WB : Nat := 13
/-- The bound on a weight. C++: WEIGHT_BOUND. -/
def BW : Nat := 2 ^ (WB - 1)
/-- The largest value that smax can have. noWrapAt bounds table SILU by it, whatever smax is.
C++: SMAXTOP. -/
def SMAXTOP : Nat := 4095
/-- The logarithm of the bound on the up product. C++: LBU. -/
def LBU : Nat := 15

/-- Refuses under no-wrap- followed by n unless ok is true. -/
def need (ok : Bool) (n : String) : Except String Unit := refuseIf (!ok) ("no-wrap-" ++ n)

/-- The two conditions of a rounding site. U-n: the span times 2^max(k, 16) is at most 2^60, which
is below the prime, so the site's relation fixes one quotient within the span. W-n: the relation
does not wrap around. n: the site's name; k: its shift; form: its digit form; A: the bound on the
accumulator; SP: the span of the quotient; Qb: the bound on the quotient; Ty: the bound on a
committed cell.
C++: site in q9. -/
def noWrapSite (Ty : Nat) (n : String) (k form A SP Qb : Nat) : Except String Unit := do
  let P2 := 2 ^ 60
  let t := 16 - k
  need (SP * 2 ^ (max k 16) ≤ P2) ("U-" ++ n)
  need ((A + 2 ^ (k - 1) + Qb * 2 ^ k) * 2 ^ t +
      (if form == 1 then 2 ^ 16 * (Ty + 128)
       else if form == 2 then 2 ^ 16 * (Ty * 257 + 32896) else 0) < P2) ("W-" ++ n)

/-- The conditions that depend on layer l. acc bounds a sum of d products of a clamped value and a
weight. By the C++ comment a value of the residual stream is below 2^lsg in absolute value, given
what a norm's row of digits shows. -/
def noWrapAt (h : Shape) (s : Scales) (dq Ty l : Nat) : Except String Unit := do
  let P2 := 2 ^ 60
  let Ty2 := Ty * 257
  let acc := h.d * clampBound * BW
  let lsg := if h.xl == 5 then 39 else 30
  let mo := h.isMoeL l
  let site := noWrapSite Ty
  let gQ := if h.gcl then 128 + 2 ^ 22 else 2 ^ 15
  let gSP := if h.gcl then 2 * gQ + 1 else 2 ^ 16
  site "gate" (s.kl l Lkg) h.hgD acc gSP gQ
  if mo then site "gate" (s.klM l 1) h.hgD acc gSP gQ
  site "up" (s.kl l Lku) h.huD acc (2 ^ 16) (2 ^ 15)
  if mo then site "up" (s.klM l 2) h.huD acc (2 ^ 16) (2 ^ 15)
  site "norm" (s.kl l LK1) 2 (2 ^ s.kl l LM1 + 2 ^ (lsg - 1)) (2 ^ 16) (2 ^ 15)
  site "norm" (s.kl l LK2) 2 (2 ^ s.kl l LM2 + 2 ^ (lsg - 1)) (2 ^ 16) (2 ^ 15)
  site "down" (s.kl l Lkd) h.hdD (h.f * (SMAXTOP + 1) * 2 ^ LBU * BW) (2 ^ (lsg + 2))
    (2 ^ (lsg + 1))
  site "qk" (s.kl l Lkq) h.hq (2 * 2 ^ h.cs * acc) (2 ^ 16) (2 ^ 15)
  site "qk" (s.kl l Lkk) h.hq (2 * 2 ^ h.cs * acc) (2 ^ 16) (2 ^ 15)
  site "o" (s.kl l Lko) h.ho (dq * clampBound * BW) (2 ^ (lsg + 2)) (2 ^ (lsg + 1))
  site "v" (s.kl l Lkv) h.hv acc (2 ^ 16) (2 ^ 15)
  if mo then
    site "lr" (s.klM l 0) h.hr acc (if h.rcl then 16 * Ty2 + 15 else 2 ^ 15)
      (if h.rcl then 8 * Ty2 + 7 else 2 ^ 14)
  if mo && h.rcl then
    need ((acc + 2 ^ (s.klM l 0 - 1)) / 2 ^ (s.klM l 0 + 3) + 1 + 2 ^ 15 + 2 ^ 16 < 2 ^ 25)
      "guard-radix-clamp"
    need (32 * Ty < P2 && (Ty2 + 2 ^ 15) + 2 ^ 25 * (Ty2 + Ty) + 2 ^ 39 < P2) "clamp-keys"

/-- The conditions under which no sum of a layer sub-proof wraps around in the field. They are
computed in natural numbers, and each bound is at most 2^60, which is below half the prime. Ty: the
bound on a committed cell that the smallness test gives. Ty2 and Ty3 bound a value of two and of
three limbs (257 = 1 + 256, 65793 = 1 + 256 + 256^2). The comments of the C++ routine give the
reason for most conditions. The shifts must have passed scalesHeld: the conditions take every shift
to be at least 1 (2^(k - 1)). C++: q9 in runStage. -/
def noWrapWith (h : Shape) (s : Scales) (dq Ty : Nat) : Except String Unit := do
  let P2 := 2 ^ 60
  let Ty2 := Ty * 257
  let Ty3 := Ty * 65793
  (List.range h.L).forM (noWrapAt h s dq Ty)
  if h.p3 then
    need ((2 * Ty2 + 1) * 2 ^ 16 ≤ P2) "U-xr"
    need (2 ^ 16 * clampBound + 2 ^ 15 + 2 ^ 16 * Ty2 < P2) "W-xr"
    need (2 ^ 15 + 2 ^ 14 + 2 ^ 17 * Ty3 < P2 / 2) "guard-radix-FS"
    if h.gcl then
      need ((Ty2 + 49152) + (Ty + 128) * 2 ^ 28 + 2 ^ 40 < P2 / 2 && Ty2 + 49152 + 65536 < 2 ^ 28)
        "guard-radix-gate-clamp"
      need (2 ^ 40 + 49152 > Ty2 + 32767 + 2 ^ 16 * 2 ^ 17) "guard-flag-gate-clamp"
    need (h.NE * Ty * Ty2 + Ty2 + h.NE * Ty < P2) "MR"
    need (h.NE * Ty + 1 < P2) "one-hot"
  need (2 ^ 16 * (Ty2 + 32896) < P2) "linear"
  need ((Ty2 + 32768) + (Ty2 + 4096) * 2 ^ 28 < P2 / 2 && Ty2 + 32768 + 65536 < 2 ^ 28)
    "guard-radix"
  need (h.xl * h.d * Ty * Ty < 2 ^ 53) "ledger"
  if h.xl == 5 then
    need (h.eps1 < 2 ^ 48) "ledger-eps"
    need (h.eps2 < 2 ^ 48) "ledger-eps"
    need (h.epsF < 2 ^ 48) "ledger-eps"

/-- noWrapWith at the bound that the smallness test gives for a request's data. -/
def noWrap (h : Shape) (s : Scales) (dq : Nat) : Except String Unit :=
  noWrapWith h s dq (2 ^ (1 + lbz))

/-- Tests the twelve widths of weights: that of a kind that is present is WB, that of an absent
kind is 0. -/
def weightWidthsHeld (h : Shape) (kinds : List KindD) : Except String Unit :=
  (List.range 12).forM fun k =>
    if kinds.any fun x => x.idx == k then refuseIf (h.wb.getD k 0 != WB) "policy-weight-kind"
    else refuseIf (h.wb.getD k 0 != 0) "header-absent-kind"

/-! ## The names of the refusals -/

/-- The names of the conditions of noWrap, without their common beginning. -/
def noWrapNames : List String :=
  (["gate", "up", "norm", "down", "qk", "o", "v", "lr", "xr"].flatMap fun n =>
    ["U-" ++ n, "W-" ++ n]) ++
  ["guard-radix-clamp", "clamp-keys", "guard-radix-FS", "guard-radix-gate-clamp",
   "guard-flag-gate-clamp", "MR", "one-hot", "linear", "guard-radix", "ledger", "ledger-eps"]

/-- All names under which the functions of this file refuse. tensorsFill is listed with the two
words that layoutBase passes to it. The functions of OnBytes/Model/Forest.lean that layoutLook calls
(shape, planeCols, pubAsk) have names of their own: Forest.names. verifier/docs/parameter-file.md
says what most of the names mean. -/
def layoutNames : List String :=
  ["plan-tensor-layout", "plan-tensor-layout-fill-stream", "plan-tensor-layout-fill-qa",
   "policy-call-list", "policy-profile", "shape-words", "shape-L", "shape-groups",
   "plan-groups-base", "shape-la", "policy-norm", "shape-heads", "policy-cs", "policy-forms",
   "header-absent-class", "policy-ut", "shape-D", "internal-layout-words", "shape-NE", "policy-gcl",
   "policy-rcl", "shape-request-matrix", "shape-lmb", "shape-call", "forest-depth-G",
   "internal-forest-pub", "header-absent-call", "shape-theta0", "shape-product-layer", "KL-length",
   "KL-shift-range", "KL-kq-kk", "KL-norm", "KL-rp", "policy-weight-kind", "header-absent-kind"] ++
  noWrapNames.map ("no-wrap-" ++ ·)

end OnBytes.Model.Layer
