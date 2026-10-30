-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Frame.lean: helper functions, records and constants that the checks of all of the
model's sub-proofs share.

A request's proof is meant to show that the model's integer arithmetic was carried out on the
request. It is made of sub-proofs: for groups of layers, for their attention, and for the output
head. The C++ verifier keeps most of their shared helpers in verifier/src/vf_common.h, and the list
of a smallness test's matrices in verifier/src/vf_smallness_matrices.h. The part on integers gives
the Lean names of the C++ field helpers.

Terms. OnBytes/Iop/Ground.lean explains Blk, dry run and view. A lookup call is meant to show that
every key of a list is a row value of a public table; the part on one lookup call explains forest,
product tree and multiplicity. The smallness test is the last part of every sub-proof: random
combinations of the committed columns, meant to show that every committed value is small. A refusal
is a rejection under a name. Three words have several meanings. Frame: this file;
the first 32 lines of the parameter file (the frame's lines, OnBytes/Params/File.lean); the record
ReqFrame (OnBytes/Iop/Req.lean). Call: a lookup call (Call); a line call of the parameter file; a
run of the verifier. tau: the row values of a lookup table (Call.tau); the line tau, the number of
combinations of the smallness test (Settings.tau).

Main definitions: refuse, mustAs, testAs, refuseIf, fOfNat, fOfInt, ofNat, ofInt, scaleNat, powers,
roundUp, clog2, mix64, eqTab, eqOne, orderDefault, orderRange, Call, TMat, Tail, Settings,
tauServed.

No theorem is stated here. Two rules are not enforced by Lean: see eqIndexOK and orderRange.
-/
import OnBytes.Iop.Ground

namespace OnBytes.Model

/-! ## Refusals -/

/-- Fails at once under the name, which the failure carries out of the run (Blk.fail). The name is
the one that the C++ verifier gives the same rejection. -/
def refuse {α : Type} (name : String) : Blk α := Blk.fail name

/-- Fails under the name unless b is true, in the dry run and on a view. It is for conditions on
public numbers. -/
def mustAs (name : String) (b : Bool) : Blk Unit :=
  if b then pure () else refuse name

/-- Fails under the name unless b is true. It is for conditions on received or drawn values, so the
dry run, in which every value is 0, skips it. -/
def testAs (name : String) (b : Bool) : Blk Unit := do
  if b || (← Blk.isDry) then pure () else refuse name

/-- Returns the name as an error if b is true. It is for functions of public numbers that are not
written in Blk; they return the name of the first test that failed. -/
def refuseIf (b : Bool) (name : String) : Except String Unit :=
  if b then .error name else .ok ()

/-! ## Integers as elements of the field

The field. The C++ type Ex is E. Its helpers are functions of OnBytes/Field/Ext.lean: eZ() is
zeroE, eO() is oneE, eInv is invE, ePow is powE, isZ is isZeroE, and the operators +, - and * are
addE, subE and mulE. ofNat, ofInt and scaleNat, below, replace eB, eI and eS. -/

/-- The residue of a natural number in the base field. -/
def fOfNat (v : Nat) : F := (v % pW.toNat).toUInt64

/-- The residue of an integer in the base field. -/
def fOfInt (v : Int) : F :=
  let r := v.natAbs % pW.toNat
  if v < 0 ∧ r ≠ 0 then (pW.toNat - r).toUInt64 else r.toUInt64

/-- A natural number as an element of the extension field. It is reduced. The C++ helper eB takes
a word that its caller knows to be below the prime, and does not reduce. -/
def ofNat (v : Nat) : E := ofF (fOfNat v)

/-- An integer as an element of the extension field. -/
def ofInt (v : Int) : E := ofF (fOfInt v)

/-- x times a natural number. -/
def scaleNat (x : E) (v : Nat) : E := scaleE (fOfNat v) x

/-- Appends c, c x, c x^2 and so on to a, n elements in all. -/
def powersLoop (x : E) : Nat → E → Array E → Array E
  | 0, _, a => a
  | n + 1, c, a => powersLoop x n (mulE c x) (a.push c)

/-- The n powers 1, x, x^2 and so on. -/
def powers (x : E) (n : Nat) : Array E := powersLoop x n oneE (Array.emptyWithCapacity n)

/-- x rounded up to a multiple of w. -/
def roundUp (x w : Nat) : Nat := (x + w - 1) / w * w

/-- The least l with v ≤ 2^l. -/
abbrev clog2 (v : Nat) : Nat := ceilLog2 v

/-- The SplitMix64 mixer, in 64-bit arithmetic that wraps around. It is no cryptographic hash. It
has one use outside tests: below profile 4 it makes the public numbers that take the place of
attention's outputs (stubO, OnBytes/Model/Layer.lean). -/
def mix64 (z : UInt64) : UInt64 :=
  let a := z + 0x9E3779B97F4A7C15
  let b := (a ^^^ (a >>> 30)) * 0xBF58476D1CE4E5B9
  let c := (b ^^^ (b >>> 27)) * 0x94D049BB133111EB
  c ^^^ (c >>> 31)

/-! ## The equality polynomial -/

/-- One more coordinate: every entry a of the table becomes the two entries a (1 - zv) and a zv. -/
def eqTabStep (t : Array E) (zv : E) : Array E :=
  t.foldl (fun n a =>
    let hi := mulE a zv
    (n.push (subE a hi)).push hi) (Array.emptyWithCapacity (2 * t.size))

/-- The values eq(z, c) for all c below 2^len, where len is the number of coordinates of z.
Coordinate 0 belongs to the top bit of c. eq(z, c) is a product with one factor for each coordinate
zv of z: zv if the coordinate's bit of c is 1, and 1 - zv if it is 0. -/
def eqTab (z : Array E) : Array E := z.foldl eqTabStep #[oneE]

/-- True if c < 2^len and z has at most 63 coordinates, where len is their number. Otherwise the C++
routine for a single entry (eqOne, verifier/src/vf_common.h) refuses as internal-eq-index. A caller
of eqOne should test this first and fail where it is false, unless its code makes it plain that
c < 2^len. Lean does not enforce this. -/
def eqIndexOK (z : Array E) (c : Nat) : Bool := decide (z.size ≤ 63) && decide (c < 2 ^ z.size)

/-- The value eq(z, c): entry c of eqTab z, by the same products in the same order, without the
table. It is 0 where eqIndexOK is false. -/
def eqOne (z : Array E) (c : Nat) : E :=
  if eqIndexOK z c then
    (z.foldl (fun (s : E × Nat) zv =>
      let hi := mulE s.1 zv
      (if c.testBit (s.2 - 1) then hi else subE s.1 hi, s.2 - 1)) (oneE, z.size)).1
  else zeroE

/-! ## Orders of variables -/

/-- The variables from mu - 1 down to 0: the order in which most levels of a product tree are
summed. -/
def orderDefault (mu : Nat) : List Nat := (List.range mu).reverse

/-- The order 2, 1, 0, 5, 4, 3, 8, 7, 6, then mu - 1 down to 9: the lowest nine variables in three
groups of three, then the others from the top down. It is meant for mu ≥ 9, which is not tested
here; its caller is the layer sub-proof (OnBytes/Model/Layer.lean). -/
def orderRange (mu : Nat) : List Nat :=
  [2, 1, 0, 5, 4, 3, 8, 7, 6] ++ ((List.range (mu - 9)).reverse.map (· + 9))

/-! ## One lookup call

The keys of a sub-proof's calls are cut into trees of one size, together called a forest
(OnBytes/Model/Forest.lean). The lookup forms products over the keys and over the table's rows level
by level, in product trees (OnBytes/Model/Look.lean). A multiplicity, or count, is the number of a
call's keys, padding not counted, that hit one row of its table. -/

/-- One call of the lookup argument: every key of a vector of keys is a row value of a public table.
The record holds what the sub-proof that makes the call (its host) fixes. What a run adds (the
challenge, the point at which the keys are claimed) has fields in the C++ record; here the lookup
returns it. -/
structure Call where
  /-- the call's name, which appears in the names of refusals -/
  name : String := ""
  /-- the call has 2^n keys, padding counted -/
  n : Nat := 0
  /-- the call's keys are split into 2^iota trees -/
  iota : Nat := 0
  /-- the table has 2^k rows -/
  k : Nat := 0
  /-- a multiplicity has 2^kappa bits -/
  kappa : Nat := 0
  /-- a flag that the host sets together with the table, from the kind of the call: 0 where row t
  has the value t, 1 or 2 with an explicit table (tau). No formula reads it. The checks only
  compare it: at most 2 in every call, 0 in the two calls of the smallness test -/
  fn : Nat := 0
  /-- the table row that padding keys point to -/
  t0 : Nat := 0
  /-- the public row values; none: row t has the value t -/
  tau : Option (Array UInt64) := none
  /-- for each tree the number of its padding keys -/
  pub : Array Nat := #[]
  /-- for each tree the rows with counts of their own, as pairs of a row and its count. callAsk
  (OnBytes/Model/Forest.lean) refuses a call in which this list is not empty -/
  heavy : List (List (Nat × Nat)) := []
  deriving Inhabited

namespace Call

/-- The value of row t. A row beyond an explicit table has the value 0; the lookup refuses an
explicit table whose length is not 2^k before it reads a row. -/
def tauAt (c : Call) (t : Nat) : UInt64 :=
  match c.tau with
  | none => t.toUInt64
  | some a => a.getD t 0

end Call

/-! ## The matrices of a sub-proof's smallness test -/

/-- One matrix of a sub-proof's smallness test. -/
structure TMat where
  /-- the matrix's name -/
  name : String := ""
  /-- the number of its rows -/
  m : Nat := 0
  /-- the number of its columns -/
  k : Nat := 0
  /-- 0: this sub-proof commits to it; 1: an earlier sub-proof has committed to it. shapeF
  (OnBytes/Model/Tail.lean) refuses every other value -/
  kind : Nat := 0
  /-- for kind 1: its index in the sub-proof's list of the matrices of earlier sub-proofs -/
  foreign : Option Nat := none
  /-- for kind 1: its first column in the owner's array. shapeF (OnBytes/Model/Tail.lean) refuses a
  value other than 0 -/
  ttOff : Nat := 0
  /-- 256 times the owning sub-proof's number, plus the matrix's index there -/
  aId : Nat := 0
  /-- the parameter w of the matrix's symbol array (OnBytes/Model/FormF.lean; the C++ says symbol
  tree). No line of the parameter file sets it, so it is always 0 -/
  wp : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The matrices of one sub-proof's smallness test. The name is the C++ record's; it is not the tail
of a code word. -/
structure Tail where
  /-- the matrices, in the sub-proof's order -/
  mats : Array TMat := #[]
  deriving DecidableEq, Repr, Inhabited

/-- The number of columns of all matrices together. -/
def Tail.foldColumns (t : Tail) : Nat := t.mats.foldl (fun s M => s + M.k) 0

/-! ## Constants of the format and numbers of a run -/

/-- A random combination of the smallness test must lie from -2^lbz to 2^lbz - 1
(OnBytes/Model/Tail.lean). In the C++ of this test the word fold, as in foldColumns and the fold
list, refers to these combinations. -/
def lbz : Nat := 17

/-- The output head's test against overflow (no-wrap-H-J-E, OnBytes/Model/HeadLayout.lean) assumes
that each limb of an entry of the embedding, that is each of its digits in base 256, is below
2^(lbzw + 1) in absolute value. A request's proof does not show that. The key's proof of the ranges
shows more: each limb is a signed byte (verifier/docs/parameter-file.md). -/
def lbzw : Nat := 20

/-- log2 of the most keys in one tree of a lookup forest if the parameter file has no line
lidb. -/
def lidbSealed : Nat := 22

/-- The largest value of the line lidb. It must stay below 32: a count is a number of 32 bits, so
already a single tree must have fewer than 2^32 keys. Forest.shape (OnBytes/Model/Forest.lean) tests
more: all trees of a forest together have fewer than 2^32 keys (forest-keys). -/
def lidbMost : Nat := 30

/-- The largest value of the line nminH. -/
def nminHMost : Nat := 28

/-- The most bits of proof of work that this verifier accepts before a verifier's message, for each
kind of work. -/
def workMost : Nat := 32

/-- The fewest requested bits of security with which a run of the verifier can end in an
acceptance. A run that asks for fewer is no verification, whatever it finds. -/
def bar : Nat := 128

/-- Doubles its last argument while the double is at most tau. The first argument bounds the number
of doublings. -/
def tauFirst : Nat → Nat → Nat → Nat
  | 0, _, first => first
  | fuel + 1, tau, first => if 2 * first ≤ tau then tauFirst fuel tau (2 * first) else first

/-- Which values the line tau may have: 32, 64, 96, 128, 160, 192 and 256. These are the multiples
of 32 up to 256 that are a power of two or the sum of two powers of two. -/
def tauServed (tau : Nat) : Bool :=
  if tau < 32 ∨ tau > 256 ∨ tau % 32 ≠ 0 then false
  else
    let rest := tau - tauFirst 8 tau 32
    rest &&& (rest - 1) == 0

/-- The numbers that lines of the parameter file set for a run and that the sub-proofs read. In
the C++ verifier they are the variables LIDB, NMINH, TAU, POW, POWS, POWC and
statedTarget.hb. -/
structure Settings where
  /-- log2 of the most keys in one tree of a lookup forest: the line lidb -/
  lidb : Nat := lidbSealed
  /-- log2 of the fewest keys of a call of the output head; 0: the line nminH is absent, and the
  line nmin holds for the head too (keyFloor, OnBytes/Model/HeadLayout.lean) -/
  nminH : Nat := 0
  /-- the number of random combinations of the smallness test: the line tau -/
  tau : Nat := 160
  /-- the bits of proof of work before a draw of positions in a request's own rounds -/
  pow : Nat := 0
  /-- the bits of proof of work before a draw of positions in a batch's shared rounds -/
  powS : Nat := 0
  /-- the bits of proof of work before a draw of positions in the committer's rounds -/
  powC : Nat := 0
  /-- the security target in bits: the line sec of the parameter file. hb is the C++ verifier's name
  for the word that holds it in its statement, the list of 32-bit words of its public inputs -/
  hb : Nat := 0
  deriving DecidableEq, Repr, Inhabited

end OnBytes.Model
