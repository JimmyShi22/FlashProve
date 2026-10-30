-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLook.lean: the order of a lookup's rounds, tested against the plan.

The C++ programs describe the rounds of a lookup twice. Their verifier receives and draws in the
order of its source (verifier/src/vf_lookup_argument.h), and their planner lists the rounds
beforehand (plan_lookup in blocks/numbers/blocks.h). This file writes out the planner's list,
lookupEntries, and makes a dry run of Forest.pad (OnBytes/Model/Look.lean) against it. The list is
typed in this file. It follows plan_lookup for 32 planes, all keys in one part, and the setting in
which one coefficient of each round polynomial is not sent. No guard compares it with what the C++
planner prints or with Params.planForest (OnBytes/Params/SubRounds.lean). The program does not
import this file.

What is tested when the file compiles. Each section below begins with its own account.
 1. The dry run goes through.
 2. It does not go through against another list.
 3. The claims and the list of owed claims.
 4. The weights on the rows of the planes' matrix.
 5. The public polynomials at points of 0 and 1.
 6. Wrong public numbers and a caller's faults.
 7. Equality weights over a stretch of bits.
 8. The weights of the claim on the key vectors.

Under 3 no guard compares the name of a refusal: a guard sees only that the dry run fails. A dry run
holds no value of a proof. Apart from the constant under 8, nothing here tests the arithmetic of a
claim; OnBytes/Model/TestLookHonest.lean and its three neighbours do. No guard tries the conditions
internal-forest-point, internal-slot-count and internal-forest-place of Forest.pad.
-/
import OnBytes.Model.Look

namespace OnBytes.Model.Forest.Test

/-- An entry of a plan: the prover sends sent elements of E, and the verifier draws drawn elements,
of which notZero must not be 0. -/
def entry (name : String) (sent drawn : Nat) (notZero : Nat := 0) : Fmt.Entry :=
  { name := name, msg := 24 * sent, drawE := drawn, drawNZ := notZero }

/-- The rounds of a sumcheck, as the planner lists them. coefficients: for each variable the number
of coefficients of its round polynomial; one of them is not sent. ends: none if no value is
shown, else the degree in the further variable and the number of end values. -/
def pscEntries (coefficients : List Nat) (ends : Option (Nat × Nat)) : List Fmt.Entry :=
  [entry "PSC epsilon" 1 1] ++ coefficients.map (fun d => entry "PSC round" (d - 1) 1) ++
    match ends with
    | none => []
    | some (degreeY, values) => [entry "PSC Y" degreeY 1 1, entry "PSC values" values 0]

/-- The levels of a product tree from the root down: level l has l + more variables. -/
def treeEntries (levels more : Nat) : List Fmt.Entry :=
  (List.range levels).flatMap fun l =>
    pscEntries (List.replicate (l + more) 3) (some (2, 2)) ++ [entry "LINE" 0 1]

/-- The rounds of a lookup with 2^v keys, a table of 2^d rows and 32 planes. -/
def lookupEntries (v d : Nat) (shifted : Bool) : List Fmt.Entry :=
  (if shifted then [entry "LKP shift" 0 1] else []) ++ [entry "LKP" 0 1] ++
    pscEntries [] (some (3, 3)) ++
    (List.range 30).flatMap (fun _ => pscEntries [] (some (3, 2))) ++
    [entry "JOIN" 0 5] ++ treeEntries v 0 ++ treeEntries d 5 ++
    pscEntries (List.replicate d 3 ++ List.replicate 5 2) none ++
    [entry "ZERO" 0 (5 + d)] ++ pscEntries (List.replicate (5 + d) 3) (some (2, 1))

/-- A group of calls with the given n and k, each with the range table (row t has the value t). -/
def calls (n k : List Nat) : Array Call :=
  ((n.zip k).map fun x => { name := "c", n := x.1, k := x.2, kappa := 5 : Call }).toArray

/-- The dry run of an action of a sub-proof that has the given number of slots, against a list of
entries. True if it goes through and each round receives as many bytes as its entry says. -/
def dryHolds {α : Type} (x : SubM α) (slots : Nat) (entries : List Fmt.Entry) : Bool :=
  match Blk.rounds (StateT.run x (({} : Fork).slots slots)) { entries := entries, st := {} } with
  | none => false
  | some rounds => rounds.all fun r => (r.1.items.map Fmt.Item.bytes).sum == r.1.entry.msg

/-- The dry run of the messages of a lookup without padding, against a list of entries. -/
def padHolds (lid : Nat) (n k : List Nat) (entries : List Fmt.Entry) : Bool :=
  match shape (calls n k) lid with
  | .error _ => false
  | .ok h => dryHolds (pad (calls n k) (noPub h) lid) (elems h) entries

/-- The messages of a lookup, then all its claims, with made-up forms for what the sub-proof
reads from its arrays, then the end of the sub-proof. without says what is left out: 0 nothing, 1
the claim on the key vectors, 2 the claims that read only mask entries, 3 the mark that the three
plane claims, which are added, are added. -/
def padAndClaims (lid lm : Nat) (n k : List Nat) (without : Nat) : SubM Unit := do
  let h ← SubM.get (shape (calls n k) lid).toOption
  let g ← pad (calls n k) (noPub h) lid
  SubM.change (·.batchBy oneE)
  if without != 2 then objects g
  if without == 3 then
    (← planeClaims g lm (fun _ _ => pure (Aff.ofConst zeroE))
      (fun _ => pure (Aff.ofConst zeroE))).forM SubM.lin
  else planeLins g lm (fun _ _ => pure (Aff.ofConst zeroE)) (fun _ => pure (Aff.ofConst zeroE))
  if without != 1 then SubM.lin (← join g (Array.replicate h.NC (Aff.ofConst zeroE)))
  SubM.must ((← SubM.claims) ==
    (if without == 2 then 0 else lins h) + 3 + (if without == 1 then 0 else 1))
  let _ ← SubM.settle (elems h)

/-- The dry run of the messages of a lookup with the given numbers of padding keys. -/
def padWith (lid : Nat) (n k : List Nat) (pub : Array Nat) (entries : List Fmt.Entry) : Bool :=
  match shape (calls n k) lid with
  | .error _ => false
  | .ok h => dryHolds (pad (calls n k) pub lid) (elems h) entries

/-- The messages of a lookup without padding, and then an action on what they leave. -/
def padThen (lid : Nat) (n k : List Nat) (next : Shape → Heard → SubM Unit) : SubM Unit := do
  let h ← SubM.get (shape (calls n k) lid).toOption
  let g ← pad (calls n k) (noPub h) lid
  next h g

/-- True if uEnt t x goes through in a sub-proof with the given arrays. -/
def entHolds (trees : Array HTree) (t x : Nat) : Bool :=
  (Blk.rounds (StateT.run (uEnt t x) { trees := trees }) { entries := [], st := {} }).isSome

/-- The name under which the dry run of an action fails, from the state F and against a list of
entries; the empty string if it goes through. -/
def dryName {α : Type} (x : SubM α) (F : Fork) (entries : List Fmt.Entry) : String :=
  match Blk.dryRunNamed (StateT.run x F) { entries := entries, st := {} } with
  | .error e => e.name
  | .ok _ => ""

/-- The name under which the dry run of the messages of a lookup without padding fails against a
list of entries; the empty string if it goes through. -/
def padName (lid : Nat) (n k : List Nat) (entries : List Fmt.Entry) : String :=
  match shape (calls n k) lid with
  | .error e => e
  | .ok h => dryName (pad (calls n k) (noPub h) lid) (({} : Fork).slots (elems h)) entries

/-- The array, the virtual row and the column that uEnt t x names in a sub-proof with the given
arrays; none if it refuses. -/
def entOf (trees : Array HTree) (t x : Nat) : Option (List (Nat × Nat × Nat)) :=
  match Blk.dryRunNamed (StateT.run (uEnt t x) { trees := trees }) { entries := [], st := {} } with
  | .ok y => some (y.2.1.ents.toList.map fun e => (e.tree, e.row, e.idx))
  | .error _ => none

/-- The 32 numbers of the line PHIP lm=5 of verifier/tests/forest_weights.txt. -/
def powers32 : Array E :=
  #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
    262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728,
    268435456, 536870912, 1073741824, 2147483648].map ofF

/-- The number x as a point of count coordinates 0 and 1, the top bit's first. -/
def bitsOf (count x : Nat) : Array E :=
  (Array.range count).map fun i => if x.testBit (count - 1 - i) then oneE else zeroE

/-- What a lookup of two calls with kT = 6 and cK = 1 leaves, as far as phiB reads it. The first
point is (t | c | j) = (38 | 1 | 13), the second (5 | 0 | 30). -/
def twoPoints : Heard :=
  { shape := (shape (calls [10, 11] [5, 6]) 10).toOption.getD {}, leaves := {},
    zb0 := bitsOf 12 ((38 * 2 + 1) * 32 + 13), zb1 := bitsOf 12 ((5 * 2 + 0) * 32 + 30) }

/-- Four calls with five trees: the first has two. Its padding row is row 9. -/
def fiveTrees : Shape :=
  (shape ((calls [11, 10, 10, 10] [5, 5, 5, 5]).modify 0 fun k => { k with t0 := 9 })
    10).toOption.getD {}

/-- The constant of the claim on the key vectors, with all key forms 0 and 0 at the end of the key
side, where the point zy is the number y of a tree. -/
def joinAt (h : Shape) (theta alpha : E) (y : Nat) : Option E :=
  let zy := bitsOf h.rK y
  let g : Heard :=
    { shape := h, theta := theta, alpha := alpha, leaves := {}, zy := zy,
      e := (Array.range h.NC).map (callWeight h zy) }
  match Blk.dryRunNamed (StateT.run (join g (Array.replicate h.NC (Aff.ofConst zeroE))) {})
      { entries := [], st := {} } with
  | .ok x => some x.2.1.const
  | .error _ => none

/-- True if each call's weight at each tree number says whether the tree is the call's. -/
def weightsHold (lid : Nat) (n k : List Nat) : Bool :=
  match shape (calls n k) lid with
  | .error _ => false
  | .ok h =>
    (List.range (2 ^ h.rK)).all fun y => (List.range h.NC).all fun c =>
      callWeight h (bitsOf h.rK y) c ==
        if y < h.NT && h.callOf.getD y 0 == c then oneE else zeroE

/-- A written table of 2^5 rows. -/
def written : Call :=
  { name := "w", n := 10, k := 5, kappa := 5, fn := 1,
    tau := some ((Array.range 32).map fun t => (1000 + 7 * t).toUInt64) }

/-- Three calls. A call's number has two bits here, so the number 3 belongs to no call. -/
def three : Shape := (shape (calls [10, 10, 10] [5, 6, 5]) 10).toOption.getD {}

/-! ## 1. The dry run goes through

At four groups of calls the dry run of Forest.pad goes through: it closes the rounds of the list
typed above (lookupEntries; no guard compares it with what the C++ planner prints), in their order
and under their names, with the listed numbers of draws, and in each round it receives as many
bytes as the list says. It also takes as many slots and leaves as many claims as Forest.elems and
Forest.lins say (Forest.pad tests that itself).
-/

#guard padHolds 10 [10] [5] (lookupEntries 10 5 false)
#guard padHolds 10 [10, 11] [5, 6] (lookupEntries 12 7 true)
#guard padHolds 22 [13, 12, 13, 12, 12, 12] [16, 16, 8, 16, 16, 16] (lookupEntries 15 19 true)
#guard padHolds 24 [20, 20, 20, 20] [16, 16, 16, 16] (lookupEntries 22 18 true)

/-! ## 2. It does not go through against another list

The dry run of Forest.pad does not go through against a list with the shift's round for a single
call, without it for two calls, with a key level too few, with a table level too many, without its
last entry, or with one entry more. Each time it fails under the name plan.
-/

#guard padName 10 [10, 11] [5, 6] (lookupEntries 12 7 true) == ""
#guard padName 10 [10] [5] (lookupEntries 10 5 true) == "plan"
#guard padName 10 [10, 11] [5, 6] (lookupEntries 12 7 false) == "plan"
#guard padName 10 [10, 11] [5, 6] (lookupEntries 11 7 true) == "plan"
#guard padName 10 [10, 11] [5, 6] (lookupEntries 12 8 true) == "plan"
#guard padName 10 [10, 11] [5, 6] (lookupEntries 12 7 true).dropLast == "plan"
#guard padName 10 [10, 11] [5, 6] (lookupEntries 12 7 true ++ [entry "LINE" 0 1]) == "plan"

/-! ## 3. The claims and the list of owed claims

In the same dry run, after the messages, all claims can be added and the list of owed claims is
then settled. The run fails without the claim on the key vectors, without the claims that read
only mask entries, without the mark that the plane claims are added, and with an lm that
planeCols refuses. No guard of this section compares the name of a refusal: it sees only that the
dry run fails.
-/

#guard dryHolds (padAndClaims 10 5 [10, 11] [5, 6] 0) 574 (lookupEntries 12 7 true)
#guard !dryHolds (padAndClaims 10 5 [10, 11] [5, 6] 1) 574 (lookupEntries 12 7 true)
#guard !dryHolds (padAndClaims 10 5 [10, 11] [5, 6] 2) 574 (lookupEntries 12 7 true)
#guard !dryHolds (padAndClaims 10 5 [10, 11] [5, 6] 3) 574 (lookupEntries 12 7 true)
#guard !dryHolds (padAndClaims 10 4 [10, 11] [5, 6] 0) 574 (lookupEntries 12 7 true)
-- 574 scalars: the closed form of OnBytes/Model/TestForest.lean at v = 12 and d = 7
#guard (shape (calls [10, 11] [5, 6]) 10).toOption.map elems == some 574

/-! ## 4. The weights on the rows of the planes' matrix

The weights under which the counts are summed, at lm = 5, 6 and 8: the three lines PHIP of
verifier/tests/forest_weights.txt, which repeat the 32 numbers typed here. Then the weights
under which the planes are read, at two points of 0 and 1: phiB is 1 at the one row that the
point names, and each of the two points gives its own row.
-/

#guard phiP 5 == powers32
#guard phiP 6 == powers32 ++ powers32
#guard phiP 8 == (Array.range 8).flatMap fun _ => powers32
#guard (twoPoints.shape.kT, twoPoints.shape.cK) == (6, 1)
-- the low two bits of t = 38 are 2: row 2 * 32 + 13
#guard phiB twoPoints 7 0 == some ((Array.range 128).map fun r => if r == 77 then oneE else zeroE)
-- the low two bits of t = 5 are 1: row 1 * 32 + 30
#guard phiB twoPoints 7 1 == some ((Array.range 128).map fun r => if r == 62 then oneE else zeroE)

/-! ## 5. The public polynomials at points of 0 and 1

At points whose coordinates are 0 and 1 the public polynomials give back what they interpolate.
At three groups, a call's weight is 1 on the call's own trees and 0 on all other numbers, also
on the numbers of trees that hold only padding. Two tables give their rows. At one group of
three calls the joined table gives call c's row moved by c theta, and the last call's for the
number after the last call; and the padding key of call 2 is moved by 2 theta.
-/

#guard weightsHold 22 [14, 16, 15, 16, 14, 15, 16] [16, 8, 16, 8, 16, 8, 16]
#guard weightsHold 30 [10, 11, 12, 13, 14] [8, 8, 8, 8, 8]
#guard weightsHold 10 [10, 10, 10] [5, 6, 5]
#guard (List.range 32).all fun t => tableAt written (bitsOf 5 t) == ofF (1000 + 7 * t).toUInt64
#guard (List.range 64).all fun t =>
  tableAt { name := "r", n := 10, k := 6, kappa := 5 } (bitsOf 6 t) == ofF t.toUInt64
#guard three.NC == 3 && three.cK == 2
#guard (List.range 4).all fun c =>
  joinedTableAt three (E.mk3 5 6 7) #[ofF 100, ofF 200, ofF 300] (bitsOf 2 c) ==
    addE (ofF (100 * (min c 2 + 1)).toUInt64) (scaleE (min c 2).toUInt64 (E.mk3 5 6 7))
#guard padKeyOf { three with calls := three.calls.modify 2 fun k => { k with t0 := 9 } }
  (E.mk3 5 6 7) 2 == E.mk3 19 12 14

/-! ## 6. Wrong public numbers and a caller's faults

Some refusals that only wrong public numbers or a caller's fault can cause. Forest.pad refuses
numbers of padding keys that Forest.pubAsk refuses: too many in a tree, a call that is all
padding, a list of the wrong length. paddingLaid refuses a count that differs from these
numbers. join refuses a list of forms whose length is not the number of calls. uEnt refuses an
array that is not there or has no column, and a row's number from 2^32 on; where it goes through
it names row x / K and column x mod K. Next to each refusal
there is a run that goes through. The last guards compare the names of these refusals:
Forest.pad fails under the word "refused", since it drops the name that Forest.pubAsk returns;
the three others fail under their own names. Making the plane claims of one lookup a second time
fails, also under "refused"; the first time goes through. No guard tries the conditions
internal-forest-point, internal-slot-count and internal-forest-place of Forest.pad.
-/

-- the numbers of padding keys: one tree of 1024 keys
#guard padWith 10 [10] [5] #[0] (lookupEntries 10 5 false)
#guard padWith 10 [10] [5] #[1023] (lookupEntries 10 5 false)
#guard !padWith 10 [10] [5] #[1024] (lookupEntries 10 5 false)
#guard !padWith 10 [10] [5] #[1025] (lookupEntries 10 5 false)
#guard !padWith 10 [10] [5] #[] (lookupEntries 10 5 false)
#guard !padWith 10 [10] [5] #[0, 0] (lookupEntries 10 5 false)
-- of two calls the first in the list, whose one tree has the number 2, is all padding
#guard padWith 10 [10, 11] [5, 6] #[0, 0, 1023] (lookupEntries 12 7 true)
#guard !padWith 10 [10, 11] [5, 6] #[0, 0, 1024] (lookupEntries 12 7 true)
-- the places that the key forms leave to the padding
#guard dryHolds (padThen 10 [10, 11] [5, 6] fun h g => paddingLaid g (noPub h)) 574
  (lookupEntries 12 7 true)
#guard !dryHolds (padThen 10 [10, 11] [5, 6] fun h g => paddingLaid g ((noPub h).modify 0 (· + 1)))
  574 (lookupEntries 12 7 true)
#guard !dryHolds (padThen 10 [10, 11] [5, 6] fun _ g => paddingLaid g #[]) 574
  (lookupEntries 12 7 true)
-- the forms of the key vectors: one for each call
#guard dryHolds (padThen 10 [10, 11] [5, 6] fun h g => do
  let _ ← join g (Array.replicate h.NC (Aff.ofConst zeroE))) 574 (lookupEntries 12 7 true)
#guard !dryHolds (padThen 10 [10, 11] [5, 6] fun _ g => do let _ ← join g #[]) 574
  (lookupEntries 12 7 true)
#guard !dryHolds (padThen 10 [10, 11] [5, 6] fun h g => do
  let _ ← join g (Array.replicate (h.NC + 1) (Aff.ofConst zeroE))) 574 (lookupEntries 12 7 true)
-- an entry of a vector that is stored as an array
#guard entHolds #[{ K := 1 }] 0 0
#guard entHolds #[{ K := 1 }] 0 (2 ^ 32 - 1)
#guard !entHolds #[{ K := 1 }] 0 (2 ^ 32)
#guard entHolds #[{ K := 8 }] 0 (2 ^ 35 - 1)
#guard !entHolds #[{ K := 8 }] 0 (2 ^ 35)
#guard !entHolds #[] 0 0
#guard !entHolds #[{ K := 1 }] 1 0
#guard !entHolds #[{ K := 0 }] 0 0
#guard entOf #[{ K := 1 }, { K := 8 }] 1 19 == some [(1, 2, 3)]
-- the names of these refusals
#guard dryName (pad (calls [10, 11] [5, 6]) #[0, 0, 1023] 10) (({} : Fork).slots 574)
  (lookupEntries 12 7 true) == ""
#guard dryName (pad (calls [10, 11] [5, 6]) #[0, 0, 1024] 10) (({} : Fork).slots 574)
  (lookupEntries 12 7 true) == "refused"
#guard dryName (pad (calls [10, 11] [5, 6]) #[0, 0, 1025] 10) (({} : Fork).slots 574)
  (lookupEntries 12 7 true) == "refused"
#guard dryName (pad (calls [10, 11] [5, 6]) #[0, 0] 10) (({} : Fork).slots 574)
  (lookupEntries 12 7 true) == "refused"
#guard dryName (padThen 10 [10, 11] [5, 6] fun h g => paddingLaid g ((noPub h).modify 0 (· + 1)))
  (({} : Fork).slots 574) (lookupEntries 12 7 true) == "internal-forest-padding-places"
#guard dryName (padThen 10 [10, 11] [5, 6] fun _ g => do let _ ← join g #[])
  (({} : Fork).slots 574) (lookupEntries 12 7 true) == "internal-forest-join"
#guard dryName (uEnt 0 0) { trees := #[{ K := 1 }] } [] == ""
#guard dryName (uEnt 0 (2 ^ 32)) { trees := #[{ K := 1 }] } [] == "internal-L-row"
#guard dryName (uEnt 0 0) { trees := #[{ K := 0 }] } [] == "internal-L-row"
#guard dryName (uEnt 0 0) {} [] == "internal-L-row"
-- the plane claims of one lookup are made once
#guard dryName (padThen 10 [10, 11] [5, 6] fun _ g => do
  let _ ← planeClaims g 5 (fun _ _ => pure (Aff.ofConst zeroE)) (fun _ => pure (Aff.ofConst zeroE)))
  (({} : Fork).slots 574) (lookupEntries 12 7 true) == ""
#guard dryName (padThen 10 [10, 11] [5, 6] fun _ g => do
  let _ ← planeClaims g 5 (fun _ _ => pure (Aff.ofConst zeroE)) (fun _ => pure (Aff.ofConst zeroE))
  let _ ← planeClaims g 5 (fun _ _ => pure (Aff.ofConst zeroE)) (fun _ => pure (Aff.ofConst zeroE)))
  (({} : Fork).slots 574) (lookupEntries 12 7 true) == "refused"

/-! ## 7. Equality weights over a stretch of bits

eqLow and eqLowAt take rs[v] as the coordinate of bit v. At a point of 0 and 1 that is not the
same read backwards, eqLow is 1 at the one index whose bits are the point's and 0
elsewhere; at made-up elements eqLowAt gives the entries of eqLow.
-/

-- bits 1, 2, 3 of the point are 0, 0, 1: the index 4
#guard eqLow #[oneE, zeroE, zeroE, oneE, oneE] 1 4 ==
  (Array.range 8).map fun c => if c == 4 then oneE else zeroE
#guard (List.range 8).all fun c =>
  eqLowAt #[E.mk3 1 2 3, E.mk3 4 5 6, E.mk3 7 8 9, E.mk3 10 11 12, E.mk3 13 14 15] 1 4 c ==
    (eqLow #[E.mk3 1 2 3, E.mk3 4 5 6, E.mk3 7 8 9, E.mk3 10 11 12, E.mk3 13 14 15] 1 4).getD c
      zeroE

/-! ## 8. The weights of the claim on the key vectors

The weights of Forest.join at a group of five trees, so that three numbers of trees hold only
padding. With all key forms 0, and the number of a tree as the point zy, the claim's constant is
alpha - c theta for a tree of call c, and alpha - (call 0's padding key) for each of the three
others.
-/

#guard (fiveTrees.NT, fiveTrees.rK, fiveTrees.callOf) == (5, 3, #[0, 0, 1, 2, 3])
#guard (List.range 5).all fun y =>
  joinAt fiveTrees (E.mk3 5 6 7) (E.mk3 21 22 23) y ==
    some (subE (E.mk3 21 22 23) (scaleE (fiveTrees.callOf.getD y 0).toUInt64 (E.mk3 5 6 7)))
#guard [5, 6, 7].all fun y =>
  joinAt fiveTrees (E.mk3 5 6 7) (E.mk3 21 22 23) y == some (subE (E.mk3 21 22 23) (ofF 9))

end OnBytes.Model.Forest.Test
