-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionSumsHonest.lean: the two sumchecks of the attention sub-proof, run on
the messages of an honest prover that is written in this file, on arbitrary tables.

The tests run when this file is compiled. The program does not import this file.

The section The prover says how the prover works.

What is tested.
 1. A sumcheck of products with two variables and two pairs, which starts from a hidden value.
 2. A sumcheck by degrees with the degrees 2 and 3 and three end values, from a public start.
In both the check adds the row and one claim for each end value (the first also one for the start).
These claims compare a hidden value with the prover's true value, which a verifier does not know. On
the honest messages the one equation (the sum of all claims under the powers of the batching
element; Fork.settle in OnBytes/Model/Hide.lean) holds on the prover's mask row. If 1 is added to
any one scalar of the messages while the draws stay as they are, it does not hold. It does not hold
either if 1 is added to one weight or to the summand that the verifier takes. With a weight too many
or too few the sumcheck of products refuses under internal-sc3. Either sumcheck refuses a start that
names a slot that is still free. The draws are fixed elements of this file: no hash makes them from
the messages.

What is not tried: no pair of maps, no end value, no variable; a degree of 0 or above 64 in scdIn; a
second call of sc3Row or scdRow on the same state; a dry run of either check.

The prover here is not the C++ prover. It was written from the same reading of the protocol as
OnBytes/Model/AttentionSums.lean, so a misreading that both share is not found here. The file holds
no theorem.
-/
import OnBytes.Model.AttentionSums
import OnBytes.Model.TestPsc

namespace OnBytes.Attention.TestSumsHonest

open OnBytes.Model
open OnBytes.Model.TestPsc (addP scaleP mulP bump viewOf valueOn batchEntry batchNow)
open OnBytes.Psc (polyAt)

/-- The element with the coordinates a, b, c. -/
def el (a b c : UInt64) : E := E.mk3 a b c

/-! ## The prover

The prover follows the head of OnBytes/Iop/Psc.lean and its section on the hiding polynomial,
for any summand. The sumcheck runs on the polynomial
  G = U + eps S + eps gap X_1 .. X_k.
U is the hiding polynomial, whose coefficients are entries of the mask row. S is the summand, in
which each shown map has the further variable Y times an entry of the mask row added to it. gap is
the public target minus the true sum. The prover finds each round's polynomial by brute force: it
sums G over all later variables at enough nodes and interpolates.
-/

/-- The sum of a list. -/
def total (l : List E) : E := l.foldl addE zeroE

/-- The product of a list. -/
def product (l : List E) : E := l.foldl mulE oneE

/-- The n entries of the mask row from entry pos on. -/
def entries (m : Array E) (pos n : Nat) : List E :=
  (List.range n).map fun i => m.getD (pos + i) zeroE

/-- All points with n coordinates 0 or 1. -/
def cube : Nat → List (List E)
  | 0 => [[]]
  | n + 1 => (cube n).flatMap fun t => [zeroE :: t, oneE :: t]

/-- The coefficients of the polynomial that takes the values v at the nodes 0, 1, 2 and so on. -/
def interpolate (v : List E) : List E :=
  let nodes := List.range v.length
  v.zipIdx.foldl (fun s x =>
    let basis := (nodes.filter (· != x.2)).foldl (fun p j =>
      scaleP (invE (subE (ofNat x.2) (ofNat j))) (mulP p [subE zeroE (ofNat j), oneE])) [oneE]
    addP s (scaleP x.1 basis)) []

/-- The multilinear map with the table f, at a point. Coordinate 0 goes with the top bit. -/
def mapAt (f : Array E) (x : List E) : E :=
  ((eqTab x.toArray).zip f).foldl (fun s p => addE s (mulE p.1 p.2)) zeroE

/-- The hiding polynomial at the point (x, y). It is a sum of one term for each variable. The term
of a variable of x is a polynomial in that variable without a constant coefficient, times the
product of all later coordinates of x. (X has the sum 1 over 0 and 1, so this product does not
change the term's sum over the later variables.) The term of the further variable is a polynomial in
y with a constant coefficient. The coefficients are the entries of the mask row from entry pos on,
by variable and then by degree. ds: for each variable of x the number of coefficients of a round's
polynomial, which is one more than its term has; dY: the number of coefficients of the term in y. -/
def hidingAt (m : Array E) : (pos : Nat) → (ds : List Nat) → (dY : Nat) → List E → E → E
  | pos, d :: ds, dY, x :: xs, y =>
    addE (mulE (polyAt (zeroE :: entries m pos (d - 1)) x) (product xs))
      (hidingAt m (pos + (d - 1)) ds dY xs y)
  | pos, _, dY, _, y => polyAt (entries m pos dY) y

/-- One run of a sumcheck, as the prover sees it. -/
structure Run where
  /-- for each variable the number of coefficients of a round's polynomial -/
  ds : List Nat
  /-- the same for the further variable -/
  dY : Nat
  /-- the sumcheck's first slot -/
  first : Nat
  /-- the mask row -/
  m : Array E
  /-- what the verifier will draw to join the hiding polynomial to the claim -/
  eps : E
  /-- the challenges of the variables -/
  rs : List E
  /-- the challenge of the further variable -/
  beta : E
  /-- the public target minus the true sum -/
  gap : E
  /-- the summand at a point x and at the further variable y -/
  S : List E → E → E
  /-- the shown maps at the point of the challenges -/
  ends : List E

/-- The slot of the first end value. -/
def Run.sEnd (t : Run) : Nat := t.first + (t.ds.map (· - 1)).sum + t.dY

/-- The polynomial on which the sumcheck runs. -/
def Run.G (t : Run) (x : List E) (y : E) : E :=
  addE (hidingAt t.m t.first t.ds t.dY x y)
    (mulE t.eps (addE (t.S x y) (mulE t.gap (product x))))

/-- The polynomial of the round in variable number i, which has d coefficients. -/
def Run.round (t : Run) (i d : Nat) : List E :=
  let before := t.rs.take i
  interpolate ((List.range d).map fun c =>
    total ((cube (t.ds.length - i - 1)).map fun later => t.G (before ++ ofNat c :: later) zeroE))

/-- The prover's messages: the sum of the hiding polynomial; for each variable the coefficients
except the linear one; for the further variable the coefficients except the constant; the end
values, each plus the last challenge times its entry of the mask row. -/
def Run.messages (t : Run) : List (List E) :=
  [[total ((cube t.ds.length).map fun x => hidingAt t.m t.first t.ds t.dY x zeroE)]] ++
  (t.ds.zipIdx.map fun x => (t.round x.2 x.1).eraseIdx 1) ++
  [(interpolate ((List.range t.dY).map fun c => t.G t.rs (ofNat c))).drop 1,
   t.ends.zipIdx.map fun x => addE x.1 (mulE t.beta (t.m.getD (t.sEnd + x.2) zeroE))]

/-- What the verifier draws in the rounds of the run. -/
def Run.draws (t : Run) : List (List E) :=
  [[t.eps]] ++ t.rs.map (fun r => [r]) ++ [[t.beta], []]

/-- The plan's entries of the run's rounds. head: the number of scalars that come before the sum of
the hiding polynomial in its message. The tests here do not read msg. -/
def Run.plan (t : Run) (head : Nat) : List Fmt.Entry :=
  let first : Fmt.Entry := { name := "PSC epsilon", msg := 24 * (head + 1), drawE := 1 }
  let inX (d : Nat) : Fmt.Entry := { name := "PSC round", msg := 24 * (d - 1), drawE := 1 }
  let inY : Fmt.Entry := { name := "PSC Y", msg := 24 * (t.dY - 1), drawE := 1, drawNZ := 1 }
  let values : Fmt.Entry := { name := "PSC values", msg := 24 * t.ends.length }
  first :: t.ds.map inX ++ [inY, values]

/-- A mask row of arbitrary elements. -/
def maskRow : Array E := (Array.range 20).map fun i =>
  E.mk3 (UInt64.ofNat (3 * i + 7)) (UInt64.ofNat (i * i + 1)) (UInt64.ofNat (5 * i + 2))

/-- The element that batches the claims. -/
def theta : E := el 6 2 0

/-- Runs a check on messages and draws. After them comes the round that batches the given number of
claims. Returns the value of the one equation on the mask row, or none if the check stops. -/
def valueOf (check : SubM (Array E × E)) (plan : List Fmt.Entry) (claims : Nat)
    (msgs draws : List (List E)) : Option E :=
  match Blk.walk (check.run {}) { entries := plan ++ [batchEntry claims], st := {} } []
      (viewOf (msgs ++ [[]]) (draws ++ [[theta]])) with
  | some (y, []) => some (valueOn maskRow y.1)
  | _ => none

/-- The name under which a check fails on messages and draws. Returns none if it does not fail. -/
def failsAs (check : SubM (Array E × E)) (plan : List Fmt.Entry) (claims : Nat)
    (msgs draws : List (List E)) : Option String :=
  match (check.run {}).runNamed { entries := plan ++ [batchEntry claims], st := {} } false
      (viewOf (msgs ++ [[]]) (draws ++ [[theta]])) [] with
  | .error e => some e.name
  | .ok _ => none

/-! ## The sumcheck of products -/

/-- The tables of the two pairs of maps, on four places. -/
def tabA : Array (Array E) :=
  #[#[el 2 6 5, el 3 5 8, el 9 7 9, el 3 2 3], #[el 1 4 1, el 5 9 2, el 6 5 3, el 5 8 9]]

/-- See tabA. -/
def tabB : Array (Array E) :=
  #[#[el 8 4 6, el 2 6 4, el 3 3 8, el 3 2 7], #[el 7 9 3, el 2 3 8, el 4 6 2, el 6 4 3]]

/-- The weight of pair b at a point: a factor of its own times eq with a fixed point. -/
def weightAt (b : Nat) (x : List E) : E :=
  mulE ((#[el 3 1 4, el 1 5 9] : Array E).getD b zeroE) (mapAt (eqTab #[el 2 7 1, el 8 2 8]) x)

/-- The run. Slot 0 holds the start, so the sumcheck begins at slot 1 and its end values have the
slots 10 to 13. -/
def run3 : Run :=
  let rs : List E := [el 2 3 0, el 7 8 1]
  let pair (b : Nat) (x : List E) (y : E) : E :=
    mulE (weightAt b x) (mulE
      (addE (mapAt (tabA.getD b #[]) x) (mulE y (maskRow.getD (10 + 2 * b) zeroE)))
      (addE (mapAt (tabB.getD b #[]) x) (mulE y (maskRow.getD (11 + 2 * b) zeroE))))
  { ds := [4, 4], dY := 3, first := 1, m := maskRow, eps := el 4 5 9, rs := rs, beta := el 6 4 0,
    gap := maskRow.getD 0 zeroE, S := fun x y => addE (pair 0 x y) (pair 1 x y),
    ends := [mapAt (tabA.getD 0 #[]) rs, mapAt (tabB.getD 0 #[]) rs, mapAt (tabA.getD 1 #[]) rs,
      mapAt (tabB.getD 1 #[]) rs] }

/-- The true sum. -/
def sum3 : E := total ((cube 2).map fun x => run3.S x zeroE)

/-- The check: the start is received as a hidden value; then the sumcheck, its row, the claim that
says what the start is, and one claim for each end value. spoil is added to the weight of pair 1.
more is appended to the two weights, and then the last drop weights are left out. -/
def check3 (spoil : E) (more : Array E := #[]) (drop : Nat := 0) : SubM (Array E × E) := do
  SubM.slots (1 + sc3Slots 2 2)
  SubM.setPlanClaims 6
  let s ← SubM.claimsIn 1
  let o ← sc3In 2 2 (Aff.slot s)
  let W := #[weightAt 0 o.r.toList, addE spoil (weightAt 1 o.r.toList)] ++ more
  let o ← sc3Row o (W.extract 0 (W.size - drop))
  batchNow
  SubM.lin o.rowU
  SubM.lin (Aff.slot s - Aff.ofConst sum3)
  SubM.lin (sc3A o 0 - Aff.ofConst (run3.ends.getD 0 zeroE))
  SubM.lin (sc3B o 0 - Aff.ofConst (run3.ends.getD 1 zeroE))
  SubM.lin (sc3A o 1 - Aff.ofConst (run3.ends.getD 2 zeroE))
  SubM.lin (sc3B o 1 - Aff.ofConst (run3.ends.getD 3 zeroE))
  SubM.batchRows 6
  SubM.allTaken
  SubM.must (o.sEnd == run3.sEnd && (← SubM.slot) == 14)
  SubM.test (o.r == run3.rs.toArray)
  SubM.settle (← SubM.slot)

/-- The prover's messages: the start under its mask is the first scalar of the first message. -/
def msgs3 : List (List E) :=
  match run3.messages with
  | first :: rest => (addE sum3 (maskRow.getD 0 zeroE) :: first) :: rest
  | [] => []

/-- The value of the one equation if 1 is added to scalar number k of the messages. There are 14,
counted from 0, so k = 14 changes nothing. -/
def value3 (k : Nat) (spoil : E := zeroE) : Option E :=
  valueOf (check3 spoil) (run3.plan 1) 6 (bump k msgs3) run3.draws

#guard (msgs3.map (·.length)) == [2, 3, 3, 2, 4]
#guard value3 14 == some zeroE
#guard (List.range 14).all fun k => (value3 k).any fun v => !isZeroE v
#guard (value3 14 oneE).any fun v => !isZeroE v
-- with a weight too many or too few the check stops, under the name of that test
#guard failsAs (check3 zeroE) (run3.plan 1) 6 msgs3 run3.draws == none
#guard failsAs (check3 zeroE #[oneE]) (run3.plan 1) 6 msgs3 run3.draws == some "internal-sc3"
#guard failsAs (check3 zeroE #[] 1) (run3.plan 1) 6 msgs3 run3.draws == some "internal-sc3"
#guard sumsNames.contains "internal-sc3"

/-- Only the messages of the sumcheck of products, from the given start. -/
def only3 (start : Aff) : SubM (Array E × E) := do
  SubM.slots (sc3Slots 2 2)
  let _ ← sc3In 2 2 start
  pure (#[], zeroE)

-- a start that names a slot that is still free is refused; the test has no name of its own
#guard failsAs (only3 (Aff.ofConst zeroE)) (run3.plan 0) 0 run3.messages run3.draws == none
#guard failsAs (only3 (Aff.slot 5)) (run3.plan 0) 0 run3.messages run3.draws == some "refused"

/-! ## The sumcheck by degrees -/

/-- The tables of three maps. The third depends only on the second variable. -/
def tabK : Array (Array E) :=
  #[#[el 5 0 2, el 8 8 4, el 1 9 7, el 1 6 9], #[el 3 9 9, el 3 7 5, el 1 0 5, el 8 2 0],
    #[el 9 7 4, el 9 4 4, el 9 7 4, el 9 4 4]]

/-- The run: the sum of the product of the three maps. It has degree 2 in the first variable and
degree 3 in the second. The sumcheck begins at slot 0, and its end values have the slots 9 to
11. -/
def runD : Run :=
  let rs : List E := [el 5 9 2, el 3 0 7]
  let shown (j : Nat) (x : List E) (y : E) : E :=
    addE (mapAt (tabK.getD j #[]) x) (mulE y (maskRow.getD (9 + j) zeroE))
  { ds := [3, 4], dY := 4, first := 0, m := maskRow, eps := el 8 1 6, rs := rs, beta := el 4 0 6,
    gap := zeroE, S := fun x y => mulE (shown 0 x y) (mulE (shown 1 x y) (shown 2 x y)),
    ends := (List.range 3).map fun j => mapAt (tabK.getD j #[]) rs }

/-- The true sum. -/
def sumD : E := total ((cube 2).map fun x => runD.S x zeroE)

/-- The check: the sumcheck from the public start, its row on the product of what was shown, and
one claim for each end value. spoil is added to the summand. -/
def checkD (spoil : E) : SubM (Array E × E) := do
  SubM.slots (sumcheckSlotsDegrees [2, 3] 3 3)
  SubM.setPlanClaims 4
  let o ← scdIn [2, 3] 3 3 (Aff.ofConst sumD)
  let k ← SubM.shown o.sEnd
  let l ← SubM.shown (o.sEnd + 1)
  let n ← SubM.shown (o.sEnd + 2)
  let o ← scdRow o (addE spoil (mulE k (mulE l n)))
  batchNow
  SubM.lin o.rowU
  SubM.lin (Aff.slot o.sEnd - Aff.ofConst (runD.ends.getD 0 zeroE))
  SubM.lin (Aff.slot (o.sEnd + 1) - Aff.ofConst (runD.ends.getD 1 zeroE))
  SubM.lin (Aff.slot (o.sEnd + 2) - Aff.ofConst (runD.ends.getD 2 zeroE))
  SubM.batchRows 4
  SubM.allTaken
  SubM.must (o.sEnd == runD.sEnd && (← SubM.slot) == 12)
  SubM.test (o.r == runD.rs.toArray)
  SubM.settle (← SubM.slot)

/-- The value of the one equation if 1 is added to scalar number k of the messages. There are 12,
counted from 0, so k = 12 changes nothing. -/
def valueD (k : Nat) (spoil : E := zeroE) : Option E :=
  valueOf (checkD spoil) (runD.plan 0) 4 (bump k runD.messages) runD.draws

#guard (runD.messages.map (·.length)) == [1, 2, 3, 3, 3]
#guard valueD 12 == some zeroE
#guard (List.range 12).all fun k => (valueD k).any fun v => !isZeroE v
#guard (valueD 12 oneE).any fun v => !isZeroE v

/-- Only the messages of the sumcheck by degrees, from the given start. -/
def onlyD (start : Aff) : SubM (Array E × E) := do
  SubM.slots (sumcheckSlotsDegrees [2, 3] 3 3)
  let _ ← scdIn [2, 3] 3 3 start
  pure (#[], zeroE)

-- a start that names a slot that is still free is refused; the test has no name of its own
#guard failsAs (onlyD (Aff.ofConst zeroE)) (runD.plan 0) 0 runD.messages runD.draws == none
#guard failsAs (onlyD (Aff.slot 5)) (runD.plan 0) 0 runD.messages runD.draws == some "refused"

end OnBytes.Attention.TestSumsHonest
