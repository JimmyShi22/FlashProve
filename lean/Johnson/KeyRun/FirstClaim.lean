-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/KeyRun/FirstClaim.lean: the claim that a key file's first chain leaves on the committed
matrix, as a plain function with code of the chain's public parameters and its view: `claim₁`.

Words. Chain, view, plan, program, block, dry run, context: the head of
Johnson/KeyRun/ThirdAtClaim.lean. Lookup, part, key tree, level, plane, tie: OnBytes/Iop/Lkp.lean.
Sumcheck, Y: OnBytes/Iop/Psc.lean. Pending row: OnBytes/Iop/Wf.lean. Mask entry, ledger:
OnBytes/Iop/Ground.lean.
In the program that claim is the value of a run of blocks (`Key.oneTime`, OnBytes/Key/OneTime.lean):
the lookups, the pending rows that they leave, and the batching of these rows into one. Here it is
computed with no run: there is no value of the type `Blk`, no context and no dry run beneath
`claim₁`.

Why so few rounds are read. A zero-knowledge sumcheck hands on one claim for each shown value (the
field `ends` of what `Psc.run` returns, OnBytes/Iop/Psc.lean). Such a claim holds the sumcheck's
challenges, the shown value, one fresh mask entry and the challenge of Y. It holds nothing of the
claim with which the sumcheck began. So the claim on the leaves of a part's key tree follows from
the rounds of the tree's last level alone, and of a lookup's rounds `claim₁` reads only the shift,
alpha and each part's last level. `roundsRead` lists the rounds of which a value is read.

What each piece is.
  - Written here, after the program's text: `layLoop`, `lay` (after `Send.admit` and
    `Blk.takeMask`); `headLen`, `levelLen`, `treeLen` (after `Lkp.roundsOf`); `leavesOf` (after
    `Lkp.levelChain` at a key tree's last level, with the field `ends` of `Psc.run` and the change
    of the point in `Lkp.psc` written out); `keysAt` (after `Lkp.run` and `Lkp.keyTrees`);
    `pendingAt` (after `Wf.pendingOf`); `heardAt` (after `Psc.hear`); `batched` (after
    `Batt.verify`); `claimOfKeys` (after `memberFirstVerify`).
  - The program's own functions, called as they stand, none of them a block: `Lkp.orderBeginning`,
    `Lkp.byVariable`, `Lkp.keysOf`, `Lkp.keyMasks`, and `Lkp.roundsOf`, `Lkp.treeRounds`, two lists
    of rounds that the program keeps for its tests and does not call itself (OnBytes/Iop/Lkp.lean);
    `lineAt`, `Psc.run` (OnBytes/Iop/Psc.lean); `Wf.lookupsOf`, `Wf.indexMasks`,
    `Wf.indexMaskEntries`, `Wf.eqPlaces`, `Wf.coveredSum`, `Wf.sumOfForm`, `Wf.pendingRow`
    (OnBytes/Iop/Wf.lean); `Wf.matrixOf` (OnBytes/Key/Ranges.lean); `Batt.fits`, `Batt.masksOf`,
    `Batt.claimOf`, `Batt.summandOf`, `Batt.rowOf` (OnBytes/Iop/Batt.lean); `memberClaim`
    (OnBytes/Iop/Lin.lean); `Send.freeMaskEntries` (OnBytes/Iop/Send.lean); `Blk.nextRealRow`
    (OnBytes/Iop/Ground.lean: a function on numbers, in spite of the first part of its name); and
    small helpers on field elements, numbers and lists.

What it is not.
  - No theorem is stated: no equation ties `claim₁` to the program's claim or to a typed protocol
    of this library. Nothing on soundness or hiding.
  - It makes a claim and tests next to nothing. A changed value in a round that it does not read,
    or a changed sent element in a round of which it reads the challenge alone, leaves the claim as
    it was: to catch these is the work of the first chain's own check, which is not here.
  - Not done here, and done by the program's run: the tests on the public parameters
    (`Key.admitted`, `Lkp.Public.ok`, `memberRowsFit`), the plan's count of rows at BAT-sigma
    (`Blk.requireRows`), the numbers of coefficients sent in the last levels' rounds, the rows that
    the lookups add to their group, the first chain's proximity test, the closing of the ledger of
    mask entries.


-/
import OnBytes.Key.OneTime

set_option autoImplicit false

namespace Johnson.KeyRun.FirstClaim

open OnBytes
open OnBytes.Params (OneTime WfLookup)

/-! ## Reading a view's rounds -/

/-- The elements that the prover sends in a round. Nothing if an item is not of the kind `.e`. -/
def sentOf (r : Fmt.RoundView) : Option (List E) :=
  r.vals.mapM fun g =>
    match g with
    | .e x => some (E.ofTriple x)
    | _ => none

/-- The elements that a round draws. -/
def drawnOf (r : Fmt.RoundView) : List E := r.drawn.elems.map E.ofTriple

/-- The element that a round draws, if it draws exactly one. -/
def oneDrawn (r : Fmt.RoundView) : Option E :=
  match drawnOf r with
  | [x] => some x
  | _ => none

/-- A chain's rounds with the names that the plan gives them. -/
structure Rounds where
  /-- the names of the plan's entries, in their order -/
  names : Array String
  /-- the view's rounds, in their order -/
  rvs : Array Fmt.RoundView

/-- Round number i, if the plan calls it by this name. -/
def Rounds.named (R : Rounds) (i : Nat) (name : String) : Option Fmt.RoundView :=
  if R.names[i]? == some name then R.rvs[i]? else none

/-- The rounds of a key's first chain. -/
def roundsOf (one : OneTime) (v : Fmt.View) : Rounds :=
  ⟨(one.given.rounds.map (·.name)).toArray, v.rounds.toArray⟩

/-! ## The order in which mask entries are given out -/

/-- The numbers of the next count entries from the number next on, appended to acc. An entry's row
is the low logRows bits of its number, and a number on a row beyond the real ones is passed over. -/
def layLoop (rows logRows : Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, acc => acc
  | n + 1, next, acc =>
    let i := Blk.nextRealRow rows logRows (2 ^ logRows) next
    layLoop rows logRows n (i + 1) (acc.push i)

/-- The numbers of the first count free entries of a sampled message's mask rows, in the order in
which they are given out. Nothing if the message has no mask rows or fewer free entries. -/
def lay (codes : Codes) (s : OracleShape) (count : Nat) : Option (Array Nat) :=
  let free := Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers
  if 0 < s.maskRows && count ≤ free then
    some (layLoop (max s.maskRows 1) (ceilLog2 s.maskRows) count 0 #[])
  else none

/-! ## Where a lookup's rounds are -/

/-- The rounds of a lookup before its first key tree: the shift if there is one, alpha, three rounds
for each step of the tie and for each step from the product of the parts' roots to a root, and the
draw that joins the planes. -/
def headLen (S : Lkp.Public) : Nat :=
  (if S.shifted then 1 else 0) + 1 + 3 * (S.planes - 1) + 3 * (S.parts.length - 1) + 1

/-- The rounds of the last level of a key tree of v levels: PSC epsilon, v - 1 times PSC round,
PSC Y, PSC values, LINE. -/
def levelLen (v : Nat) : Nat := v + 3

/-- The rounds of a key tree of v levels. -/
def treeLen (v : Nat) : Nat := (Lkp.treeRounds 0 v 0).length

/-- The rounds of a lookup. -/
def lookupLen (S : Lkp.Public) : Nat := (Lkp.roundsOf 0 S).length

/-! ## The claims on the keys -/

/-- The claim on the leaves of a key tree of v levels. first: the number of the first round of the
tree's last level. a, b: the two mask entries under which the two halves are shown. The two halves'
claims are at the level's challenges, each put back at its variable's place; the draw of the round
LINE joins them. -/
def leavesOf (R : Rounds) (S : Lkp.Public) (first v : Nat) (a b : Slot) : Option PointClaim := do
  guard (1 ≤ v)
  let _ ← R.named first "PSC epsilon"
  let byRound ← (List.range (v - 1)).mapM fun t =>
    (R.named (first + 1 + t) "PSC round").bind oneDrawn
  let beta ← (R.named (first + v) "PSC Y").bind oneDrawn
  let values ← (R.named (first + v + 1) "PSC values").bind sentOf
  let rho ← (R.named (first + v + 2) "LINE").bind oneDrawn
  let order := Lkp.orderBeginning S.lastKeyLevelOrder (v - 1)
  guard (order.length == v - 1)
  let point := Lkp.byVariable byRound order
  match values with
  | [y0, y1] => pure (lineAt rho ⟨point, [(a, beta)], y0⟩ ⟨point, [(b, beta)], y1⟩)
  | _ => none

/-- For each part of a lookup whose first round has the number first: the number of the first round
of its key tree's last level, and the tree's number of levels. -/
def lastLevels (S : Lkp.Public) (first : Nat) : List (Nat × Nat) :=
  (S.parts.foldl (fun (acc : Nat × List (Nat × Nat)) v =>
    let stop := acc.1 + treeLen v
    (stop, (stop - levelLen v, v) :: acc.2)) (first + headLen S, [])).2.reverse

/-- The claims on the keys of one lookup, one for each part. first: the number of the lookup's first
round. slots: the mask entries of the claims on keys, two for each part, in the parts' order. -/
def keysAt (R : Rounds) (S : Lkp.Public) (first : Nat) (slots : List Slot) :
    Option (List Lkp.Keys) := do
  let theta ← if S.shifted then (R.named first "LKP shift").bind oneDrawn else pure zeroE
  let alpha ← (R.named (first + (if S.shifted then 1 else 0)) "LKP").bind oneDrawn
  (lastLevels S first).zipIdx.mapM fun p => do
    let a ← slots[2 * p.2]?
    let b ← slots[2 * p.2 + 1]?
    let onLeaves ← leavesOf R S p.1.1 p.1.2 a b
    pure (Lkp.keysOf S theta alpha p.2 onLeaves)

/-- The number of the first round of the first lookup: before it the index-mask message and the
message with the multiplicities are sent and sampled, in two rounds each. -/
def firstLookupAt : Nat := 4

/-- The lookups as the lookup argument takes them, each with the number of its first round and the
number of mask entries that the lookups before it have taken of the index-mask message. -/
def lookupsAt (one : OneTime) : List (Lkp.Public × Nat × Nat) :=
  ((Wf.lookupsOf one.ranges (Wf.matrixOf one.lin)).foldl
    (fun (acc : Nat × Nat × List (Lkp.Public × Nat × Nat)) S =>
      (acc.1 + lookupLen S, acc.2.1 + Lkp.keyMasks S, (S, acc.1, acc.2.1) :: acc.2.2))
    (firstLookupAt, 0, [])).2.2.reverse

/-- The mask entries that the chain takes of the index-mask message, in the order in which they are
taken. idx: the number of that message among the chain's oracle messages. -/
def slotsOf (one : OneTime) (idx : Nat) : Option (List Slot) :=
  (lay one.codes one.indexMasks.shape
    (Wf.indexMaskEntries one.ranges (Wf.matrixOf one.lin))).map
      fun l => l.toList.map fun i => ⟨idx, i⟩

/-- The claims on the keys of all lookups, lookup by lookup. -/
def keys₁ (one : OneTime) (v₁ : Fmt.View) (idx : Nat := 0) : Option (List (List Lkp.Keys)) := do
  let R := roundsOf one v₁
  let slots ← slotsOf one idx
  (lookupsAt one).mapM fun x => keysAt R x.1 x.2.1 ((slots.drop x.2.2).take (Lkp.keyMasks x.1))

/-! ## The pending rows -/

/-- The pending rows of one lookup, from the claims on its parts' keys, under the four conditions
that the program asks of a claim: there is one for each part; its point has one coordinate for each
bit of a key's number; its weights have no written-out factor; its weights add up to the sum of the
equality vector over the places that the part's runs cover. -/
def pendingAt (m : Wf.Matrix) (l : WfLookup) (keys : List Lkp.Keys) : Option (List TensorRow) :=
  if l.parts.length == keys.length then
    (zipT l.parts keys).mapM fun x =>
      let e := Wf.eqPlaces m x.2.point
      if x.2.point.length == m.kCol + x.1.logPlaces &&
          x.2.weights.tensors.all (·.denseVars.isEmpty) &&
          Wf.sumOfForm x.2.weights == Wf.coveredSum x.1 e then
        some (Wf.pendingRow m l x.1 x.2 e)
      else none
  else none

/-! ## The batching -/

/-- What is heard in a sumcheck over n variables in which no value is shown. first: the number of
its round PSC epsilon. -/
def heardAt (R : Rounds) (first n : Nat) : Option Psc.Heard := do
  let r ← R.named first "PSC epsilon"
  let mu ←
    match ← sentOf r with
    | [x] => some x
    | _ => none
  let eps ← oneDrawn r
  let rounds ← (List.range n).mapM fun t => do
    let q ← R.named (first + 1 + t) "PSC round"
    pure (← sentOf q, ← oneDrawn q)
  pure ⟨mu, eps, rounds, []⟩

/-- The number of the one round that the plan calls by this name. Nothing if there is none or more
than one. -/
def theRound (R : Rounds) (name : String) : Option Nat :=
  match (R.names.toList.zipIdx.filter (·.1 == name)).map (·.2) with
  | [i] => some i
  | _ => none

/-- Several rows on the matrix become one. fresh: the mask entries that the batching takes. -/
def batched (R : Rounds) (kCol : Nat) (rows : List TensorRow) (fresh : List Slot) :
    Option TensorRow := do
  guard (Batt.fits kCol rows)
  let at0 ← theRound R "BAT-sigma"
  let x ← (R.named at0 "BAT-sigma").bind oneDrawn
  let o ← Psc.run (Batt.claimOf rows x) (Batt.summandOf rows x) fresh (← heardAt R (at0 + 1) kCol)
  guard (o.rowMaps.length == rows.length)
  pure (Batt.rowOf rows o)

/-! ## The claim -/

/-- The claim, from the claims on the keys of all lookups. -/
def claimOfKeys (one : OneTime) (v₁ : Fmt.View) (keys : List (List Lkp.Keys)) (idx : Nat := 0) :
    Option LinClaim := do
  let m := Wf.matrixOf one.lin
  guard (one.ranges.lookups.length == keys.length)
  let pending := (← (zipT one.ranges.lookups keys).mapM fun x => pendingAt m x.1 x.2).flatten
  match pending with
  | [] => none
  | [r] => pure (memberClaim r)
  | _ =>
    let slots ← slotsOf one idx
    let fresh := (slots.drop (Wf.indexMasks one.ranges m)).take (Batt.masksOf m.kCol)
    pure (memberClaim (← batched (roundsOf one v₁) m.kCol pending fresh))

/-- **The claim that a key's first chain leaves on the committed matrix.** one: the chain's public
parameters. v₁: the chain's view; its sealing round may be there or not, since it is not read. idx:
the number under which the claim's mask terms name the index-mask message. -/
def claim₁ (one : OneTime) (v₁ : Fmt.View) (idx : Nat := 0) : Option LinClaim := do
  claimOfKeys one v₁ (← keys₁ one v₁ idx) idx

/-- The numbers of the rounds of which `claim₁` reads a value (a sent element or a drawn one), where
more than one row is pending. -/
def roundsRead (one : OneTime) : List Nat :=
  let R : Rounds := ⟨(one.given.rounds.map (·.name)).toArray, #[]⟩
  ((lookupsAt one).flatMap fun x =>
    ((List.range (if x.1.shifted then 2 else 1)).map (x.2.1 + ·)) ++
      (lastLevels x.1 x.2.1).flatMap fun p => (List.range (levelLen p.2 - 1)).map (p.1 + 1 + ·)) ++
  match theRound R "BAT-sigma" with
  | some i => (List.range (one.lin.kCol + 2)).map (i + ·)
  | none => []

end Johnson.KeyRun.FirstClaim
