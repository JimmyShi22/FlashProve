-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/TestLkp.lean: tests of OnBytes/Iop/Lkp.lean. They run when this file compiles.

What is tested, at small sizes.
 1. The conditions on the public inputs: two well-formed examples, and altered copies that are
    refused.
 2. The table: its extension at a corner of the cube is the row with that number.
 3. Runs of padding as cubes: each place of a run lies in exactly one cube, other places in none.
    The public factor.
 4. The claim on the keys: the weights are the equality vector, made 0 at the padding, and the
    target is such that the claim holds for keys for which the claim on the leaves holds.
 5. The orders of rounds and the blocks of real planes, at values worked out by hand. A vector cut
    to a block of planes, and weights cut to a function's own keys, entry by entry.
 6. The dry run of the block goes through on the entries of Lkp.roundsOf, with the same kinds and
    items, and takes as many mask entries as Lkp.allMasks and Lkp.keyMasks say. The four ways in
    which Lkp.verify fails before or at a row.
 7. A whole run on the messages of an honest prover that is written from the definitions: all
    rows and all claims on the keys hold; after a change to the first element sent in any one round,
    one of them fails.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Iop.Lkp

namespace OnBytes.TestLkp

open Lkp

/-- A small number as an element of the extension field. -/
def n (x : UInt64) : E := ofF x

/-- Keys in two parts, one range table of four rows, three real planes of four, one place of
padding. -/
def one : Public where
  parts := [2, 1]
  d := 2
  mu := 2
  live := 3
  readFrom := [0]
  keys := [{ function := some 0 }]
  tables := [{ logRows := 2 }]
  padding := [{ part := 0, first := 3, length := 1, row := 1 }]

/-- Two functions under the shift, a tree's number in a key's lowest bit; one table is a range, the
other is written out; a run of padding with step 2 in the second function's tree. -/
def two : Public where
  parts := [3]
  d := 2
  mu := 2
  g := 1
  shifted := true
  readFrom := [0]
  keys := [{ first := 0, function := some 0 }, { first := 1, function := some 1 }]
  tables := [{ first := 0, logRows := 1, function := 0 },
    { first := 2, logRows := 1, function := 1, rows := [n 5, n 9] }]
  padding := [{ part := 0, first := 3, logStep := 1, length := 3, row := 3 }]
  lastKeyLevelOrder := [0, 1]

#guard one.ok && two.ok
#guard one.planes == 3 && two.planes == 4 && one.allKeys == 6 && paddingCount two == 3
-- too many keys for the planes; no message named
#guard !{ one with parts := [2, 2] }.ok && !{ one with readFrom := [] }.ok
-- a part with a single key; all four planes written as 4, not as 0; a single real plane
#guard !{ one with parts := [2, 0] }.ok && !{ one with live := 4 }.ok && !{ one with live := 1 }.ok
-- the bounds on the sizes: no part; no place or more than 64 places for planes; a part with as many
-- bits as there are planes; d + planes at 64; several parts with a shift or with tree numbers
#guard !{ one with parts := [] }.ok && !{ one with mu := 0, live := 0 }.ok
#guard !{ one with mu := 7, live := 3 }.ok && !{ one with parts := [3] }.ok
#guard { one with d := 60, tables := [{ logRows := 60 }] }.sizesOK &&
  !{ one with d := 61, tables := [{ logRows := 61 }] }.sizesOK
#guard !{ one with shifted := true }.sizesOK && !{ one with g := 1 }.sizesOK
-- the table's pieces do not cover the rows; they overlap, with sizes that add up to all rows
#guard !{ one with tables := [{ logRows := 1 }] }.ok
#guard !{ one with tables := [{ logRows := 1 }, { logRows := 1 }] }.ok
-- padding: outside its part; a row number beyond the table; two runs that meet; a wrong order
#guard !{ one with padding := [{ part := 0, first := 4, length := 1, row := 1 }] }.ok
#guard !{ one with padding := [{ part := 2, first := 0, length := 1, row := 1 }] }.ok
#guard !{ one with padding := [{ part := 0, first := 3, length := 1, row := 4 }] }.ok
#guard !{ one with padding := [{ part := 0, first := 2, length := 2, row := 1 },
  { part := 0, first := 3, length := 1, row := 1 }] }.ok
#guard !{ one with padding := [{ part := 0, first := 3, length := 1, row := 1 },
  { part := 0, first := 2, length := 1, row := 1 }] }.ok
-- a part that is nothing but padding
#guard !{ one with padding := [{ part := 1, first := 0, length := 2, row := 1 }] }.ok
-- several functions without the shift; a run that leaves its tree; a run that covers every place
-- of one function
#guard !{ two with shifted := false }.ok
#guard !{ two with padding := [{ part := 0, first := 3, logStep := 0, length := 2, row := 3 }] }.ok
#guard !{ two with padding := [{ part := 0, first := 1, logStep := 1, length := 4, row := 3 }] }.ok
-- an order that names a variable which the last key level has not, or one variable twice
#guard !{ two with lastKeyLevelOrder := [0, 2] }.ok && !{ two with lastKeyLevelOrder := [1, 1] }.ok

/-- The corner of the cube whose coordinates are the low count bits of t. -/
def corner (count t : Nat) : List E :=
  (List.range count).map fun j => if t.testBit j then oneE else zeroE

#guard (List.range 4).map (rowAt one zeroE) == [n 0, n 1, n 2, n 3]
#guard (List.range 4).map (rowAt two (n 100)) == [n 0, n 1, n 105, n 109]
#guard (List.range 4).all fun t => tableAt one zeroE (corner 2 t) == rowAt one zeroE t
#guard (List.range 4).all fun t => tableAt two (n 100) (corner 2 t) == rowAt two (n 100) t
-- pieces by the low bit of a row's number, the shorter table repeated
#guard (List.range 8).map (rowAt { two with d := 3, h := 1, tables :=
    [{ first := 0, logRows := 2 }, { first := 1, logRows := 1, function := 1 }] } (n 100)) ==
  [n 0, n 100, n 1, n 101, n 2, n 100, n 3, n 101]
#guard (List.range 8).all fun t =>
  let S := { two with d := 3, h := 1, tables :=
    [{ first := 0, logRows := 2 }, { first := 1, logRows := 1, function := 1 }] }
  tableAt S (n 100) (corner 3 t) == rowAt S (n 100) t

/-- Key number i lies in the cube. -/
def inCube (c : Cube) (i : Nat) : Bool := i &&& c.mask == c.value &&& c.mask

/-- Key number i is a place of the run. -/
def inRun (p : Padding) (i : Nat) : Bool :=
  decide (p.first ≤ i) && (i - p.first) % 2 ^ p.logStep == 0 &&
  decide ((i - p.first) / 2 ^ p.logStep < p.length)

/-- Each number below 2^bits lies in one cube of the run if it is a place of it, else in none. -/
def cubesFit (p : Padding) (bits : Nat) : Bool :=
  (List.range (2 ^ bits)).all fun i =>
    ((cubesOf p bits).filter fun c => inCube c i).length == if inRun p i then 1 else 0

#guard cubesFit { first := 3, logStep := 1, length := 3 } 3
#guard cubesFit { first := 1, logStep := 0, length := 13 } 4
#guard cubesFit { first := 5, logStep := 2, length := 7 } 5
#guard cubesFit { first := 0, logStep := 0, length := 16 } 4
#guard (cubesOf { first := 1, logStep := 0, length := 13 } 4).length == 5
#guard factorOf one zeroE (n 10) == n 9 && factorOf two (n 100) (n 1000) == n (891 * 891 * 891)

/-- A point without special structure. -/
def somePoint (count : Nat) : List E :=
  (List.range count).map fun j => E.mk3 (UInt64.ofNat (3 * j + 7)) (UInt64.ofNat (j + 2)) 5

/-- Builds the true claim on the leaves of part 0 from made-up keys and tests what Lkp.keysOf makes
of it: the weights are the equality vector, 0 at the padding, and the claim on the keys holds. keys:
the real keys before the shift, by key number; fn: the function of a key number. -/
def keysHold (S : Public) (theta alpha : E) (keys : Nat → E) (fn : Nat → Nat) : Bool :=
  let bits := S.firstBits
  let z := somePoint bits
  let run := fun (i : Nat) => S.padding.find? fun p => p.part == 0 && inRun p i
  let leaf := fun (i : Nat) =>
    match run i with
    | some p => subE alpha (rowAt S theta p.row)
    | none => subE alpha (addE (keys i) (mulE (natE (fn i)) theta))
  let value := (List.range (2 ^ bits)).foldl
    (fun r i => addE r (mulE (eqWeight z i oneE) (leaf i))) zeroE
  let k := keysOf S theta alpha 0 ⟨z, [], value⟩
  ((List.range (2 ^ bits)).all fun i =>
    k.weights.entry i == if (run i).isSome then zeroE else eqWeight z i oneE) &&
  (List.range (2 ^ bits)).foldl (fun r i => addE r (mulE (k.weights.entry i) (keys i))) zeroE
    == k.target

#guard keysHold one zeroE (E.mk3 77 1 2) (fun i => n (UInt64.ofNat (i * i + 1))) fun _ => 0
#guard keysHold two (E.mk3 9 8 7) (E.mk3 77 1 2) (fun i => n (UInt64.ofNat (i * i + 1)))
  fun i => i % 2

#guard byVariable [n 10, n 11, n 12] [2, 0, 1] == [n 11, n 12, n 10]
#guard orderBeginning [0, 1] 4 == [0, 1, 3, 2] && defaultOrder 3 == [2, 1, 0]
#guard liveBlocks 3 == [(0, 1), (2, 0)] && liveBlocks 7 == [(0, 2), (4, 1), (6, 0)]
#guard liveBlocks 4 == [(0, 2)]

/-- A vector on mu plane variables and d table variables, cut to one block of planes, has the
vector's entries at that block's planes: entry j + 2^bits t of the part is entry
first + j + 2^mu t of the vector. -/
def onBlockFits (mu d : Nat) (block : Nat × Nat) : Bool :=
  let v := Tensor.eq (somePoint (mu + d)) (n 5)
  let part := onBlock v mu block
  part.vars == block.2 + d &&
  (List.range (2 ^ d)).all fun t => (List.range (2 ^ block.2)).all fun j =>
    part.entry (j + 2 ^ block.2 * t) == v.entry (block.1 + j + 2 ^ mu * t)

-- every block of 7 real planes among 8, and of 3 among 4
#guard (liveBlocks 7).all (onBlockFits 3 2) && (liveBlocks 3).all (onBlockFits 2 2)

/-- The weights on all keys, cut to the own key vector of the function that holds a block of tree
numbers: entry (y - first) + 2^logTrees x of the part is entry y + 2^g x of the weights. -/
def weightsFit (S : Public) (b : KeyBlock) : Bool :=
  let v := Tensor.eq (somePoint S.firstBits) (n 7)
  let own := weightsOfBlock S (Form.ofTensor v) b
  (List.range (2 ^ (S.firstBits - S.g))).all fun x => (List.range (2 ^ b.logTrees)).all fun y =>
    own.entry (y + 2 ^ b.logTrees * x) == v.entry (b.first + y + 2 ^ S.g * x)

#guard two.keys.all (weightsFit two)

/-- A statement for the runs below: message 0 has one main row for the multiplicities and one mask
row, and is the one member of group 0; message 1 has one mask row. Both have been sampled. -/
def statement (S : Public) : Statement where
  codes := { base := #[⟨12, 2 ^ (S.mu + S.d), 4⟩], mask := #[⟨12, 1024, 4⟩] }
  oracles := #[
    { shape := { code := 0, mainRows := 1, maskRows := 1 }, sampled := true, groups := [0],
      ledger := some { next := 0, left := 1000, rows := 1, logRows := 0 } },
    { shape := { maskRows := 1 }, sampled := true,
      ledger := some { next := 0, left := 1000, rows := 1, logRows := 0 } }]
  groups := #[{ code := 0, members := #[0], kept := #[false] }]

/-- A round as data that can be compared. -/
def lineOf (r : Fmt.Round) : Fmt.Entry × Fmt.Kind × List Fmt.Item := (r.entry, r.kind, r.items)

/-- The block, followed by a look at how many entries the two ledgers have left. -/
def block (S : Public) (second : Bool) : Blk (Nat × Nat) := do
  let _ ← verify S (fun row v => row.add 0 .main v) 0 0 (if second then some 1 else none)
  let a ← Blk.oracle 0
  let b ← Blk.oracle 1
  pure ((a.ledger.map (·.left)).getD 0, (b.ledger.map (·.left)).getD 0)

/-- The dry run goes through on the entries of Lkp.roundsOf, which shows that names and numbers of
draws agree; its kinds and items are those of Lkp.roundsOf; and it takes the announced numbers of
mask entries. The entries themselves come back as they were handed in. -/
def dryFits (S : Public) (second : Bool) : Bool :=
  let want := roundsOf 0 S
  match (block S second).dryRun { entries := want.map (·.entry), st := statement S } with
  | none => false
  | some (got, left) =>
    got.map (fun r => lineOf r.1) == want.map lineOf &&
    left == (1000 - (allMasks S - if second then keyMasks S else 0),
      1000 - (if second then keyMasks S else 0))

#guard allMasks one == 74 && keyMasks one == 4
#guard dryFits one true
#guard dryFits one false
#guard dryFits two true
#guard dryFits two false

/-- The dry run of the block fails on these public inputs and this statement. -/
def dryFails (S : Public) (T : Statement) : Bool :=
  ((block S true).dryRun { entries := (roundsOf 0 S).map (·.entry), st := T }).isNone

/-- The statement of the first example with the sample of message number o not answered. -/
def notSampled (o : Nat) : Statement :=
  let T := statement one
  { T with oracles := T.oracles.modify o fun x => { x with sampled := false } }

-- public inputs that are not well-formed
#guard dryFails { one with parts := [2, 2] } (statement one)
-- the sample of the message that is read and gives mask entries, or of the second message that
-- gives mask entries, is not answered
#guard dryFails one (notSampled 0) && dryFails one (notSampled 1)
-- a row reads the main table of a message that the public inputs do not declare as read
#guard dryFails { one with readFrom := [1] } (statement one)

/-! ## A whole run on the messages of an honest prover

The prover below is written from the definitions: it builds both trees, and computes every round's
polynomial by summing the masked summand over the cube and interpolating. It keeps the verifier's
books with the pure functions of Lkp.lean and Psc.lean, so what the test shows is this: on these
messages every row that the block leaves holds for the prover's bits and mask entries, and every
claim on the keys holds for the prover's keys; and after the first element sent in a round is
changed, whichever round it is, some row or claim fails. -/

namespace Hon

/-- Made-up elements: no randomness, only values without special structure. None is 0. -/
def el (s : Nat) : E :=
  E.mk3 (UInt64.ofNat (s * s * 1000003 + 7 * s + 11)) (UInt64.ofNat (s * 998244353 + 5))
    (UInt64.ofNat (s * s * s + 13))

/-- The prover's mask entries. -/
def maskAt (t : Slot) : E := el (5000 + 1000 * t.oracle + t.index)

/-- The value of a mask form. -/
def formAt (m : MaskForm) : E := m.foldl (fun r t => addE r (mulE t.2 (maskAt t.1))) zeroE

/-- The multilinear extension of a table at a point; variable t belongs to bit t of the index. -/
def mle (table x : List E) : E := (x.foldl (fun l c => halve c l) table).headD zeroE

/-- The sum of two polynomials, given by their coefficients. -/
def addP : List E → List E → List E
  | a :: as, b :: bs => addE a b :: addP as bs
  | [], bs => bs
  | as, [] => as

/-- The divided differences of the values at the nodes 0, 1, 2 and so on. -/
def diffs (values : Array E) : Array E :=
  (List.range (values.size - 1)).foldl (fun v s0 =>
    let step := invE (natE (s0 + 1))
    (List.range (v.size - (s0 + 1))).foldl (fun v k =>
      let i := v.size - 1 - k
      v.setIfInBounds i (mulE (subE (v.getD i zeroE) (v.getD (i - 1) zeroE)) step)) v) values

/-- The coefficients of the polynomial that takes the listed values at 0, 1, 2 and so on. -/
def fromValues (values : List E) : List E :=
  let dd := diffs values.toArray
  (List.range values.length).reverse.foldl (fun g i =>
    addP [dd.getD i zeroE] (addP (zeroE :: g) (g.map fun c => negE (mulE (natE i) c)))) []

#guard fromValues [n 1, n 6, n 17, n 34] == [n 1, n 2, n 3, n 0]

/-- The sum over variables under equality weights at the listed points. -/
def sumW : List E → (List E → E) → E
  | [], g => g []
  | z :: zs, g =>
    addE (mulE (subE oneE z) (sumW zs fun xs => g (zeroE :: xs)))
      (mulE z (sumW zs fun xs => g (oneE :: xs)))

/-- What the prover carries along: the rounds so far, a counter for the verifier's elements, and
the next free mask entry of each of the two messages. -/
structure P where
  /-- the rounds so far -/
  rvs : List Fmt.RoundView := []
  /-- the counter -/
  tick : Nat := 0
  /-- the next free entry of message 0 -/
  own : Nat := 0
  /-- the next free entry of message 1 -/
  key : Nat := 0

/-- The prover's steps. -/
abbrev PM : Type → Type := StateM P

/-- A round: what is sent, and how many elements are drawn. Returns these. -/
def round (sent : List E) (draws : Nat) : PM (List E) := fun s =>
  let d := (List.range draws).map fun i => el (s.tick + i)
  (d, { s with
    rvs := s.rvs ++ [⟨sent.map fun x => Fmt.ItemValue.e x.triple, ⟨d.map E.triple, [], [], none⟩⟩]
    tick := s.tick + draws })

/-- Sends the elements; one element is drawn after them and returned. -/
def roundOne (sent : List E) : PM E := do
  pure ((← round sent 1).headD zeroE)

/-- The fresh mask entries of a sumcheck, as the block takes them. -/
def freshP (second : Bool) (count : Nat) (lastOfKeys : Bool) : PM (List Slot) := fun s =>
  if lastOfKeys && second then
    (((List.range (count - 2)).map fun i => ⟨0, s.own + i⟩) ++
        [⟨1, s.key⟩, ⟨1, s.key + 1⟩],
      { s with own := s.own + (count - 2), key := s.key + 2 })
  else ((List.range count).map fun i => ⟨0, s.own + i⟩, { s with own := s.own + count })

/-- The rounds of the variables. H: the masked summand on all variables. zs: the weights' points.
gone: the challenges so far. Returns what was sent with each challenge. -/
def roundsP (H : List E → E) : List E → List Nat → List E → PM (List (List E × E))
  | _ :: zs, d :: ds, gone => do
    let q := fromValues ((List.range d).map fun node =>
      sumW zs fun rest => H (gone ++ natE node :: rest))
    let g ← roundOne (q.drop 1)
    let later ← roundsP H zs ds (gone ++ [g])
    pure ((q.drop 1, g) :: later)
  | _, _, _ => pure []

/-- One sumcheck under equality weights. maps: the summand's maps as functions of a point given
round by round, the shown ones first. Returns what the verifier computes from the messages. -/
def pscP (second : Bool) (c : Psc.Claim) (S : Psc.Summand) (maps : List (List E → E))
    (lastOfKeys : Bool := false) : PM Psc.Out := do
  let fr ← freshP second (Psc.masksOf c S) lastOfKeys
  let vars := Psc.varsOf c S
  let zs := vars.map fun w => w.moment.getD 1 zeroE
  let k := c.vars.length
  let w := (fr.take (Psc.hidingEntries vars)).map maskAt
  let inner := (fr.drop (Psc.hidingEntries vars)).map maskAt
  let U := fun (p : List E) => Psc.dot (Psc.hidingForm vars p) w
  let mu := sumW zs U
  let eps ← roundOne [mu]
  let H := fun (p : List E) =>
    let x := p.take k
    let y := (p.drop k).headD zeroE
    let all := maps.map fun m => m x
    let shown := ((all.take S.shown).zip inner).map fun q => addE q.1 (mulE q.2 y)
    let a := S.coeffs x shown
    addE (U p) (mulE eps (addE (addE (a.headD zeroE) (Psc.dot (a.drop 1) (all.drop S.shown)))
      (formAt c.masks)))
  let rounds ← roundsP H zs (vars.map (·.d)) []
  let point := (rounds.map (·.2)).take k
  let beta := (rounds.map (·.2)).getLastD zeroE
  let values := (((maps.take S.shown).map fun m => m point).zip inner).map fun q =>
    addE q.1 (mulE beta q.2)
  if S.shown != 0 then
    discard (round values 0)
  pure ((Psc.run c S fr ⟨mu, eps, rounds, values⟩).getD default)

/-- The level above a level of a product tree: entry i times entry i + half the length. -/
def above (l : List E) : List E :=
  ((l.take (l.length / 2)).zip (l.drop (l.length / 2))).map fun p => mulE p.1 p.2

/-- The levels of a tree, from the level reached after the given number of steps up, down to the
leaves. -/
def levelsOf : Nat → List E → List (List E)
  | 0, l => [l]
  | k + 1, l => levelsOf k (above l) ++ [l]

/-- The prover's side of Lkp.levelChain. tree: the levels below the one that the claim is on. -/
def chainP (S : Public) (second keys : Bool) (more : Nat) :
    List (List E) → Nat → PointClaim → PM PointClaim
  | [], _, c => pure c
  | next :: tree, l, c => do
    let variables := more + l
    let lastOfKeys := keys && tree.isEmpty
    let order :=
      if lastOfKeys then orderBeginning S.lastKeyLevelOrder variables else defaultOrder variables
    let half := next.length / 2
    let o ← pscP second
      { vars := order.map fun t => Psc.Weight.equality (c.point.getD t zeroE) 3
        masks := c.masks
        target := c.value }
      summandProduct
      [fun p => mle (next.take half) (byVariable p order),
       fun p => mle (next.drop half) (byVariable p order)] lastOfKeys
    let rho ← roundOne []
    match o.ends.map fun x => { x with point := byVariable x.point order } with
    | [e0, e1] => chainP S second keys more tree (l + 1) (lineAt rho e0 e1)
    | _ => pure c

/-- The later steps of the tie. powers: the partial products of the tie from the third on; roots:
the planes' roots from plane 1 on. -/
def tieP (second : Bool) : List E → List E → PointClaim → PM (List PointClaim)
  | p :: ps, g :: gs, onPower => do
    let o ← pscP second ((Psc.Claim.atPoint onPower []).getD default) summandTie
      [fun _ => p, fun _ => g]
    let rest ← tieP second ps gs (o.ends.headD default)
    pure (o.ends.getD 1 default :: rest)
  | _, _, onPower => pure [onPower]

/-- From the product of the parts' roots to each root. roots: those that are left. -/
def partsP (second : Bool) : List E → PointClaim → PM (List PointClaim)
  | z :: z2 :: zs, onRoot => do
    let o ← pscP second ((Psc.Claim.atPoint onRoot []).getD default) summandProduct
      [fun _ => z, fun _ => (z2 :: zs).foldl mulE oneE]
    let rest ← partsP second (z2 :: zs) (o.ends.getD 1 default)
    pure (o.ends.headD default :: rest)
  | _, onRoot => pure [onRoot]

/-- The key trees of all parts. -/
def keyTreesP (S : Public) (second : Bool) :
    List (List (List E)) → List PointClaim → PM (List PointClaim)
  | t :: ts, c :: cs => do
    let x ← chainP S second true 0 (t.drop 1) 0 c
    let rest ← keyTreesP S second ts cs
    pure (x :: rest)
  | _, _ => pure []

/-- The run of padding in which key number i of a part lies, if any. -/
def runOf (S : Public) (part i : Nat) : Option Padding :=
  S.padding.find? fun p => p.part == part && inRun p i

/-- The bits of the multiplicities. keyRow: the number of the row that a real key equals. -/
def bitsOf (S : Public) (keyRow : Nat → Nat → Nat) : List E :=
  (List.range (2 ^ (S.mu + S.d))).map fun idx =>
    let count := (((List.range S.parts.length).zip S.parts).map fun p =>
      ((List.range (2 ^ p.2)).filter fun i =>
        (runOf S p.1 i).isNone && keyRow p.1 i == idx / 2 ^ S.mu).length).sum
    if count.testBit (idx % 2 ^ S.mu) then oneE else zeroE

/-- The prover's side of Lkp.run. -/
def runP (S : Public) (second : Bool) (keyRow : Nat → Nat → Nat) : PM Unit := do
  let theta ← if S.shifted then roundOne [] else pure zeroE
  let alpha ← roundOne []
  let a := factorOf S theta alpha
  let bits := bitsOf S keyRow
  let keyTrees := ((List.range S.parts.length).zip S.parts).map fun p =>
    levelsOf p.2 ((List.range (2 ^ p.2)).map fun i =>
      subE alpha (rowAt S theta (((runOf S p.1 i).map (·.row)).getD (keyRow p.1 i))))
  let table := levelsOf S.d (((List.range bits.length).zip bits).map fun p =>
    addE oneE (mulE p.2 (subE (subE alpha oneE) (rowAt S theta (p.1 / 2 ^ S.mu)))))
  let G := (table.headD []).take S.planes
  let powers := G.foldr (fun g l =>
    match l with
    | [] => [g]
    | p :: _ => mulE (mulE p p) g :: l) []
  let roots := keyTrees.map fun t => (t.headD []).headD zeroE
  let first ← pscP second { vars := [], masks := [], target := zeroE } (summandTieFirst a)
    [fun _ => mulE a (powers.headD zeroE), fun _ => powers.getD 1 zeroE, fun _ => G.headD zeroE]
  let later ← tieP second (powers.drop 2) (G.drop 1) (first.ends.getD 1 default)
  let onRoots ← partsP second roots (first.ends.headD default)
  let r ← round [] S.mu
  let onTop := joinPlanes S r (first.ends.getD 2 default :: later)
  let _ ← keyTreesP S second keyTrees onRoots
  let onTable ← chainP S second false S.mu (table.drop 1) 0 onTop
  let all := S.mu + S.d
  let order := defaultOrder all
  let bitsMap := fun (p : List E) => mle bits (byVariable p order)
  let _ ← pscP second
    { vars := order.map fun t =>
        Psc.Weight.equality (onTable.point.getD t zeroE) (if t < S.mu then 2 else 3)
      masks := onTable.masks
      target := onTable.value }
    (summandLeaves S theta alpha order) [bitsMap]
  let zeta ← round [] all
  let _ ← pscP second
    { vars := order.map fun t => Psc.Weight.equality (zeta.getD t zeroE) 3
      masks := []
      target := zeroE }
    summandBits [bitsMap]

/-- The row holds for the prover's bits and mask entries. -/
def rowHolds (S : Public) (bits : List E) (r : Row) : Bool :=
  let main := ((List.range bits.length).zip bits).foldl
    (fun s p => addE s (mulE (r.coefficient 0 .main p.1) p.2)) zeroE
  (List.range (allMasks S)).foldl
    (fun s i => addE s (mulE (r.coefficient 0 .mask i) (maskAt ⟨0, i⟩))) main == r.target

/-- The claim on a part's keys holds for the prover's keys as they are before the shift. -/
def keysHoldAt (S : Public) (keyRow : Nat → Nat → Nat) (part : Nat) (k : Keys) : Bool :=
  (List.range (2 ^ k.point.length)).foldl
    (fun s i => addE s (mulE (k.weights.entry i) (rowAt S zeroE (keyRow part i))))
    (formAt k.masks) == k.target

/-- Adds 1 to the first element that is sent in round number at. -/
def alter (rvs : List Fmt.RoundView) (at_ : Nat) : List Fmt.RoundView :=
  ((List.range rvs.length).zip rvs).map fun p =>
    if p.1 == at_ then
      match p.2.vals with
      | .e x :: rest => { p.2 with vals := .e (addE (E.ofTriple x) oneE).triple :: rest }
      | _ => p.2
    else p.2

/-- The rounds of the prover's run. -/
def rvsOf (S : Public) (second : Bool) (keyRow : Nat → Nat → Nat) : List Fmt.RoundView :=
  let r : Unit × P := (runP S second keyRow).run {}
  r.2.rvs

/-- Runs the block on the prover's rounds, with round number at altered if one is named. Returns
whether the block went through, and whether there are as many rows and claims on the keys as there
should be and all of them hold. -/
def trial (S : Public) (second : Bool) (keyRow : Nat → Nat → Nat) (at_ : Option Nat) :
    Bool × Bool :=
  let rvs := rvsOf S second keyRow
  let checks := ((roundsOf 0 S).filter fun r => r.entry.name == "PSC epsilon").length
  let b : Blk (Out × Array Row) := do
    let o ← verify S (fun row v => row.add 0 .main v) 0 0 (if second then some 1 else none)
    pure (o, (← Blk.group 0).rows)
  match b.walk { entries := (roundsOf 0 S).map (·.entry), st := statement S } []
      ((at_.map (alter rvs)).getD rvs) with
  | some ((o, rows), []) =>
    (true, rows.size == checks + 2 && o.keys.length == S.parts.length &&
      rows.all (rowHolds S (bitsOf S keyRow)) &&
      ((List.range o.keys.length).zip o.keys).all fun p => keysHoldAt S keyRow p.1 p.2)
  | _ => (false, false)

/-- Keys for the first example: any rows of the one table. -/
def rowsOne (part i : Nat) : Nat := (3 * i + part + 1) % 4

/-- Keys for the second example: function 0 has the rows 0 and 1, function 1 the rows 2 and 3. -/
def rowsTwo (_ i : Nat) : Nat := 2 * (i % 2) + (i / 2) % 2

#guard trial one true rowsOne none == (true, true)
#guard trial one false rowsOne none == (true, true)
#guard trial two true rowsTwo none == (true, true)
/-- The numbers of the rounds of the first example's run in which something is sent. -/
def sending : List Nat :=
  let rvs := rvsOf one true rowsOne
  (List.range rvs.length).filter fun i => !(rvs.getD i ⟨[], ⟨[], [], [], none⟩⟩).vals.isEmpty

-- of the 50 rounds, eight send nothing: "LKP", "JOIN", "ZERO" and five "LINE"
#guard (rvsOf one true rowsOne).length == 50 && sending.length == 42
#guard
  let idle := (((List.range 50).zip (roundsOf 0 one)).filter fun p => !sending.contains p.1).map
    (·.2.entry.name)
  idle.length == 8 && (idle.filter (· == "LINE")).length == 5 &&
    ["LKP", "JOIN", "ZERO"].all idle.contains
-- the first element sent in a round changed, for every such round: the block goes through, and a
-- row or a claim on the keys fails
#guard sending.all fun i => trial one true rowsOne (some i) == (true, false)

end Hon

end OnBytes.TestLkp
