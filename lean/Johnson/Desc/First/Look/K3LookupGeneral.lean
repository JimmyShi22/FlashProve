-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3LookupGeneral.lean: the kind of block "lookup", GENERAL IN THE LOOKUP'S NUMBERS:
the text of Johnson/Desc/First/Look/K3Lookup.lean with four numerals made letters, one step more, and one
arm more, so that one text serves the lookups of a proof file's links and the lookups with parts of
a key file. Definitions with code. No theorem.

Why one text. The planner has one routine for the rounds of every lookup (`Params.planLookup`,
OnBytes/Params/Planner.lean:428-446), at a list and four numbers: the keys' parts; d; mu; the number
of real planes; whether there is a shift. The lookups of a proof file's links are that routine at
one part, mu = 5, all 32 planes real (`Params.planForest`, OnBytes/Params/SubRounds.lean:43).
`verify-on-bytes` has two routines for the two files: `Forest.pad` (OnBytes/Model/Look.lean:369-421)
and `Lkp.run` (OnBytes/Iop/Lkp.lean:706-756).

The course, in the order of the rounds: the shift, where there is one; the point alpha; the tie of
the two sides' roots: planes - 1 masked sumchecks without a variable; WITH SEVERAL PARTS: parts - 1
more, from the product of the parts' roots to each root; mu draws, which make the claims on the
planes' roots one claim (a plane that is not real has the public root 1); A PRODUCT TREE FOR EACH
PART of the keys, from the root down; the table side's product trees as one; the sumcheck on its
leaves, left open; mu + d draws; the sumcheck that the bits are bits.

Main names:
  `Face`: the numbers, the orders of the key levels' rounds, THE PADDING AS DATA, and one public
    letter (the factor of a bit in a leaf: the table). `Face.factor`, `Face.count`: the public
    factor and the number of keys that are no padding, both computed from the padding. `Face.slots`,
    `Face.lins`: how many hidden values the rounds take, how many claims they leave. `Face.ok`: the
    tests on these numbers. `Face.size`: the planner's record.
  `tieG`, `partsG`, `keysG`, `messagesG f`: **the lookup's rounds, heard in order**; `HeardG`: what
    was heard: for each part the point and the form that its key tree leaves.
  `faceOf h`, `toHeard h`: the face of a proof file's lookup of shape h, and from what was heard to
    `verify-on-bytes`'s record: that at these `messagesG` gives what `messages h` (K3Lookup.lean)
    gives is not shown here.
  `PlaneClaim`, `eqPairs`, `planesG`: the three claims that read the planes of the counts' bits.
  `entriesG`, `PG`, `PG.entries`, `PG.planOk`, `SeatG`, `hearG`, `doneG`, `lookupKind`: the rounds by
    the planner's own routine; a place's public parameters (no entry among them); the seat; the test
    for whoever closes the link; the kind.

The ledger. A hidden value is a number (a slot) in the order of sending; a claim is a linear form
over slots (`Model.Aff`); the ledger (`Model.Fork`) counts the slots and keeps what was shown under
each. In a proof file slot j is entry j of the sub-proof's mask row. In a key file the hidden values
are mask entries of oracle messages, taken in the same order; WHICH MESSAGE'S WHICH ENTRY SLOT j IS,
IS A PUBLIC TABLE OF THE SEAT'S, not of this text: the two end values of each part's last key level
lie in another message than the rest (`Lkp.fresh`, OnBytes/Iop/Lkp.lean:517-525).

Limits: those of K3Lookup.lean, and: NO THEOREM SAYS THAT `messagesG` AT `faceOf h`, WITH `toHeard h`,
GIVES WHAT `messages h` GIVES, or that at a key file's numbers it gives what `Lkp.run` gives: runs
alone hold it against these: at the 10 and 50 lookups of two stored proof files (value and ledger),
and at the two lookups of each of two stored key files (every claim that reads hidden values alone
against `verify-on-bytes`'s rows; the forms on the parts' keys through `keysOf`). `Lkp.run`
makes of each part's form a claim on that part's keys with the padding's and the shift's shares
taken out (`keysOf`), and asks that the messages read have had their samples answered: neither is
here: the first is the caller's, the second `before`'s. THE HEARING LAYS THREE DEBTS IN THE LEDGER:
"objects" and "planes" mark the first two; the third stands open until the caller marks it. IN WHICH
ORDER, AND UNDER WHICH SIGN, THE CLAIMS BECOME ROWS OF A GROUP IS NOT THIS TEXT'S MATTER: the
program lays the leaves' row in front of the bits' (Johnson/Desc/First/Look/K3Key.lean). At a proof
file's link the run "planes" is that of Johnson/Desc/First/Look/K3Runs.lean, whose caller
reads the planes column by column. `Face.ok` does not ask the planner's two bounds on sizes;
`PG.planOk` does, through `PG.entries`. A PADDING KEY IS A FUNCTION OF THE SHIFT, AND `leaf` A
LETTER: THAT EACH PADDING KEY IS A ROW OF THE TABLE, AND THAT `leaf` IS THAT TABLE'S, IS THEIR
MAKER'S MATTER: nothing here can test it, and a padding key that is in no row lets that key in. WHAT
IS TAKEN OUT OF A PART'S CLAIM FOR ITS PADDING IS THE CALLER'S: so the padding is said twice:
here and in the caller's files. THE TESTS OF THE KEY FILE'S OWN ITEM "ranges" (`Wf.publicOk`,
`lookupOk`, `fitsMatrix`, `coversAllRows`; `Lkp.Public.keysOK`, `tablesOK`, `paddingOK`) ARE NOT
HERE: the face has no datum for them: THE CALLER'S, on the plan. That the seat's table of homes is
one-to-one over both lookups and what follows, skips the entries that mask answers, and has room,
is left to the seat's files. `ofNat` lays a number into the field: right below the prime alone.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Lookup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Call Aff Psc)
open OnBytes.Model (eqTab orderDefault ofNat)
open OnBytes.Model.Forest (Shape Heard tableAt joinedTableAt callWeight padKeyOf)
open First.Prod (wholeStandIn Carried)

/-! ## The numbers -/

/-- **A lookup's public face**: numbers, orders and one public function. -/
structure Face where
  /-- several functions share the table: a shift is drawn -/
  shifted : Bool
  /-- a count has 2 ^ mu places for bits -/
  mu : Nat
  /-- how many of these (the planes) are real: the first ones -/
  planes : Nat
  /-- part i of the keys has 2 ^ parts[i] keys -/
  parts : List Nat
  /-- the table has 2 ^ d rows -/
  d : Nat
  /-- for part i, for its key tree's level with m variables: the bit that each round fixes -/
  orders : Nat → Nat → List Nat
  /-- THE PADDING, SAID ONCE: runs of places that hold a public key and are not counted: how many
  places, and the key, from the shift. The public factor and the number of keys that are no padding
  are computed from it -/
  padding : List (Nat × (E → E))
  /-- from the shift, alpha and the leaves' point (a coordinate a round, in the rounds' order):
  alpha - 1 - the table's row there: the factor of a bit in a leaf of the table side -/
  leaf : E → E → Array E → E

/-- The public factor: the product of alpha - key over all places of padding. -/
def Face.factor (f : Face) (theta alpha : E) : E :=
  f.padding.foldl (fun a p => mulE a (powE (subE alpha (p.2 theta)) p.1)) oneE

/-- The number of all keys, padding counted. -/
def Face.allKeys (f : Face) : Nat := (f.parts.map (2 ^ ·)).sum

/-- The number of keys that are no padding. -/
def Face.count (f : Face) : Nat := f.allKeys - (f.padding.map (·.1)).sum

/-- The number of hidden values that the rounds take: the tie's first sumcheck, its later ones, the
parts', the key levels', the table levels', the leaves', the bits'. -/
def Face.slots (f : Face) : Nat :=
  7 + 6 * (f.planes - 2) + 5 * (f.parts.length - 1) +
    (f.parts.map fun v => ((List.range v).map fun k => 2 * k + 5).sum).sum +
    ((List.range f.d).map fun l => 2 * (f.mu + l) + 5).sum +
    (1 + f.mu + 2 * f.d) + (1 + 2 * (f.mu + f.d) + 2 + 1)

/-- The number of claims that the rounds leave and that read hidden values alone. -/
def Face.lins (f : Face) : Nat :=
  (f.planes - 1) + (f.parts.length - 1) + f.parts.sum + f.d + 1

/-- The tests on the numbers: mu from 1 to 6; from 2 to 2 ^ mu real planes; a part at least, and
each of a bit at least; several parts only without a shift; not all keys are padding; and every
level's order of every part's key tree is a list of that level's variables, each once. (The table
side goes by `orderDefault`, which is such a list at every number.) -/
def Face.ok (f : Face) : Bool :=
  decide (1 ≤ f.mu) && decide (f.mu ≤ 6) && decide (2 ≤ f.planes) &&
    decide (f.planes ≤ 2 ^ f.mu) && !f.parts.isEmpty && (f.parts.all fun v => decide (1 ≤ v)) &&
    (decide (f.parts.length ≤ 1) || !f.shifted) &&
    decide ((f.padding.map (·.1)).sum < f.allKeys) &&
    f.parts.zipIdx.all fun x => First.Prod.runOk 0 x.1 0 (f.orders x.2)

/-- The planner's record of these numbers. -/
def Face.size (f : Face) : Params.LookupSize :=
  { v := f.parts.headD 0, d := f.d, mu := f.mu, shifted := f.shifted
    live := if f.planes == 2 ^ f.mu then 0 else f.planes
    parts := if f.parts.length == 1 then [] else f.parts }

/-! ## DECIDES -/

/-- Z = a G_0 G_1^2 ... G_(w-1)^(2^(w-1)), by squaring and multiplying: w - 1 masked sumchecks
without a variable (`tie`, K3Lookup.lean, at w planes). Returns the claims, the slot of Z and the w slots
of the G_j. -/
def tieG (w : Nat) (a : E) : Fl (Array Aff × Nat × Array Nat) := do
  let sq (x y : E) := mulE (mulE x x) y
  let x ← wholeStandIn (Aff.ofConst zeroE) [] 3 3 fun v =>
    subE (v.getD 0 zeroE) (mulE a (sq (v.getD 1 zeroE) (v.getD 2 zeroE)))
  let s ← (List.range (w - 2)).foldlM
    (fun (s : Array Aff × Nat × Array Nat) _ => do
      let y ← wholeStandIn (Aff.slot s.2.1) [] 3 2 fun v => sq (v.getD 0 zeroE) (v.getD 1 zeroE)
      pure (s.1.push y.row, y.sEnd, s.2.2.push (y.sEnd + 1)))
    (#[x.row], x.sEnd + 1, #[x.sEnd + 2])
  pure (s.1, x.sEnd, s.2.2.push s.2.1)

/-- **From the product of the parts' roots to each root.** C: the form of the product of the roots
that are left. Each step is a masked sumcheck without a variable that shows the next part's root and
the product of the others, and claims that C is their product. The number counts the steps that are
left. Returns the rows, and a form for each part's root. -/
def partsG : Nat → Array Aff → Aff → Fl (Array Aff × List Aff)
  | 0, rows, C => pure (rows, [C])
  | n + 1, rows, C => do
    let w ← wholeStandIn C [] 2 2 fun v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)
    let x ← partsG n (rows.push w.row) (Aff.slot (w.sEnd + 1))
    pure (x.1, Aff.slot w.sEnd :: x.2)

/-- **The parts' key trees, one after the other**, each from its root down. The parts with their
numbers; the forms of their roots; the rows so far. Returns the rows, and for each part the point
and the form that its tree leaves. -/
def keysG (f : Face) : List (Nat × Nat) → List Aff → Array Aff →
    Fl (Array Aff × List (Array E × Aff))
  | x :: xs, C :: Cs, rows => do
    let k ← First.Prod.run 0 x.1 (f.orders x.2) { rows := rows, point := #[], form := C }
    let y ← keysG f xs Cs k.rows
    pure (y.1, (k.point, k.form) :: y.2)
  | _, _, rows => pure (rows, [])

/-- What was heard. -/
structure HeardG where
  /-- the shift; 0 where there is none -/
  theta : E
  alpha : E
  /-- the public factor -/
  a : E
  /-- the claims that read hidden values alone -/
  rows : Array Aff
  /-- the sumcheck on the table side's leaves, left open: the caller closes it -/
  leaves : Psc
  /-- the slot of the bits' end value -/
  sBit : Nat
  /-- for each part: its key tree's last point, THE HIGHEST VARIABLE FIRST, and the form on
  alpha - key there -/
  keys : List (Array E × Aff)
  /-- the leaves' point; the bits' point -/
  zb0 : Array E
  zb1 : Array E
  owedObjects : Nat
  owedPlanes : Nat
  owedJoin : Nat

/-- **The lookup's rounds, heard in order.** -/
def messagesG (f : Face) : Fl HeardG := do
  let m := f.mu + f.d
  let slot0 ← Fl.slot
  let owedObjects ← Fl.owe "look-up-mask-claims"
  let owedPlanes ← Fl.owe "look-up-plane-claims"
  let owedJoin ← Fl.owe "look-up-join"
  -- the shift between the functions, where there is one; the point at which the sides are compared
  let theta ← if f.shifted then Fl.answer .lkpShift else pure zeroE
  let alpha ← Fl.answer .lkp
  let a := f.factor theta alpha
  -- the two sides' roots are tied
  let (rows, sZ, sG) ← tieG f.planes a
  -- from the product of the parts' roots to each
  let (rows, roots) ← partsG (f.parts.length - 1) rows (Aff.slot sZ)
  -- one claim on the planes' roots, at mu drawn coordinates; a plane that is not real has root 1
  let rhoT := (← Fl.point .lkpPlanes f.mu).reverse
  let ej := eqTab rhoT
  let cT := (List.range (2 ^ f.mu)).foldl
    (fun (c : Aff) j =>
      if j < f.planes then Aff.addMul c (Aff.slot (sG.getD j 0)) (ej.getD j zeroE)
      else c + Aff.ofConst (ej.getD j zeroE)) (Aff.ofConst zeroE)
  -- the key side: a product tree for each part
  let (rows, keys) ← keysG f f.parts.zipIdx roots rows
  Fl.must (keys.length == f.parts.length)
  -- the table side's product trees as one, from the mu coordinates down: d levels
  let table ← First.Prod.run f.mu f.d orderDefault { rows := rows, point := rhoT, form := cT }
  Fl.must (table.point.size == m)
  -- a leaf of the table side is 1 + b (alpha - 1 - row): a sumcheck whose claim the caller closes
  let leaves ← Fl.pscBegin table.form
  let (zb0, leaves) ← Fl.roundsIn .eq leaves
    ((List.range m).map fun j => (table.point.getD j zeroE, if j < f.d then 2 else 1))
  -- the bits are bits: b^2 - b sums to 0 against the equality weights of a drawn point
  let r5 := (← Fl.point .zero m).reverse
  let bits ← wholeStandIn (Aff.ofConst zeroE) r5.toList 2 1 fun x =>
    subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)
  let rows := table.rows.push bits.row
  -- two counts of its own: no input can trip them
  Fl.must ((← Fl.slot) == slot0 + f.slots && rows.size == f.lins)
  pure {
    theta := theta, alpha := alpha, a := a, rows := rows, leaves := leaves, sBit := bits.sEnd,
    keys := keys, zb0 := zb0, zb1 := (bits.challenges.take m).toArray,
    owedObjects := owedObjects, owedPlanes := owedPlanes, owedJoin := owedJoin }

/-! ## CLAIMS on the planes of the counts' bits -/

/-- A claim that reads the planes: lead + scalar * <v, the bits> = 0, where v is the vector of
product form with these pairs (its halves at 0 and at 1), a pair a variable, the lowest variable
first: the mu variables of a plane's number, then the d variables of a row's. -/
structure PlaneClaim where
  lead : Aff
  scalar : E
  pairs : List (E × E)

/-- The equality vector's pairs at a point that is given a coordinate a round, the highest variable
first. -/
def eqPairs (m : Nat) (z : Array E) : List (E × E) :=
  (List.range m).map fun t =>
    let x := z.getD (m - 1 - t) zeroE
    (subE oneE x, x)

/-- **The three claims on the planes**: what the leaves' sumcheck left, with the planes' value at
its point; the planes' value at the bits' sumcheck's point is what that sumcheck has shown; the
counts add up to the number of keys that are no padding. It closes the leaves' sumcheck: the
coefficients of its hiding polynomial are put under their slots here. -/
def planesG (f : Face) (g : HeardG) : Fl (List PlaneClaim) := do
  let m := f.mu + f.d
  let (row, _) ← Fl.pscRow g.leaves oneE
  pure [
    ⟨row, mulE g.leaves.eps (f.leaf g.theta g.alpha g.zb0), eqPairs m g.zb0⟩,
    ⟨Aff.slot g.sBit, subE zeroE oneE, eqPairs m g.zb1⟩,
    ⟨Aff.ofConst (subE zeroE (ofNat f.count)), oneE,
      ((List.range f.mu).map fun t => (oneE, ofNat (2 ^ 2 ^ t))) ++
        List.replicate f.d (oneE, oneE)⟩]

/-! ## At a proof file's link -/

/-- The face of a proof file's lookup of shape h: one part, 32 planes, all real, a shift. -/
def faceOf (h : Shape) : Face :=
  { shifted := true, mu := 5, planes := 32, parts := [h.v], d := h.d
    orders := fun _ => keyOrders h
    padding := (h.emptyKeys, fun theta => padKeyOf h theta 0) ::
      (List.range h.NT).map fun y =>
        (h.pub.getD y 0, fun theta => padKeyOf h theta (h.callOf.getD y 0))
    leaf := fun theta alpha zb0 =>
      let tT := h.calls.map fun k => tableAt k (zb0.extract (h.kT - k.k) h.kT)
      subE (subE alpha oneE) (joinedTableAt h theta tT (zb0.extract h.kT (h.kT + h.cK))) }

/-- From what was heard to `verify-on-bytes`'s record of a lookup of shape h: the calls' points,
weights and tables. Nothing where there is not just one part, or one of that text's two counts on
the calls fails. -/
def toHeard (h : Shape) (g : HeardG) : Option Heard :=
  match g.keys with
  | [(point, form)] =>
    let zx := point.extract 0 h.dT
    let zy := point.extract h.dT point.size
    let zk := (Array.range h.NC).map fun c => zy.extract (h.rK - h.iota.getD c 0) zy.size ++ zx
    if (h.iota.all fun i => decide (i ≤ h.rK)) && ((List.range h.NC).all fun c =>
        (zk.getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0) then
      let tT := h.calls.map fun k => tableAt k (g.zb0.extract (h.kT - k.k) h.kT)
      let row := joinedTableAt h g.theta tT (g.zb0.extract h.kT (h.kT + h.cK))
      some {
        shape := h, theta := g.theta, alpha := g.alpha, a := g.a, rows := g.rows
        leaves := g.leaves, leavesA := subE (subE g.alpha oneE) row, sBit := g.sBit, zx := zx
        zy := zy, e := (Array.range h.NC).map (callWeight h zy), cEnd := form, zb0 := g.zb0
        zb1 := g.zb1, tT := tT, zk := zk, owedObjects := g.owedObjects
        owedPlanes := g.owedPlanes, owedJoin := g.owedJoin }
    else none
  | _ => none

/-! ## The kind -/

/-- The plan's entries of the lookup's rounds, by the planner's own routine. set: the plan's
setting. scope: how often the chain is run. Nothing where the planner refuses. -/
def entriesG (set : Params.Setting) (scope : Params.Scope) (f : Face) : Option (List Fmt.Entry) :=
  match Params.finish set scope (Params.planLookup f.size) with
  | .ok p => some (p.rounds.map (·.entry))
  | .error _ => none

/-- **A place's public parameters**: numbers and public functions alone: NO ENTRY OF THE PLAN, no
declared round. -/
structure PG where
  name : String
  /-- where the block stands: the chain, the link, its number inside the link -/
  chain : Nat
  link : Nat
  piece : Nat
  /-- the plan's setting, and how often the chain is run -/
  set : Params.Setting
  scope : Params.Scope
  face : Face
  /-- the number of the first hidden value that the rounds take -/
  first : Nat
  /-- how many hidden values the ledger has room for -/
  ns : Nat

/-- The plan's entries of the place's rounds: the planner's own, of the numbers. -/
def PG.entries (p : PG) : Option (List Fmt.Entry) := entriesG p.set p.scope p.face

/-- **The tests on the plan alone**: the face's; the planner makes the rounds (so its two bounds
hold: the keys are fewer than 2 ^ planes; the counts' sum cannot wrap); the ledger has room; some
oracle message is named as fixed before the first draw; every guest fits. bits: the number of a
place's bits that a guest may name. -/
def PG.planOk {S Cl : Type} (p : PG) (before : List (Nat × Nat)) (bits : Nat)
    (guests : List (First.Look.Guest S Cl)) : Bool :=
  p.face.ok && p.entries.isSome && decide (p.first + p.face.slots ≤ p.ns) && !before.isEmpty &&
    guests.all (First.Look.Guest.fits bits)

/-- Where the carried record keeps what the kind reads and writes (`Seat`, K3Lookup.lean, at `HeardG`). -/
structure SeatG (S Cl : Type) where
  fork : S → Option Fork
  owed : S → First.Tape.RowsOwed
  put : S → HeardG → Fork → S
  mark : S → Fork → S
  heard : S → Option HeardG
  claim : Aff → Cl
  /-- a claim that reads the planes, as a claim: how the planes are read is the caller's -/
  claimP : S → PlaneClaim → Option Cl

/-- The lookup's messages at a place. Nothing is left over. Nothing where the face fails its tests:
at no part the text would hear, and tie the key side's root to no key. -/
def hearG (p : PG) (F : Fork) (rs : List Fmt.RoundView) : Option (HeardG × Fork) :=
  if p.face.ok then p.entries.bind fun es => First.Tape.flRun {} (messagesG p.face) es F rs
  else none

/-- The debt of that number in the ledger is not yet marked as paid. -/
def unpaidG (F : Fork) (i : Nat) : Bool := ((F.owed[i]?).map (·.added)) != some true

/-- **Nothing of the lookup is left open in the ledger**: FOR WHOEVER CLOSES THE LINK: the count
stands behind the lookup's hidden values; a value lies under each of their slots (so the leaves'
sumcheck was closed); all three debts are marked. At a proof file `verify-on-bytes` asks the like
where a link is closed (`Fork.settle`, OnBytes/Model/Hide.lean:392); at a key file no routine of it
does. -/
def doneG (p : PG) (g : HeardG) (F : Fork) : Bool :=
  decide (p.first + p.face.slots ≤ F.next) &&
    ((List.range p.face.slots).all fun j => F.gotF.getD (p.first + j) false) &&
    [g.owedObjects, g.owedPlanes, g.owedJoin].all fun i => ((F.owed[i]?).map (·.added)) == some true

/-- **The kind "lookup", general in its numbers**: a host. before: the oracle messages that must
have been sent, and have had their samples answered, before the first draw. bits: the number of a
place's bits that a guest may name. guests: other kinds' identities, handed in as functions before
anything is heard, and called late, with the claims. Three runs: "objects": the claims that read
hidden values alone; it marks the first debt. "planes": the three claims on the planes, through the
seat's reader; it marks the second; it is made once. "guests". THE THIRD DEBT (the claims on the
parts' keys: ONE DEBT FOR ALL PARTS: a mark cannot tell eleven claims from twelve) IS THE CALLER'S
TO PAY: what it reads stands in `HeardG.keys`. -/
def lookupKind {S Cl : Type} (seat : SeatG S Cl) (before : List (Nat × Nat)) (bits : Nat)
    (guests : List (First.Look.Guest S Cl)) (p : PG) : Block S Cl :=
  { name := p.name
    place := ⟨p.chain, some p.link, p.piece, .K3⟩
    planOk := p.planOk before bits guests
    rounds := (p.entries.getD []).map fun e => { entry := e }
    oracles := (p.entries.getD []).map fun _ => []
    before := before
    decide := fun s rs _ => do
      let F ← named "K3: no ledger is open" (seat.fork s)
      need "K3: rows are owed in front" (seat.owed s).noneWaits
      need "K3: the ledger's count of slots" (F.next == p.first)
      need "K3: the ledger's room" (F.ns == p.ns)
      let x ← named "K3: the hearing" (hearG p F rs)
      pure (seat.put s x.1 x.2)
    claims :=
      [("objects", fun _ s => do
        let F ← named "K3 objects: no ledger is open" (seat.fork s)
        let g ← named "K3 objects: nothing was heard" (seat.heard s)
        pure (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects))),
       ("planes", fun _ s => do
        let F ← named "K3 planes: no ledger is open" (seat.fork s)
        let g ← named "K3 planes: nothing was heard" (seat.heard s)
        need "K3 planes: they are made once" (unpaidG F g.owedPlanes)
        let x ← named "K3 planes: the leaves' claim" (planesG p.face g F [])
        let l ← named "K3 planes: the caller's reader" (x.1.mapM (seat.claimP s))
        pure (l, seat.mark s (x.2.1.paid g.owedPlanes))),
       ("guests", fun _ s =>
        named "K3 guests: a guest refuses"
          ((guests.mapM fun (g : First.Look.Guest S Cl) => g.form s).map fun l => (l, s)))]
    after := [] }

end VerifiableInference.Desc.K3
