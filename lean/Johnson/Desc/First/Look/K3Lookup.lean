-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Lookup.lean: the kind of block "lookup", in the format of
Johnson/Desc/Block.lean. Definitions with code. No theorem.

A lookup is meant to show that the keys of a group of calls all stand in the calls' tables. A place
of this kind is given public numbers alone (`P`, Johnson/Desc/First/Look/LookKind.lean, with the
tests on them). ROUNDS: the planner's own list for a lookup of the place's shape
(`Params.planForest`, OnBytes/Params/SubRounds.lean:43, over `planLookup`,
OnBytes/Params/Planner.lean:428-446): only field elements are sent and only public coins are drawn.
READS: nothing: no oracle is sent and no column is opened. DECIDES: it hears (`messages`): two
draws; 31 masked sumchecks without a variable; five draws; the grand product twice
(Johnson/Desc/First/Prod/Level.lean); a masked sumcheck; 5 + d draws; a last masked sumcheck; behind
the strict reading of a round (Johnson/Desc/First/Tape/Tape.lean). It is `verify-on-bytes`'s
routine `Forest.pad` (OnBytes/Model/Look.lean:369-421) written out over these parts, as a function
on a sub-proof's ledger and a tape of rounds. CLAIMS: two named runs here: "objects": the linear
claims that the sumchecks left, as they were heard; it marks the first of the three debts that the
hearing lays in the ledger; "guests": other kinds' identities that are tested at coordinates of the
key side's point. In which order they are called is the link's to say.

Main names:
  `planOk p laid guests`: the tests on the plan alone.
  `Seat S Cl`: where the carried record keeps what the kind reads and writes.
  `paddingFactor`, `tie`, `messages h`: **the lookup's rounds, heard in order**.
  `hear p es F rs`: the same at a place: what was heard, and the ledger behind.
  `block seat piece laid before`: **the kind**, a host.

Limits: `decide` tests no equation of the protocol: every sumcheck leaves a claim; a sent value that
is changed is refused nowhere here. Two further runs of claims (on the key side's leaves; on the
planes of the counts' bits) read tables of the calling kind and are not here. That a `P` is that of
the public files is the matter of whoever makes it (`placeAt`). The arm for one call alone
(OnBytes/Model/Look.lean:191: no shift) is not here: `planOk` refuses such a place. The ledger and
what is heard are `verify-on-bytes`'s own records (`Model.Fork`, `Model.Forest.Heard`). THAT A
GUEST'S FORM READS ONLY WHAT IS SENT OR FIXED IN FRONT OF THE FIRST DRAW THAT IT BORROWS IS THE
GUEST'S FILES' TO SHOW: nothing here can test it: what is handed in early is a function; what it
reads is fixed late. That a `Seat`'s six functions fit each other is not asked. A SEAT SERVES ONE
PLACE OF A LINK: a run of claims is called late, behind all that the link hears: two places at one
seat lose the first one's claims, and nothing refuses it. THE LEDGER'S THREE DEBTS
(OnBytes/K/Kc/FlatHear.lean:115-117): the hearing lays them; "objects" marks the first; the other
two (the planes'; the key side's leaves') are marked by whoever adds these claims: the calling kind;
that all are marked is asked by `verify-on-bytes` where a link is closed (`Fork.settle`,
OnBytes/Model/Hide.lean:392); here by the kind that closes the link, if it calls that. `planOk` is
asked by the file's tests on the plan, not by `Block.step`; of its clauses `hear` asks three once
more (the shape; the padding numbers; several calls). `messages` takes any shape: where the orders
fail `planOk`'s test a level does not refuse. No text of Desc/Part/MaskedSum4.lean is called here:
`wholeStandIn` (Prod/Level.lean) and the flat functions of OnBytes/K/Kc/ stand in (`pscBegin`,
`roundsIn`, `point`, `answer`, `slot`, `owe`, `must`; through the stand-in `pscEnds`, `pscRow`,
`shown`). Nine pure functions are `verify-on-bytes`'s (`eqTab`, `orderDefault`,
`orderForestRange`, `padKeyOf`, `elems`, `lins`, `tableAt`, `joinedTableAt`, `callWeight`). Against
that routine a level's row is made in front of the round LINE, not behind it (the one turns the
ledger alone, the other the tape alone), and `decide` is the stricter by the test on the ledger's
count and by the test that nothing is heard yet at this seat: so what `heard` gives behind `decide`
is what this `decide` has laid, wherever the seat reads what it lays
(Johnson/Desc/First/Look/K3SeatLaw.lean). No theorem says that `messages` gives what `Forest.pad`,
or the library's flat copy of it (`lkPad`, OnBytes/K/Kc/FlatHear.lean), gives.
That a sent or a drawn word is
below the field's prime is not asked by this kind: the fold asks it of the whole view in front
(`viewWordsBelowPrime`, in `FileDescription.runEnd`): a run through `Block.step` alone does not. That the claims are
gathered is the matter of the link in whose `hear` the block stands, and that they are batched of
its batching. What a round holds and draws is said by ROUNDS, and `Block.step` holds a view against
it (`roundsFit`); the strict reading of a round asks the same once more, and its limits hold here
too; four of its clauses read the entry alone and are asked here at the view's time. All that the
hearing refuses bears one name. WHICH ORACLE MESSAGES MUST BE FIXED BEFORE THE SHIFT IS DRAWN (the
keys'; the counts' bits') is the calling kind's to name (`before`): at the empty list nothing is
asked. Nothing has been shown of it.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Kc.FlatHear
import Johnson.Desc.First.Prod.Level
import Johnson.Desc.Block
import Johnson.Desc.First.Look.LookKind
import Johnson.Desc.First.Tape.Tape
import Johnson.Desc.First.Tape.RowsOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Call Aff)

open First.Look (P Guest)

/-- Where the carried record keeps what the kind reads and writes. -/
structure Seat (S Cl : Type) where
  /-- the open sub-proof's ledger, if one is open -/
  fork : S → Option Fork
  /-- the count of rows that the round closed last still owes -/
  owed : S → First.Tape.RowsOwed
  /-- behind the hearing: the record with what was heard and the ledger behind. Called once a place.
  It leaves what `owed` reads as it is: no entry of a lookup counts rows -/
  put : S → Model.Forest.Heard → Fork → S
  /-- the record with the ledger alone laid anew: for a mark in it -/
  mark : S → Fork → S
  /-- what was heard here -/
  heard : S → Option Model.Forest.Heard
  /-- a linear form, claimed to be 0, as a claim -/
  claim : Aff → Cl

/-! ## DECIDES: what the verifier does with the lookup's rounds

The keys of all calls, each moved by its call's number times the shift theta, are the leaves of one
product tree ("the key side"): a leaf is alpha - key. The tables' rows are the leaves of 32 product
trees ("the table side"), one for each bit j of a row's count: a leaf is 1 + b (alpha - 1 - row), b
that bit. The lookup is tested by the equation Z = a G_0 G_1^2 G_2^4 ... G_31^(2^31) at the drawn
alpha: Z the key side's root, G_j the root of tree j, a the public product over the padding keys. No
equation is tested while the rounds are heard: every sumcheck leaves one linear form in hidden
values, which is claimed to be 0.
-/

open OnBytes.Model (eqTab orderDefault)
open OnBytes.Model.Forest (Shape Heard padKeyOf elems lins tableAt joinedTableAt callWeight
  orderForestRange)
open First.Prod (wholeStandIn Carried)

/-- The public factor a: the product of alpha - key over all padding keys. -/
def paddingFactor (h : Shape) (theta alpha : E) : E :=
  (List.range h.NT).foldl
    (fun a y => mulE a (powE (subE alpha (padKeyOf h theta (h.callOf.getD y 0))) (h.pub.getD y 0)))
    (powE (subE alpha (padKeyOf h theta 0)) h.emptyKeys)

/-- Z = a G_0 G_1^2 ... G_31^(2^31), by squaring and multiplying: 31 masked sumchecks without a
variable. The first shows Z, P_1, G_0 and claims Z - a P_1^2 G_0 = 0; step j shows P_(j+1), G_j and
claims P_j = P_(j+1)^2 G_j; the last power is G_31. Returns the 31 claims, the slot of Z and the 32
slots of the G_j. -/
def tie (a : E) : Fl (Array Aff × Nat × Array Nat) := do
  let sq (x y : E) := mulE (mulE x x) y
  let w ← wholeStandIn (Aff.ofConst zeroE) [] 3 3 fun v =>
    subE (v.getD 0 zeroE) (mulE a (sq (v.getD 1 zeroE) (v.getD 2 zeroE)))
  let s ← (List.range 30).foldlM
    (fun (s : Array Aff × Nat × Array Nat) _ => do
      let w ← wholeStandIn (Aff.slot s.2.1) [] 3 2 fun v => sq (v.getD 0 zeroE) (v.getD 1 zeroE)
      pure (s.1.push w.row, w.sEnd, s.2.2.push (w.sEnd + 1)))
    (#[w.row], w.sEnd + 1, #[w.sEnd + 2])
  pure (s.1, w.sEnd, s.2.2.push s.2.1)

/-- In which order a level of the key side's tree binds its variables. -/
def keyOrders (h : Shape) (mu : Nat) : List Nat :=
  if mu + 1 = h.v then orderForestRange mu h.rK else orderDefault mu

/-- THE TESTS ON THE PLAN ALONE: the public side's (Johnson/Desc/First/Look/LookKind.lean), and the
grand product's on its two runs' orders and first points. -/
def planOk {S Cl : Type} (p : P) (laid : Array Nat) (guests : List (Guest S Cl)) : Bool :=
  p.planOk laid guests &&
    match p.shape with
    | some h => First.Prod.runOk 0 h.v 0 (keyOrders h) && First.Prod.runOk 5 h.d 5 orderDefault
    | none => false

/-- **The lookup's rounds, heard in order.** h: the place's shape, with its padding numbers. It
always hears the shift: that there are several calls is asked by `hear` and by `planOk`. -/
def messages (h : Shape) : Fl Heard := do
  let v := h.v
  let d := h.d
  let m := 5 + d
  let slot0 ← Fl.slot
  let owedObjects ← Fl.owe "look-up-mask-claims"
  let owedPlanes ← Fl.owe "look-up-plane-claims"
  let owedJoin ← Fl.owe "look-up-join"
  -- the shift between the calls; the point at which the two sides are compared
  let theta ← Fl.answer .lkpShift
  let alpha ← Fl.answer .lkp
  let a := paddingFactor h theta alpha
  -- the two sides' roots are tied
  let (rows, sZ, sG) ← tie a
  -- one claim on the 32 roots of the table side, at five drawn coordinates
  let rhoT := (← Fl.point .lkpPlanes 5).reverse
  let ej := eqTab rhoT
  let cT := (List.range 32).foldl
    (fun (f : Aff) j => Aff.addMul f (Aff.slot (sG.getD j 0)) (ej.getD j zeroE)) (Aff.ofConst zeroE)
  -- the key side's product tree, from the root down: v levels
  let keys ← First.Prod.run 0 v (keyOrders h) { rows := rows, point := #[], form := Aff.slot sZ }
  let zx := keys.point.extract 0 h.dT
  let zy := keys.point.extract h.dT keys.point.size
  -- the table side's 32 product trees as one, from the five coordinates down: d levels
  let table ← First.Prod.run 5 d orderDefault { rows := keys.rows, point := rhoT, form := cT }
  Fl.must (table.point.size == m)
  -- a leaf of the table side is 1 + b (alpha - 1 - row): a sumcheck whose claim the caller closes
  let leaves ← Fl.pscBegin table.form
  let (zb0, leaves) ← Fl.roundsIn .eq leaves
    ((List.range m).map fun j => (table.point.getD j zeroE, if j < d then 2 else 1))
  -- the bits are bits: b^2 - b sums to 0 against the equality weights of a drawn point
  let r5 := (← Fl.point .zero m).reverse
  let bits ← wholeStandIn (Aff.ofConst zeroE) r5.toList 2 1 fun x =>
    subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)
  let rows := table.rows.push bits.row
  -- four counts of its own: no input can trip them
  Fl.must ((← Fl.slot) == slot0 + elems h && rows.size == lins h)
  Fl.must (h.iota.all fun i => decide (i ≤ h.rK))
  let zk := (Array.range h.NC).map fun c => zy.extract (h.rK - h.iota.getD c 0) zy.size ++ zx
  Fl.must ((List.range h.NC).all fun c =>
    (zk.getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0)
  -- the public tables at the leaves' point
  let tT := h.calls.map fun k => tableAt k (zb0.extract (h.kT - k.k) h.kT)
  let row := joinedTableAt h theta tT (zb0.extract h.kT (h.kT + h.cK))
  pure {
    shape := h, theta := theta, alpha := alpha, a := a, rows := rows, leaves := leaves,
    leavesA := subE (subE alpha oneE) row, sBit := bits.sEnd, zx := zx, zy := zy,
    e := (Array.range h.NC).map (callWeight h zy), cEnd := keys.form, zb0 := zb0,
    zb1 := (bits.challenges.take m).toArray, tT := tT, zk := zk, owedObjects := owedObjects,
    owedPlanes := owedPlanes, owedJoin := owedJoin }

/-- **The lookup's messages at a place.** es: the place's entries. Nothing is left over. Nothing
where the place has no shape, its padding numbers do not fit, or there is one call alone. -/
def hear (p : P) (es : List Fmt.Entry) (F : Fork) (rs : List Fmt.RoundView) : Option (Heard × Fork) :=
  match p.shape with
  | some h => if 1 < h.NC then First.Tape.flRun {} (messages h) es F rs else none
  | none => none

/-- **The kind "lookup"**: a host. piece: the block's number inside its link. laid: the calling
kind's count of padding places, tree by tree. before: the oracle messages that must have been sent
before the shift is drawn: the calling kind's to name. guests: other kinds' identities, handed in as
functions before anything is heard, and called late, with the claims. `decide` asks that nothing is
owed in front and that the ledger's count of slots stands at the place's public number: so every
slot that the claims name is a public number. Each refusal bears the name of its test. -/
def block {S Cl : Type} (seat : Seat S Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) : KindWithGuestIdentities P (Guest S Cl) S Cl := fun p guests =>
  { name := p.name
    place := ⟨1, some p.link, piece, .K3⟩
    planOk := planOk p laid guests
    rounds := p.rounds
    oracles := p.rounds.map fun _ => []
    before := before
    decide := fun s rs _ => do
      let F ← named "K3: no sub-proof is open" (seat.fork s)
      need "K3: nothing is heard yet" (seat.heard s).isNone
      need "K3: rows are owed in front" (seat.owed s).noneWaits
      need "K3: the ledger's count of slots" (F.next == p.first)
      let x ← named "K3: the hearing" (hear p (p.entries.getD []) F rs)
      pure (seat.put s x.1 x.2)
    claims :=
      [("objects", fun _ s => do
        let F ← named "K3 objects: no sub-proof is open" (seat.fork s)
        let g ← named "K3 objects: nothing was heard" (seat.heard s)
        pure (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects))),
       ("guests", fun _ s =>
        named "K3 guests: a guest refuses"
          ((guests.mapM fun (g : Guest S Cl) => g.form s).map fun l => (l, s)))]
    after := [] }

end VerifiableInference.Desc.K3
