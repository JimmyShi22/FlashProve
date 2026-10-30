-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/Via/Rounds.lean: the kind "lookup" (K3): its hearing on the rounds of a
view, over the parts' own texts. Definitions with code. No theorem.

What it is. Johnson/Desc/First/Look/K3LookupGeneral.lean hears a lookup's rounds in the flat monad `Fl` of
OnBytes/K/Kc/Flat.lean, off a tape that is made from the view's rounds and the plan's entries, over
a stand-in for the masked sumcheck. This file says the same course a second time, line for line, on
`List Fmt.RoundView`, the type of rounds that `Block.decide` is handed, and calls
  the masked sumcheck's own text (Johnson/Desc/Part/MaskedSum4.lean): `whole` for the tie, the
    parts' step and the bits; `hear` at ends := none for the leaves; `row` where the leaves'
    sumcheck is closed;
  the grand product on a view's rounds (Johnson/Desc/First/ProdV/Level.lean): `run`.
It is general in the lookup's numbers: it reads K3LookupGeneral.lean's `Face`.

The course and who cuts the rounds. Every piece cuts its own rounds off the front of the list and
hands the rest on; how many it takes it reads off its own call, never off an entry:
  the shift, where there is one      1 round: nothing sent, 1 element drawn
  alpha                              1 round: nothing sent, 1 element drawn
  the tie                            planes - 1 masked sumchecks without a variable: 3 rounds each
  the parts' step                    parts - 1 more: 3 rounds each
  the planes' point                  1 round: nothing sent, mu elements drawn; read in reverse
  a key tree for each part           the level with m variables: m + 4 rounds
  the table side's trees as one      likewise, from mu variables up: d levels
  the leaves' sumcheck, left open    1 + (mu + d) rounds
  the bits' point                    1 round: nothing sent, mu + d elements drawn; read in reverse
  the bits' sumcheck                 (mu + d) + 3 rounds

The leaves' sumcheck is left open, and the part's own record is enough for that. `MaskedSum.hear` at
ends := none hands back start, target, eps, claim, first, vars and r. These are all the fields of
the verifier program's record `Model.Psc` that hold data; its three flags are constants at that
moment (started; not ended; no row made). `HeardV.leaves` is the part's record, `planesV` closes it
by the part's own `row`, and `toPsc` makes the program's record of it for a caller that reads
that one. In the ledger `hear` at ends := none moves the count of slots alone: its writing of end
values is a fold over the empty list.

Main names:
  `Hr`: the type of a text that hears, with "do"; `Hr.ret` and `Hr.andThen` say all that "do" means.
  `drawV`, `drawsV`, `sumV`, `openV`: a round of draws; a masked sumcheck with ends; one left open.
  `tieV`, `partsV`, `keysV`, `messagesV f`: the lookup's rounds, heard in order; `HeardV`.
  `hearV f F rs`: the same at a place: nothing is left over. It is handed no entry of the plan.
  `planesV`: the three claims on the planes; it closes the leaves' sumcheck.
  `toPsc`, `toHeardG`: to the verifier program's record, and to K3LookupGeneral.lean's.
  `entriesV f`: the rounds that this text hears, as entries of the plan with the work bits left 0,
    made of the same calls as the hearing; `entriesFit`: a test for planOk, of the planner's entries
    against it.
  `SeatV`, `blockV`: the kind, as `lookupKind` has it, with this hearing.

Limits. WHAT IT LACKS AGAINST THE HEARING OFF THE TAPE (Johnson/Desc/First/Tape/Tape.lean,
`roundT`). A view's round bears no name, no mark on which draws are never 0, no count of rows: these
are fields of the plan's entry, and this text is handed none. So it does not ask: a round's name
(Flat.lean, closeOne, closeN); the entry's number of never-0 draws; clause 4 (no rows are counted;
not the round that batches rows); clause 5 (the kind of the name); of clauses 2, 3 and 6 the halves
that read the entry (e.poss, e.trits, e.msg, e.roots, e.answers, e.count). What a view can bear it
asks: every item sent is a scalar; as many are sent and as many elements are drawn as the piece's
own call says; no position and no matrix entry is drawn; the draw of every further variable Y is not
0; all rounds are used up. `entriesFit` is offered so that the entry's halves are asked once, on the
plan: where it holds, the planner's entries have, round for round, this text's names and numbers,
and `Block.step` holds the view against these entries (`roundsFit`). Nothing in this file shows that
this makes up for the tape's guards.
Further limits: those of K3LookupGeneral.lean's head and of the two parts' heads. "Not 0" judges the three
words of a draw: right only where the words are below the prime, which the fold asks of the whole
view in front. `MaskedSum.row` has not the program's four guards on a sumcheck's flags (Flat.lean,
pscRow): that the leaves' row is made once is asked by `blockV` through the debt's mark, and a
second writing under a filled slot is refused by the ledger. No theorem in this file says that
`messagesV` gives what `messagesG` or K3Lookup.lean's `messages` gives. This file imports
K3LookupGeneral.lean for `Face`, `PlaneClaim`, `eqPairs`, `PG`, `unpaidG`: through that import the
flat monad is in scope; no definition here calls it.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LookupGeneral
import Johnson.Desc.Part.MaskedSum4
import Johnson.Desc.First.ProdV.Level

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open OnBytes.Model (Fork Aff eqTab orderDefault ofNat)
open VerifiableInference.Desc.Part
open First.ProdV (Hears elementsAlone)

/-! ## A text that hears -/

/-- From a ledger and the rounds still to come: nothing, or a value, the ledger behind and the
rounds that are left. It is `First.ProdV.Hears` as a type of its own, so that texts can be written
with "do". -/
def Hr (α : Type) : Type := Fork → List Fmt.RoundView → Option (α × Fork × List Fmt.RoundView)

namespace Hr

variable {α β : Type}

/-- Returns a and changes nothing. -/
def ret (a : α) : Hr α := fun F rs => some (a, F, rs)

/-- x, then f on its value, from the ledger and the rounds that x has left. -/
def andThen (x : Hr α) (f : α → Hr β) : Hr β := fun F rs =>
  match x F rs with
  | some (a, G, rest) => f a G rest
  | none => none

instance : Monad Hr where
  pure := ret
  bind := andThen

/-- A text of the grand product's type. -/
def of (x : Hears α) : Hr α := x

/-- Nothing unless b is true. -/
def must (b : Bool) : Hr Unit := fun F rs => if b then some ((), F, rs) else none

/-- The slot of the next scalar that is sent. -/
def slot : Hr Nat := fun F rs => some (F.next, F, rs)

/-- Enters a claim in the ledger's list of owed claims. Returns its number. -/
def owe (what : String) : Hr Nat := fun F rs => some ((F.owe what).1, (F.owe what).2, rs)

end Hr

/-! ## The pieces -/

/-- **A round of draws**: nothing is sent; n elements are drawn, and nothing else. -/
def drawsV (n : Nat) : Hr (Array E) := fun F rs =>
  match rs with
  | [] => none
  | r :: rest =>
    if elementsAlone [r] then (MaskedSum.roundOf 0 n r).map fun x => (x.2.toArray, F, rest)
    else none

/-- The same for one element. -/
def drawV : Hr E := fun F rs =>
  match drawsV 1 F rs with
  | some (x, G, rest) => if x.size == 1 then some (x.getD 0 zeroE, G, rest) else none
  | none => none

/-- How many rounds a call takes. -/
def roundsOf (k : MaskedSum.Call) : Nat := k.vs.length + (if k.ends.isSome then 3 else 1)

/-- **A masked sumcheck with ends, its row made at once.** It cuts its own rounds. It refuses if a
position or a matrix entry is drawn in one of them, or if Y's draw (the last challenge) is 0.
Returns the part's record and the row. -/
def sumV (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    Hr (MaskedSum.Heard × Aff) := fun F rs =>
  if !elementsAlone (rs.take (roundsOf k)) then none else
  match MaskedSum.whole C k endTerm F (rs.take (roundsOf k)) with
  | some (h, row, G) =>
    if isZeroE (h.r.getLastD zeroE) then none else some ((h, row), G, rs.drop (roundsOf k))
  | none => none

/-- **A masked sumcheck without ends, left open**: no row is made. It cuts its own rounds. -/
def openV (C : Aff) (vs : List MaskedSum.Var) : Hr MaskedSum.Heard := fun F rs =>
  if !elementsAlone (rs.take (vs.length + 1)) then none else
  (MaskedSum.hear C { lead := 0, vs := vs, ends := none } F (rs.take (vs.length + 1))).map fun x =>
    (x.1, x.2, rs.drop (vs.length + 1))

/-- The call of a masked sumcheck without a variable: the degree in Y; the number of end values. -/
def noVar (dY n : Nat) : MaskedSum.Call := { lead := 0, vs := [], ends := some ⟨dY, n⟩ }

/-- Z = a G_0 G_1^2 ... G_(w-1)^(2^(w-1)), by squaring and multiplying: w - 1 masked sumchecks
without a variable (`tieG`, K3LookupGeneral.lean). Returns the claims, the slot of Z and the w slots of
the G_j. -/
def tieV (w : Nat) (a : E) : Hr (Array Aff × Nat × Array Nat) := do
  let sq (x y : E) := mulE (mulE x x) y
  let x ← sumV (Aff.ofConst zeroE) (noVar 3 3) fun _ v =>
    subE (v.getD 0 zeroE) (mulE a (sq (v.getD 1 zeroE) (v.getD 2 zeroE)))
  let s ← (List.range (w - 2)).foldlM
    (fun (s : Array Aff × Nat × Array Nat) _ => do
      let y ← sumV (Aff.slot s.2.1) (noVar 3 2) fun _ v => sq (v.getD 0 zeroE) (v.getD 1 zeroE)
      pure (s.1.push y.2, y.1.sEnd, s.2.2.push (y.1.sEnd + 1)))
    (#[x.2], x.1.sEnd + 1, #[x.1.sEnd + 2])
  pure (s.1, x.1.sEnd, s.2.2.push s.2.1)

/-- **From the product of the parts' roots to each root** (`partsG`). -/
def partsV : Nat → Array Aff → Aff → Hr (Array Aff × List Aff)
  | 0, rows, C => pure (rows, [C])
  | n + 1, rows, C => do
    let w ← sumV C (noVar 2 2) fun _ v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)
    let x ← partsV n (rows.push w.2) (Aff.slot (w.1.sEnd + 1))
    pure (x.1, Aff.slot w.1.sEnd :: x.2)

/-- **The parts' key trees, one after the other**, each from its root down (`keysG`). -/
def keysV (f : Face) : List (Nat × Nat) → List Aff → Array Aff →
    Hr (Array Aff × List (Array E × Aff))
  | x :: xs, C :: Cs, rows => do
    let k ← Hr.of (First.ProdV.run 0 x.1 (f.orders x.2) { rows := rows, point := #[], form := C })
    let y ← keysV f xs Cs k.rows
    pure (y.1, (k.point, k.form) :: y.2)
  | _, _, rows => pure (rows, [])

/-- The leaves' variables, in the order of the rounds: variable j is summed with the equality
weights at coordinate j of the table side's last point; a round's polynomial has three coefficients
for the d variables of a row's number, two for the mu variables of a plane's. -/
def leafVars (f : Face) (z : Array E) : List MaskedSum.Var :=
  (List.range (f.mu + f.d)).map fun j =>
    MaskedSum.Var.point (z.getD j zeroE) (if j < f.d then 3 else 2)

/-- The call of the bits' sumcheck at a point. -/
def bitsCall (z : List E) : MaskedSum.Call :=
  { lead := 0, vs := z.map fun x => MaskedSum.Var.point x 3, ends := some ⟨2, 1⟩ }

/-- What was heard: `HeardG` with the leaves' sumcheck as the part's own record. -/
structure HeardV where
  /-- the shift; 0 where there is none -/
  theta : E
  alpha : E
  /-- the public factor -/
  a : E
  /-- the claims that read hidden values alone -/
  rows : Array Aff
  /-- the sumcheck on the table side's leaves, left open: `planesV` closes it -/
  leaves : MaskedSum.Heard
  /-- the slot of the bits' end value -/
  sBit : Nat
  /-- for each part: its key tree's last point, the highest variable first, and the form on
  alpha - key there -/
  keys : List (Array E × Aff)
  /-- the leaves' point; the bits' point -/
  zb0 : Array E
  zb1 : Array E
  owedObjects : Nat
  owedPlanes : Nat
  owedJoin : Nat

/-- **The lookup's rounds, heard in order.** -/
def messagesV (f : Face) : Hr HeardV := do
  let m := f.mu + f.d
  let slot0 ← Hr.slot
  let owedObjects ← Hr.owe "look-up-mask-claims"
  let owedPlanes ← Hr.owe "look-up-plane-claims"
  let owedJoin ← Hr.owe "look-up-join"
  -- the shift between the functions, where there is one; the point at which the sides are compared
  let theta ← if f.shifted then drawV else pure zeroE
  let alpha ← drawV
  let a := f.factor theta alpha
  -- the two sides' roots are tied
  let (rows, sZ, sG) ← tieV f.planes a
  -- from the product of the parts' roots to each
  let (rows, roots) ← partsV (f.parts.length - 1) rows (Aff.slot sZ)
  -- one claim on the planes' roots, at mu drawn coordinates; a plane that is not real has root 1
  let rhoT := (← drawsV f.mu).reverse
  let ej := eqTab rhoT
  let cT := (List.range (2 ^ f.mu)).foldl
    (fun (c : Aff) j =>
      if j < f.planes then Aff.addMul c (Aff.slot (sG.getD j 0)) (ej.getD j zeroE)
      else c + Aff.ofConst (ej.getD j zeroE)) (Aff.ofConst zeroE)
  -- the key side: a product tree for each part
  let (rows, keys) ← keysV f f.parts.zipIdx roots rows
  Hr.must (keys.length == f.parts.length)
  -- the table side's product trees as one, from the mu coordinates down: d levels
  let table ← Hr.of (First.ProdV.run f.mu f.d orderDefault
    { rows := rows, point := rhoT, form := cT })
  Hr.must (table.point.size == m)
  -- a leaf of the table side is 1 + b (alpha - 1 - row): a sumcheck whose claim is made later
  let leaves ← openV table.form (leafVars f table.point)
  -- the bits are bits: b^2 - b sums to 0 against the equality weights of a drawn point
  let r5 := (← drawsV m).reverse
  let bits ← sumV (Aff.ofConst zeroE) (bitsCall r5.toList) fun _ x =>
    subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)
  let rows := table.rows.push bits.2
  -- two counts of its own: no input can trip them
  Hr.must ((← Hr.slot) == slot0 + f.slots && rows.size == f.lins)
  pure {
    theta := theta, alpha := alpha, a := a, rows := rows, leaves := leaves, sBit := bits.1.sEnd,
    keys := keys, zb0 := leaves.r.toArray, zb1 := (bits.1.r.take m).toArray,
    owedObjects := owedObjects, owedPlanes := owedPlanes, owedJoin := owedJoin }

/-- **The lookup's messages at a place.** Nothing is left over. Nothing where the face fails its
tests. No entry of the plan is read. -/
def hearV (f : Face) (F : Fork) (rs : List Fmt.RoundView) : Option (HeardV × Fork) :=
  if f.ok then
    match messagesV f F rs with
    | some (g, G, []) => some (g, G)
    | _ => none
  else none

/-! ## CLAIMS on the planes of the counts' bits -/

/-- **The three claims on the planes** (`planesG`). It closes the leaves' sumcheck by the part's own
`row`: the coefficients of its hiding polynomial are put under their slots here. It takes no
round. -/
def planesV (f : Face) (g : HeardV) (F : Fork) : Option (List PlaneClaim × Fork) :=
  (MaskedSum.row g.leaves oneE {} F).map fun x =>
    (([⟨x.1, mulE g.leaves.eps (f.leaf g.theta g.alpha g.zb0), eqPairs (f.mu + f.d) g.zb0⟩,
      ⟨Aff.slot g.sBit, subE zeroE oneE, eqPairs (f.mu + f.d) g.zb1⟩,
      ⟨Aff.ofConst (subE zeroE (ofNat f.count)), oneE,
        ((List.range f.mu).map fun t => (oneE, ofNat (2 ^ 2 ^ t))) ++
          List.replicate f.d (oneE, oneE)⟩] : List PlaneClaim), x.2)

/-! ## To the records of `OnBytes.Psc` -/

/-- How the verifier program writes a variable's way of summing. -/
def weightOf : MaskedSum.Var → OnBytes.Psc.Weight
  | .plain d => OnBytes.Psc.Weight.plain d
  | .point z d => OnBytes.Psc.Weight.equality z d

/-- **The verifier program's record of a masked sumcheck that was heard without ends and is still
open**: begun; not ended; no row made. -/
def toPsc (h : MaskedSum.Heard) : Model.Psc :=
  { start := h.start, target := h.target, eps := h.eps, claim := h.claim, first := h.first
    vars := (h.vars.map weightOf).toArray, r := h.r.toArray
    ended := false, rowMade := false, started := true }

/-- To K3LookupGeneral.lean's record; `toHeard h` (there) goes on to the verifier program's. -/
def toHeardG (g : HeardV) : HeardG :=
  { theta := g.theta, alpha := g.alpha, a := g.a, rows := g.rows, leaves := toPsc g.leaves
    sBit := g.sBit, keys := g.keys, zb0 := g.zb0, zb1 := g.zb1, owedObjects := g.owedObjects
    owedPlanes := g.owedPlanes, owedJoin := g.owedJoin }

/-! ## ROUNDS, of the same calls -/

/-- A round of draws as an entry of the plan. -/
def drawEntry (name : String) (n : Nat) : Fmt.Entry := MaskedSum.entry name 0 n 0

/-- **The rounds that `messagesV f` hears**, as entries of the plan, the work bits left 0: each
piece's by the part's own maker, at the call that the hearing makes (an entry reads no point). -/
def entriesV (f : Face) : List Fmt.Entry :=
  (if f.shifted then [drawEntry "LKP shift" 1] else []) ++ [drawEntry "LKP" 1] ++
    MaskedSum.entries (noVar 3 3) ++
    (List.range (f.planes - 2)).flatMap (fun _ => MaskedSum.entries (noVar 3 2)) ++
    (List.range (f.parts.length - 1)).flatMap (fun _ => MaskedSum.entries (noVar 2 2)) ++
    [drawEntry "JOIN" f.mu] ++
    f.parts.flatMap (fun v => First.ProdV.runEntries 0 v) ++
    First.ProdV.runEntries f.mu f.d ++
    MaskedSum.entries { lead := 0, vs := leafVars f #[], ends := none } ++
    [drawEntry "ZERO" (f.mu + f.d)] ++
    MaskedSum.entries (bitsCall (List.replicate (f.mu + f.d) zeroE))

/-- A TEST FOR planOk: the planner's entries are, round for round and but for the work bits, those
that the hearing goes by. -/
def entriesFit (f : Face) (es : List Fmt.Entry) : Bool :=
  (es.map fun e => { e with work := 0 }) == entriesV f

/-! ## The kind -/

/-- Where the carried record keeps what the kind reads and writes (`SeatG`, at `HeardV`). -/
structure SeatV (S Cl : Type) where
  fork : S → Option Fork
  owed : S → First.Tape.RowsOwed
  put : S → HeardV → Fork → S
  mark : S → Fork → S
  heard : S → Option HeardV
  claim : Aff → Cl
  /-- a claim that reads the planes, as a claim: how the planes are read is the caller's -/
  claimP : S → PlaneClaim → Option Cl

/-- **The kind "lookup", general in its numbers, hearing on a view's rounds**: `lookupKind` with four
turns: `decide` hears by `hearV`; it asks that nothing is heard yet at this seat, as K3Lookup.lean does;
"planes" closes the leaves' sumcheck by `planesV`; `planOk` asks `entriesFit` besides. -/
def blockV {S Cl : Type} (seat : SeatV S Cl) (before : List (Nat × Nat)) (bits : Nat)
    (guests : List (First.Look.Guest S Cl)) (p : PG) : Block S Cl :=
  { name := p.name
    place := ⟨p.chain, some p.link, p.piece, .K3⟩
    planOk := p.planOk before bits guests && entriesFit p.face (p.entries.getD [])
    rounds := (p.entries.getD []).map fun e => { entry := e }
    oracles := (p.entries.getD []).map fun _ => []
    before := before
    decide := fun s rs _ => do
      let F ← named "K3: no ledger is open" (seat.fork s)
      need "K3: nothing is heard yet" (seat.heard s).isNone
      need "K3: rows are owed in front" (seat.owed s).noneWaits
      need "K3: the ledger's count of slots" (F.next == p.first)
      need "K3: the ledger's room" (F.ns == p.ns)
      let x ← named "K3: the hearing" (hearV p.face F rs)
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
        let x ← named "K3 planes: the leaves' claim" (planesV p.face g F)
        let l ← named "K3 planes: the caller's reader" (x.1.mapM (seat.claimP s))
        pure (l, seat.mark s (x.2.paid g.owedPlanes))),
       ("guests", fun _ s =>
        named "K3 guests: a guest refuses"
          ((guests.mapM fun (g : First.Look.Guest S Cl) => g.form s).map fun l => (l, s)))]
    after := [] }

end VerifiableInference.Desc.K3
