-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Kc/Flat.lean: five routines of the check of the output head's sub-proof, and the routines
of the masked sumcheck beneath them, as functions on plain data.

Why. The program 'verify-on-bytes' checks the sub-proof of the output head by routines that run in
a context: the channel with the plan's entries, the statement, the book of trees, names of
refusals, a dry run beside the run on a view (OnBytes/Iop/Ground.lean, OnBytes/Model/Hide.lean). A
statement that ties such a routine to another verifier's step wants it without that context. This
file writes the receiving routines again, line for line, over two things alone: the rounds as
lists of field elements, and the ledger of the sub-proof's slots.

The plain data.
 `FlatRound`: what the prover sends in a round and what the verifier draws after it, as two lists of
   elements of the extension field; and three words of the plan's entry under which the round is
   closed: its name, how many of the drawn elements are drawn by the rule that never gives 0, and
   how many rows it batches. `Tape`: the rounds that are not yet closed; of the first one the
   elements that are not yet taken.
 `Model.Fork` (OnBytes/Model/Hide.lean): a record of numbers and arrays. Of it these routines read
   and change the ledger of the slots alone: the next free slot, and for each slot what was shown,
   its mask entry's factor and whether it is filled. THE LEDGER IS AN ARGUMENT AND A RESULT of every
   function here: it is what comes in of earlier claims (the start of a sumcheck reads what was
   shown under the slots that its form names) and what goes out.
 What a function returns beside the ledger is the program's own plain record: `Model.Psc`,
   `Model.Tsc`, `Model.Level`, `Model.Aff`: numbers, elements, arrays of them.

The form. 'Fl α' is the type of a function from a ledger and a tape to nothing, or to a value with
the new ledger and what is left of the tape. So that the texts here can be held against the
program's line by line, they are written with the same "do"; `Fl.ret` and `Fl.andThen` say what that
means, and nothing else is hidden in it: no context, no name of a refusal, no dry run.

The five routines, by the kinds of step of the head's sub-proof:
 `flatPoint` (the norm's point over the positions), `flatSquares` (the sums of limb products, their
 batching element, the product layer), `flatProducts` (the row products, their batching element, the
 token sumcheck at the point), `flatStream` (the token sumcheck of the stream times the reciprocal),
 `flatLogits` (the token sumcheck of the activations times the head's weights, which goes on over
 the channels). Their counterparts: `Model.SubM.point`, `Model.Head.hearSquares`, `hearProducts`,
 `hearStream`, `hearLogits` (OnBytes/Model/HeadHeard.lean).
None of the five tests an equation of the protocol: a sumcheck's rounds test none, and what is left
of it is one linear claim (the field `rowU` or `row` of the result), which the caller adds later.
One condition is computed from drawn values: that a round's weight is in order (`heldT`
in `Fl.pscRound`); by the program's own comment it holds at every value; no theorem here says so.
So "the flat function accepts" means that it returns: the rounds have the shape and the names that
are asked for, the weights are in order and the slots are free.

Main definitions: `FlatRound`, `Tape`, `Fl`; `recv`, `recvN`, `closeN`, `closeOne`, `closeRows`;
`Fl.claimsIn`,
`Fl.pscBegin`, `Fl.pscRound`, `Fl.roundIn`, `Fl.pscEnds`, `Fl.pscRow`, `Fl.levelIn`, `Fl.tscRounds`,
`Fl.tscIn`; `flatPoint`, `flatSquares`, `flatProducts`, `flatStream`, `flatLogits`.

Not claimed. This file holds no theorem. That these functions return what the program's routines
return is stated in OnBytes/K/Kc/Laws.lean. A flat function tests less of the plan than the
program's routine and can return where that routine refuses (see the note at the end). It does not
see an entry's bytes, work, positions or matrix entries. That an element which the plan draws other
than 0 IS not 0 is the strict reader's rule: neither the program's routines nor these functions test
it. Nothing on soundness. The program does not import this file.

-/
import OnBytes.Model.HeadHeard
import OnBytes.K.Kc.FlatTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork Aff Psc Tsc Level RoundForm)

/-! ## The rounds as plain data -/

/-- One round: three words of its entry in the plan; the elements that the prover sends, in their
order; the elements that the verifier draws after them. -/
structure FlatRound where
  /-- the name of the plan's entry under which the round is closed; nothing if the plan has no
  entry left for it -/
  name : Option String
  /-- how many of the drawn elements the plan draws by the rule that never gives 0 -/
  nz : Nat
  /-- for a round that batches rows: how many, by the plan -/
  rows : Nat
  /-- the elements sent -/
  sent : List E
  /-- the elements drawn -/
  drawn : List E
  deriving DecidableEq, Repr, Inhabited

/-- The rounds that are not yet closed. Of the first one `sent` holds what is not yet taken. -/
abbrev Tape : Type := List FlatRound

/-- Takes the next element of the open message. -/
def recv : Tape → Option (E × Tape)
  | ⟨nm, z, w, x :: s, d⟩ :: t => some (x, ⟨nm, z, w, s, d⟩ :: t)
  | _ => none

/-- Takes n more elements and appends them to a. -/
def recvLoop : Nat → Array E → Tape → Option (Array E × Tape)
  | 0, a, t => some (a, t)
  | n + 1, a, t =>
    match recv t with
    | some (x, u) => recvLoop n (a.push x) u
    | none => none

/-- Takes the next n elements of the open message. -/
def recvN (n : Nat) (t : Tape) : Option (Array E × Tape) := recvLoop n (Array.emptyWithCapacity n) t

/-- Closes the open message's round, of which every element must have been taken, and returns the n
elements that were drawn. The plan's entry must have the name, and nz elements drawn other than
0. -/
def closeN (name : String) (nz n : Nat) : Tape → Option (List E × Tape)
  | ⟨some nm, z, _, [], d⟩ :: t =>
    if nm == name && z == nz && d.length == n then some (d, t) else none
  | _ => none

/-- Closes the round and returns the one element that was drawn. -/
def closeOne (name : String) (nz : Nat) : Tape → Option (E × Tape)
  | ⟨some nm, z, _, [], [x]⟩ :: t => if nm == name && z == nz then some (x, t) else none
  | _ => none

/-- Closes the round that batches the given number of rows and returns the element drawn. -/
def closeRows (rows : Nat) : Tape → Option (E × Tape)
  | ⟨some nm, z, w, [], [x]⟩ :: t =>
    if nm == Model.RoundName.batSigma.name && z == 0 && w == rows then some (x, t) else none
  | _ => none

/-! ## A function on a ledger and a tape -/

/-- From a ledger and a tape: nothing, or a value, the new ledger and what is left of the tape. -/
def Fl (α : Type) : Type := Fork → Tape → Option (α × Fork × Tape)

namespace Fl

variable {α β : Type}

/-- Returns a and changes nothing. -/
def ret (a : α) : Fl α := fun F t => some (a, F, t)

/-- x, then f on its value, from the ledger and the tape that x has left. -/
def andThen (x : Fl α) (f : α → Fl β) : Fl β := fun F t =>
  match x F t with
  | some (a, G, u) => f a G u
  | none => none

instance : Monad Fl where
  pure := ret
  bind := andThen

/-- A step on the ledger that may refuse. -/
def change (f : Fork → Option Fork) : Fl Unit := fun F t => (f F).map fun G => ((), G, t)

/-- A step on the ledger that may refuse and that returns a value. -/
def take (f : Fork → Option (α × Fork)) : Fl α := fun F t => (f F).map fun x => (x.1, x.2, t)

/-- Reads a value off the ledger by a function that may refuse. -/
def ask (f : Fork → Option α) : Fl α := fun F t => (f F).map fun a => (a, F, t)

/-- Nothing unless b is true. -/
def must (b : Bool) : Fl Unit := fun F t => if b then some ((), F, t) else none

/-- The value of x, or nothing. -/
def need (x : Option α) : Fl α := fun F t => x.map fun a => (a, F, t)

/-- A step on the tape alone. -/
def onTape (g : Tape → Option (α × Tape)) : Fl α := fun F t => (g t).map fun x => (x.1, F, x.2)

/-! ### The calls on the rounds -/

/-- The next n elements of the open message. -/
def read (n : Nat) : Fl (Array E) := onTape (recvN n)

/-- The next element of the open message, as the sum of a hiding polynomial. -/
def readSum : Fl E := onTape recv

/-- Ends the open message; the one element drawn. r: the round's name. -/
def answer (r : Model.RoundName) : Fl E := onTape (closeOne r.name 0)

/-- `closeN`, with the drawn elements as an array. -/
def pointOn (name : String) (n : Nat) (t : Tape) : Option (Array E × Tape) :=
  (closeN name 0 n t).map fun x => (x.1.toArray, x.2)

/-- Ends the open message; the n elements drawn. -/
def point (r : Model.RoundName) (n : Nat) : Fl (Array E) := onTape (pointOn r.name n)

/-- `closeRows`, with the powers of the drawn element from its power 0. Nothing for no row. -/
def batchOn (rows : Nat) (t : Tape) : Option (Array E × Tape) :=
  if rows != 0 then (closeRows rows t).map fun x => (Model.powers x.1 rows, x.2) else none

/-- The round that batches the given number of rows; that many powers of the drawn element. -/
def batch (rows : Nat) : Fl (Array E) := onTape (batchOn rows)

/-- `closeN` for no element, without a value. -/
def emptyOn (name : String) (t : Tape) : Option (Unit × Tape) :=
  (closeN name 0 0 t).map fun x => ((), x.2)

/-- Ends the open message in a round in which nothing is drawn. -/
def empty (r : Model.RoundName) : Fl Unit := onTape (emptyOn r.name)

/-! ### Slots and hidden values -/

/-- Takes the next n slots. Returns the first of them. -/
def takeSlots (n : Nat) : Fl Nat := take fun F => some (F.next, { F with next := F.next + n })

/-- What was shown under slot j. -/
def shown (j : Nat) : Fl E := ask (·.shown j)

/-- The form a on what was shown. -/
def publicPart (a : Aff) : Fl E := ask (·.publicPart a)

/-- n hidden values that are sent outside a sumcheck. Returns the first one's slot. -/
def claimsIn (n : Nat) : Fl Nat := do
  let v ← read n
  must (v.size == n)
  let j ← takeSlots n
  change (·.hideRun j v oneE)
  pure j

/-! ### The masked sumcheck -/

/-- The beginning: the sum of the hiding polynomial, eps, the first running claim. -/
def pscBeginAt (target : E) : Fl Psc := do
  let first ← takeSlots 1
  let mu ← readSum
  let eps ← answer .pscEpsilon
  pure { target, first, eps, claim := addE mu (mulE eps target) }

/-- Begins the sumcheck of a sum that must equal the form C. -/
def pscBegin (C : Aff) : Fl Psc := do
  let p ← pscBeginAt (← publicPart C)
  pure { p with start := C, started := true }

/-- One round in a variable that is summed by w. draw: how the round is closed. Returns the
challenge. -/
def pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    Fl (E × Psc) := do
  must (fitsT w && heldT w)
  let sent ← read (w.d - 1)
  must (sent.size + 1 == w.d)
  let q := w.complete sent.toList p.claim
  let r ← onTape draw
  let _ ← takeSlots (w.d - 1)
  pure (r, { p with claim := OnBytes.Psc.polyAt q r, vars := p.vars.push w, r := p.r.push r })

/-- One round of the given form. -/
def roundIn (form : RoundForm) (p : Psc) (z : E := zeroE) (degree : Nat := 0) : Fl (E × Psc) := do
  must (!p.ended)
  let w ← need (weightT form z degree)
  pscRound p w (closeOne Model.RoundName.pscRound.name 0)

/-- The round in the further variable, then the n end values. Returns the first end value's slot. -/
def pscEnds (p : Psc) (degreeInY n : Nat) : Fl (Nat × Psc) := do
  must (!p.ended && decide (1 ≤ degreeInY) && decide (1 ≤ n))
  let (beta, p) ← pscRound p (OnBytes.Psc.Weight.atZero (degreeInY + 1))
    (closeOne Model.RoundName.pscY.name 1)
  let v ← read n
  must (v.size == n)
  empty .pscValues
  let e ← takeSlots n
  change (·.hideRun e v beta)
  pure (e, { p with ended := true })

/-- The claim that a sumcheck leaves. -/
def pscRow (p : Psc) (S0 : E) (kept : Aff := {}) : Fl (Aff × Psc) := do
  must (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size)
  change (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE))
  pure (p.rowForm S0 kept, { p with rowMade := true })

/-- The rounds of a layer of a product tree in the given order. -/
def levelRounds (mu : Nat) (rho : Array E) : List Nat → Array E → Psc → Fl (Array E × Psc)
  | [], r, p => pure (r, p)
  | v :: order, r, p => do
    must (decide (v < mu) && decide (mu - 1 - v < rho.size))
    let (x, p) ← roundIn .eq2 p (rho.getD (mu - 1 - v) zeroE)
    levelRounds mu rho order (r.set! (mu - 1 - v) x) p

/-- One layer of a product tree with mu variables. -/
def levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) : Fl Level := do
  must (order.length == mu)
  let p ← pscBegin C
  let (r, p) ← levelRounds mu rho order (Array.replicate mu zeroE) p
  let (sL, p) ← pscEnds p 2 2
  let tau ← answer .line
  let (row, _) ← pscRow p (mulE (← shown sL) (← shown (sL + 1)))
  pure { r, sL, sR := sL + 1, tau, row }

/-- One round for each coordinate in the list. Appends the challenges to r. -/
def tscLoop : List E → Array E → Psc → Fl (Array E × Psc)
  | [], r, p => pure (r, p)
  | z :: zs, r, p => do
    let (x, p) ← roundIn .eq2 p z
    tscLoop zs (r.push x) p

/-- The claimed sum, the beginning of the sumcheck, and its lt rounds under the first lt coordinates
of P. -/
def tscRounds (P : Array E) (lt : Nat) : Fl Tsc := do
  must (decide (lt ≤ P.size))
  let sCl ← claimsIn 1
  let p ← pscBegin (Aff.slot sCl)
  let (r, p) ← tscLoop (P.toList.take lt) #[] p
  pure { sCl, r, p }

/-- The whole token sumcheck. -/
def tscIn (P : Array E) (lt shown degreeInY : Nat) : Fl Tsc := do
  let o ← tscRounds P lt
  let (sEnd, p) ← pscEnds o.p degreeInY shown
  pure { o with sEnd := sEnd, p := p }

/-- The values shown in the n slots that begin at `first`. -/
def shownRun (first n : Nat) : Fl (Array E) :=
  (List.range n).foldlM (fun a j => do pure (a.push (← shown (first + j)))) #[]

/-- The rounds over the channels. Returns the challenges in the order of the rounds. -/
def channelRounds : Nat → Array E → Psc → Fl (Array E × Psc)
  | 0, r, p => pure (r, p)
  | n + 1, r, p => do
    let (x, p) ← roundIn .eq2 p Model.Head.half
    channelRounds n (r.push x) p

end Fl

/-! ## The five routines of the head -/

open OnBytes.Model (ledNS ledNP ledNO orderDefault)
open OnBytes.Model.Head (half productsShown)

/-- The norm's point over the positions: lt drawn elements. It reads one round: nothing is left to
take of its message. -/
def flatPoint (lt : Nat) : Fl (Array E) := Fl.point .zero lt

/-- The sums of limb products, the element that batches them, and the product layer. XL: the limbs
of a value of the stream; lPd: the logarithm of the padded width; lt: that of the positions; PV: the
norm's point. Returns the first slot, the powers and the layer. -/
def flatSquares (XL lPd lt : Nat) (PV : Array E) : Fl (Nat × Array E × Level) := do
  let n := ledNS XL
  let sW ← Fl.claimsIn n
  let gp ← Fl.batch n
  let plainPd := powE half lPd
  let C := (List.range n).foldl
    (fun C s => Aff.addMul C (Aff.slot (sW + s)) (mulE (gp.getD s zeroE) plainPd)) {}
  let mu := lPd + lt
  let wpl ← Fl.levelIn mu (Array.replicate lPd half ++ PV) C (orderDefault mu)
  pure (sW, gp, wpl)

/-- The row products, the element that batches them, and the token sumcheck at PV. Returns the first
slot, the powers and the sumcheck with its claim. -/
def flatProducts (XL lt : Nat) (PV : Array E) : Fl (Nat × Array E × Tsc) := do
  let sPv ← Fl.claimsIn (ledNP XL)
  let omV ← Fl.batch (ledNP XL)
  let tV ← Fl.tscIn PV lt (ledNO XL) 2
  let sh ← Fl.shownRun tV.sEnd (ledNO XL)
  let (row, p) ← Fl.pscRow tV.p (productsShown XL omV sh)
  pure (sPv, omV, { tV with p := p, rowU := row })

/-- The token sumcheck of the stream times the reciprocal, at the position coordinates zt. -/
def flatStream (lt : Nat) (zt : Array E) : Fl Tsc := do
  let tN ← Fl.tscIn zt lt 2 2
  let (row, p) ← Fl.pscRow tN.p (mulE (← Fl.shown tN.sEnd) (← Fl.shown (tN.sEnd + 1)))
  pure { tN with p := p, rowU := row }

/-- The token sumcheck of the activations times the head's weights, at the position coordinates zt,
with lam rounds more over the channels. Returns the sumcheck with its claim, and the channels'
challenges, that of bit v at place v. -/
def flatLogits (lt lam : Nat) (zt : Array E) : Fl (Tsc × Array E) := do
  let tH ← Fl.tscRounds zt lt
  let (r, p) ← Fl.channelRounds lam #[] tH.p
  let (sEnd, p) ← Fl.pscEnds p 2 2
  let (row, p) ← Fl.pscRow p (mulE (← Fl.shown sEnd) (← Fl.shown (sEnd + 1)))
  pure ({ tH with sEnd := sEnd, p := p, rowU := row }, r.reverse)

end OnBytes.K.Kc

/- What a close tests of the plan's entry, and what a tape does not show.

`closeN`, `closeOne` and `closeRows` test the entry's name and its number of elements drawn other
than 0. Only `closeRows` tests its number of batched rows: `closeN` and `closeOne` ignore it. None
of them tests the entry's number of drawn elements: the elements that the round drew are counted
against the caller's number (in `closeOne` and `closeRows`: one). The program's channel also refuses
to close a round, or to end a run, while the entry of the round closed last counts batched rows
whose number was not yet compared (`Chan.settled`, OnBytes/Iop/Ground.lean); no function here tests
that. A `FlatRound` holds elements of the field alone: what else a round sends or draws is not on a
tape, nor is the kind that belongs to an entry's name. A function hands back the rounds that it has
not closed, and does not see whether the plan has further entries. So a flat function can return
where the program's routine refuses. Whoever calls these functions on a view's rounds must test
these things itself.
-/
