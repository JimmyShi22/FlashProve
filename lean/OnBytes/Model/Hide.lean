-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Hide.lean: hidden values, affine claims on them, and the arrays that the claims read.

This is the engine that the checks of all sub-proofs of a model share. It follows
verifier/src/vf_subproof_engine.h of the C++ verifier, routine by routine. The last three routines
of that file, on a layer of a product tree, are in OnBytes/Model/Psc.lean.

Main definitions: HRow, HTree, Ent, Aff, Fork, Fork.hide, Fork.shown, Fork.publicPart, Fork.push,
Fork.kap, Fork.lin, Fork.settle, SubM, SubM.claimsIn, SubM.lin.

Where the words and the rules that the types do not enforce are explained. Fork explains hidden
value, slot, mask row and the names of this file, and says which numbers the caller must tie to the
hashed parameter bytes. Aff explains claim, form and virtual row. Fork.lin explains theta, the one
equation and why claims are added in a second pass. SubM explains sub-proof, chain, plan, strict
reader, dry run and view, what a refusal means, and the one case in which a refusal depends on a
drawn value.

What this file does not claim. No theorem is stated here; OnBytes/Model/HideLaws.lean states what
Fork.push, Fork.lin and Fork.settle compute where they return a value. Hidden is the name of a
value's part in the protocol: nothing here claims that a value stays hidden, or that a false claim
is caught. The one equation is not tested here: it is passed to the request's chain in
OnBytes/Model/Trees.lean. Numbers are natural numbers, so they do not wrap around at 2^32 as the C++
counters would. What of vf_subproof_engine.h has no counterpart here is listed at Fork.
-/
import OnBytes.Model.Frame
import OnBytes.Model.Rounds

namespace OnBytes.Model

/-! ## Arrays and their virtual rows -/

/-- One virtual row of an array: a public combination of the array's R rows. coef holds the R
weights written out, whether or not rowForm is set. A new row has none: the sub-proof's check sets
them, and doorTerms (OnBytes/Model/Trees.lean) requires that there are R.

If rowForm is set, the other fields also say how coef is a product over the bits of a row's number,
which is the form in which the equation is passed to the chain. There are three such forms. (1)
rowOnes: 1 on every row. (2) rowLo and rowHi, one entry each for every bit, bit 0 first: coef[r] is
the product over the bits t of rowHi[t] if bit t of r is set, else rowLo[t]. (3) Otherwise:
coef[rowFirst + r] is the equality polynomial of rowPoint at r for r below 2^|rowPoint|, with
coordinate 0 of the point at the top bit of r, and 0 on all other rows; rowFirst is a multiple of
2^|rowPoint|.

This file does not compare coef with the form. rowWeights in OnBytes/Model/Trees.lean does, entry by
entry, in the run on a view; the dry run skips the comparison. -/
structure HRow where
  /-- the weights on the array's R rows -/
  coef : Array E := #[]
  /-- the weights that the claims have put on the row's K entries so far -/
  L : Array E := #[]
  /-- the first column that L holds; 0 in every row of a sub-proof -/
  L0 : Nat := 0
  /-- coef has one of the product forms -/
  rowForm : Bool := false
  /-- the product form is: 1 on every row -/
  rowOnes : Bool := false
  /-- the point of the equality polynomial -/
  rowPoint : Array E := #[]
  /-- for each bit of a row's number: the factor if the bit is 0 -/
  rowLo : Array E := #[]
  /-- for each bit of a row's number: the factor if the bit is 1 -/
  rowHi : Array E := #[]
  /-- the first row that the equality polynomial covers -/
  rowFirst : Nat := 0
  deriving Inhabited

/-- The two kinds of array. -/
inductive HKind where
  /-- a table -/
  | table
  /-- the symbols of one matrix of the smallness test (OnBytes/Model/Tail.lean) -/
  | symbols
  deriving DecidableEq, Repr, Inhabited

/-- An array that the claims of a sub-proof read. -/
structure HTree where
  /-- the array's name -/
  name : String := ""
  /-- which kind of array -/
  kind : HKind := .table
  /-- the number of rows -/
  R : Nat := 0
  /-- the number of columns -/
  K : Nat := 0
  /-- a mark: some number once the chain has received the array's commitment. Only whether it is
  there is read, not the number. -/
  root : Option Nat := none
  /-- the array is committed in this sub-proof, not in another -/
  owner : Bool := false
  /-- the virtual rows; a claim names one by its index here -/
  rows : Array HRow := #[]
  deriving Inhabited

/-! ## Affine forms -/

/-- One entry of a virtual row, with a coefficient. -/
structure Ent where
  /-- the number of the array in the sub-proof's list -/
  tree : Nat := 0
  /-- the number of the virtual row among the array's -/
  row : Nat := 0
  /-- the index of the entry in the row -/
  idx : Nat := 0
  /-- the coefficient -/
  coef : E := zeroE
  deriving Inhabited

/-- An affine form in hidden values: those under slots, and entries of virtual rows. A slot or an
entry may occur more than once; its coefficients then add.

Claims. While the messages are read, no equation is tested. Each algebraic check of a sub-proof
becomes a claim: an affine form that must be 0. A virtual row (HRow) is a public combination of the
rows of an array (HTree). -/
structure Aff where
  /-- the entries of virtual rows -/
  ents : Array Ent := #[]
  /-- the slots, each with its coefficient -/
  slots : Array (Nat × E) := #[]
  /-- the constant -/
  const : E := zeroE
  deriving Inhabited

namespace Aff

/-- The constant form v. -/
def ofConst (v : E) : Aff := { const := v }

/-- The hidden value under slot j. -/
def slot (j : Nat) : Aff := { slots := #[(j, oneE)] }

/-- Entry idx of virtual row number row of array number tree. -/
def ent (tree row idx : Nat) : Aff := { ents := #[{ tree, row, idx, coef := oneE }] }

/-- The form a + k b. -/
def addMul (a b : Aff) (k : E) : Aff where
  ents := b.ents.foldl (fun l x => l.push { x with coef := mulE x.coef k }) a.ents
  slots := b.slots.foldl (fun l x => l.push (x.1, mulE x.2 k)) a.slots
  const := addE a.const (mulE b.const k)

/-- The form k a. -/
def scale (a : Aff) (k : E) : Aff := addMul {} a k

/-- The sum of two forms. -/
instance : Add Aff := ⟨fun a b => addMul a b oneE⟩

/-- The difference of two forms. -/
instance : Sub Aff := ⟨fun a b => addMul a b (subE zeroE oneE)⟩

end Aff

/-! ## The state of one sub-proof -/

/-- A claim that a routine has left for its caller to add (see Fork.settle). -/
structure Owed where
  /-- a name for the claim, as in the C++ refusal internal-claim-not-added-<name>; nothing reads it
  here -/
  what : String
  /-- it has been added -/
  added : Bool := false
  deriving Inhabited

/-- The state of the check of one sub-proof: its arrays, what was shown for its hidden values, and
the weighted sum of its claims.

Hidden values. In the protocol the prover does not send a hidden value itself. It sends the value
plus a public factor times one entry of the mask row, a row that it has committed to and that an
honest prover fills with random elements. Every scalar that a sub-proof sends has a number, its
slot, counted from 0 in the order of sending, and entry j of the mask row belongs to slot j. The
hidden value under slot j is vp[j] - mf[j] * mask[j], where mf[j] is the factor and vp[j] is what
was shown: the scalar that was sent. A sumcheck's own scalars (the sum of its hiding polynomial and
what its rounds send) are the exception. They are sent without a mask, and pscRow
(OnBytes/Model/Psc.lean) puts a coefficient of the hiding polynomial under each of their slots, with
vp[j] = 0 and mf[j] = -1. Hidden is the name of a value's part in the protocol: nothing here claims
that a value stays hidden, or that a false claim is caught.

Names follow the C++ source. In identifiers a fork is a sub-proof, a tree is
an array (HTree, trees, Ent.tree), a row can also be the claim that a sumcheck leaves (pscRow,
rowMade), kap (kappa) is the weight theta^c of claim c, and a door (doorShutF; doorH in
OnBytes/Model/Trees.lean) is the step that passes the one equation to the chain. The slot counter,
an argument of the C++ routines, is the field next. A name that ends in F belongs to a field or
function by which the program guards the order of its own steps. E is the type of an element of the
extension field, the cubic extension of the integers modulo 2^64 - 2^32 + 1 (OnBytes/Base.lean).

Public numbers. The number of slots (the argument of Fork.slots, kept as ns), the number of claims
in the plan (planClaimsF), the number of slots that the messages have taken (the argument of
Fork.settle) and the shapes of the arrays are given by the caller. This file compares them with each
other where the C++ source does, and with nothing else. A few conditions on sizes are added where
the C++ source would read outside a vector (Fork.settle, claimsIn). The caller that makes the state
and passes the equation on (OnBytes/Model/Trees.lean and the checks of the three kinds of sub-proof)
must tie these numbers to the parameter bytes that the strict reader hashes.

What has no counterpart. The fields and routines of the C++ state that serve only its tests and its
log (the values of claims on a prover's data, names of sections) have no counterpart. Nor has the
sub-proof's prefix G_, which only begins the printed names of refusals (see SubM). -/
structure Fork where
  /-- the arrays that the claims read -/
  trees : Array HTree := #[]
  /-- the number of slots -/
  ns : Nat := 0
  /-- the slot of the next scalar that is sent -/
  next : Nat := 0
  /-- for each slot: what was shown -/
  vp : Array E := #[]
  /-- for each slot: the public factor of its mask entry -/
  mf : Array E := #[]
  /-- for each slot: the coefficient of its hidden value in the one equation -/
  LS : Array E := #[]
  /-- for each slot: a hidden value has been put under it -/
  gotF : Array Bool := #[]
  /-- the constant of the one equation -/
  c0 : E := zeroE
  /-- the number of claims added so far -/
  nClaim : Nat := 0
  /-- the element whose powers are the weights of the claims -/
  theta : E := zeroE
  /-- theta has been drawn -/
  thetaDrawnF : Bool := false
  /-- the number of claims in the plan -/
  planClaimsF : Nat := 0
  /-- for each claim of the plan: its weight has been handed out. Empty until t2Batch
  (OnBytes/Model/Trees.lean) sets it up. The marks are kept so that no number is handed out twice:
  the bound planClaimsF would not catch that. -/
  kapMapF : Array Bool := #[]
  /-- doorH (OnBytes/Model/Trees.lean) has begun. From then on Fork.push and Fork.kapTake refuse. -/
  doorShutF : Bool := false
  /-- the list of owed claims: those that routines have left for their callers to add -/
  owed : Array Owed := #[]
  deriving Inhabited

namespace Fork

/-- Notes that the chain has received the commitment of array number t. w: the mark to keep. -/
def rootTaken (F : Fork) (t w : Nat) : Fork :=
  { F with trees := F.trees.modify t fun X => { X with root := some w } }

/-- Sets up n slots, none of them filled. Fork.hide refuses until this has been called. -/
def slots (F : Fork) (n : Nat) : Fork :=
  { F with
    ns := n
    vp := Array.replicate n zeroE
    mf := Array.replicate n zeroE
    LS := Array.replicate n zeroE
    gotF := Array.replicate n false }

/-- Puts a hidden value under the free slot j: shownScalar - factor * (mask entry j). A second value
under one slot is refused, for two reasons. In the protocol a mask entry is used for one scalar. And
a form names a hidden value by its slot, for which vp and mf are put in only at the end
(Fork.settle), so a second value would change what the forms made before it mean. (C++:
internal-slot-marks, internal-slot-twice.) -/
def hide (F : Fork) (j : Nat) (shownScalar factor : E) : Option Fork :=
  if decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true then
    some { F with
      gotF := F.gotF.set! j true
      vp := F.vp.set! j shownScalar
      mf := F.mf.set! j factor }
  else none

/-- One step of hideRun: puts y under slot j and goes on to the next slot. -/
def hideStep (factor : E) : Nat × Fork → E → Option (Nat × Fork)
  | (j, G), y => (G.hide j y factor).map fun H => (j + 1, H)

/-- Puts the elements of v under the slots first, first + 1 and so on, all with one factor. -/
def hideRun (F : Fork) (first : Nat) (v : Array E) (factor : E) : Option Fork :=
  match v.foldlM (hideStep factor) (first, F) with
  | some x => some x.2
  | none => none

/-- What was shown for the hidden value under slot j. Refuses if the slot is still free. (C++:
internal-slot-order.) -/
def shown (F : Fork) (j : Nat) : Option E :=
  if decide (j < F.ns) && F.gotF.getD j false then some (F.vp.getD j zeroE) else none

/-- The form a with each hidden value under a slot replaced by what was shown for it, and without
its entries of virtual rows. -/
def publicPart (F : Fork) (a : Aff) : Option E :=
  a.slots.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y))
    a.const

/-- True if the arrays have the entry that x names, inside the columns that L holds. -/
def hasEnt (trees : Array HTree) (x : Ent) : Bool :=
  match trees[x.tree]? with
  | none => false
  | some X =>
    match X.rows[x.row]? with
    | none => false
    | some r => decide (r.L0 ≤ x.idx) && decide (x.idx - r.L0 < r.L.size)

/-- Adds w times the coefficient of x to the weight L of the entry that x names. (C++:
internal-L-row, internal-L-index.) -/
def pushEnt (w : E) (trees : Array HTree) (x : Ent) : Option (Array HTree) :=
  if hasEnt trees x then
    some (trees.modify x.tree fun X =>
      { X with rows := X.rows.modify x.row fun r =>
        { r with L := r.L.modify (x.idx - r.L0) fun v => addE v (mulE w x.coef) } })
  else none

/-- Adds w times the coefficient x.2 to the coefficient LS of slot x.1. ns: the number of slots.
(C++: internal-L-slot.) -/
def pushSlot (w : E) (ns : Nat) (LS : Array E) (x : Nat × E) : Option (Array E) :=
  if x.1 < ns then some (LS.modify x.1 fun v => addE v (mulE w x.2)) else none

/-- Adds w times the form a to the one equation. The fields trees and LS are taken out of the state
while they are changed, so that the compiled program changes them in place. (C++:
internal-f-door.) -/
def push (F : Fork) (w : E) (a : Aff) : Option Fork :=
  if F.doorShutF then none
  else
    let ns := F.ns
    let trees := F.trees
    let LS := F.LS
    let G := { F with trees := #[], LS := #[] }
    match a.ents.foldlM (pushEnt w) trees, a.slots.foldlM (pushSlot w ns) LS with
    | some trees', some LS' =>
      some { G with trees := trees', LS := LS', c0 := addE G.c0 (mulE w a.const) }
    | _, _ => none

/-- Takes the drawn element as theta. It is drawn once. (C++: internal-f-draws.) -/
def batchBy (F : Fork) (drawn : E) : Option Fork :=
  if F.thetaDrawnF then none else some { F with theta := drawn, thetaDrawnF := true }

/-- The weight of claim number c, counted from 0 in the order of the plan: theta^c. No weight is
given before theta is drawn. This function leaves no mark in kapMapF; Fork.lin and t2Lin
(OnBytes/Model/Trees.lean) take their weights by Fork.kap, that is, by kapTake. (C++:
internal-f-draws.) -/
def kapAt (F : Fork) (c : Nat) : Option E :=
  if F.thetaDrawnF then some (powE F.theta c) else none

/-- Hands out the weight of claim number c. Once kapMapF is set up, c must be a claim of the plan
whose weight has not been handed out. (C++: internal-f-door, internal-f-draws.) -/
def kapTake (F : Fork) (c : Nat) : Option (E × Fork) :=
  if F.doorShutF then none
  else if F.kapMapF.isEmpty then (F.kapAt c).map fun k => (k, F)
  else if decide (c < F.planClaimsF) && F.kapMapF.size == F.planClaimsF &&
      !F.kapMapF.getD c true then
    (F.kapAt c).map fun k => (k, { F with kapMapF := F.kapMapF.set! c true })
  else none

/-- True if the weight of every claim of the plan has been handed out. (C++: internal-f-draws.) -/
def kapAllTakenF (F : Fork) : Bool :=
  F.kapMapF.size == F.planClaimsF && F.kapMapF.all id

/-- Hands out the weight of the next claim and adds 1 to nClaim. -/
def kap (F : Fork) : Option (E × Fork) :=
  (F.kapTake F.nClaim).map fun x => (x.1, { x.2 with nClaim := x.2.nClaim + 1 })

/-- Puts on the list of owed claims a claim that the caller must add later. Returns its index. -/
def owe (F : Fork) (what : String) : Nat × Fork :=
  (F.owed.size, { F with owed := F.owed.push { what } })

/-- Marks claim number i of the list of owed claims as added. -/
def paid (F : Fork) (i : Nat) : Fork :=
  { F with owed := F.owed.modify i fun o => { o with added := true } }

/-- Adds the claim that the form f is 0.

One equation. The claims are added up, claim number c with the weight theta^c, where theta is drawn
after all messages of the sub-proof. So a routine that reads messages returns its claims as forms,
and its caller adds them with SubM.lin in a second pass, after theta is drawn. This file collects
the coefficients of the sum: the weights L on each virtual row, LS on the slots, and the constant
c0. Fork.settle writes the sum as the one equation. -/
def lin (F : Fork) (f : Aff) : Option Fork :=
  F.kap.bind fun x => x.2.push x.1 f

/-- One step of settle, for slot j with the coefficient l: the coefficient of the slot's mask entry
is - l * mf[j], and l * vp[j] is added to the constant. A slot with a coefficient must be filled. -/
def settleStep (F : Fork) : Nat × Array E × E → E → Option (Nat × Array E × E)
  | (j, maskCoef, constant), l =>
    if isZeroE l then some (j + 1, maskCoef, constant)
    else if F.gotF.getD j false then
      some (j + 1, maskCoef.set! j (subE zeroE (mulE l (F.mf.getD j zeroE))),
        addE constant (mulE l (F.vp.getD j zeroE)))
    else none

/-- The one equation, written on the mask row itself: (the sum over the virtual rows of L times the
row's entries) + sum_j maskCoef[j] * (mask entry j) + constant = 0. Returns maskCoef and the
constant. used: the number of slots that the messages of the sub-proof have taken. Each of them must
be filled by now, with a hidden value that was shown or with a coefficient of a hiding polynomial.
The slots of such coefficients are filled only where the claim of a sumcheck is made, so a sumcheck
whose claim was never made is found here. Every claim in the list of owed claims must be marked as
added (Fork.paid); the caller sets that mark, and nothing compares it with what was added. Whether a
claim that was made was also added is not tested here. doorH (OnBytes/Model/Trees.lean) tests it by
counting: nClaim must be planClaimsF, and every weight must have been handed out (SubM.allTaken). On
the slots from used on, see SubM. (C++: internal-slot-marks, internal-claim-not-added-<name>,
internal-slot-unused, internal-slot-order.) -/
def settle (F : Fork) (used : Nat) : Option (Array E × E) :=
  if decide (used ≤ F.ns) && F.gotF.size == F.ns && F.LS.size == F.ns && F.vp.size == F.ns &&
      F.mf.size == F.ns && F.owed.all (·.added) && F.gotF.all id 0 used then
    match F.LS.foldlM (settleStep F) (0, Array.replicate F.ns zeroE, F.c0) with
    | some x => some x.2
    | none => none
  else none

/-- Frees the weights L of all virtual rows. A sub-proof's plan (for example
OnBytes/Model/LayerPlan.lean) keeps its state without them, to save memory. fillL allocates them
again. -/
def trimL (F : Fork) : Fork :=
  { F with trees := F.trees.map fun X =>
    { X with rows := X.rows.map fun r => { r with L := #[] } } }

/-- Gives every virtual row its K weights L, all 0. -/
def fillL (F : Fork) : Fork :=
  { F with trees := F.trees.map fun X =>
    { X with rows := X.rows.map fun r => { r with L := Array.replicate X.K zeroE } } }

end Fork

/-! ## The type of a sub-proof's routines -/

/-- A routine of a sub-proof's check: a block (Blk, OnBytes/Iop/Ground.lean) that also changes the
state of the sub-proof (Fork).

Words. A sub-proof is one part of a request's proof (OnBytes/Model/Frame.lean). The chain is the
sequence of rounds, each a message of the prover and a draw of the verifier, on which all sub-proofs
of a request run (OnBytes/Model/Rounds.lean). The plan is the chain's public list of rounds, each
with its name and sizes. A sub-proof's own plan fixes its numbers of slots and claims. The strict
reader is Fmt.readChainX (OnBytes/Base.lean).

How it is written. A routine in Blk, the type in which messages are received and rounds are closed,
is run in two ways. The dry run, in which every received or drawn value is 0, gives the description
of the rounds. The run on a view, that is, on what was read from a file, gives the decision. The
steps on the state are plain functions on Fork. They return none where the C++ verifier refuses.
Whether a step returns none depends on public numbers and on the order of the calls, not on a value
that was received or drawn. There is one exception. A slot whose number is used (the argument of
Fork.settle) or more must be filled only if its coefficient in LS is not 0, and LS depends on what
was drawn: in a dry run most coefficients are 0. (t2Batch in OnBytes/Model/Trees.lean requires that
used is ns, and then there is no such slot.) A step that returns none has no name of its own: in
SubM it fails under the general name refused (unnamed, OnBytes/Iop/Ground.lean). The C++ verifier
prints the sub-proof's prefix (for example H:) and then a name that begins with internal-. That name
is given in brackets at each function. It points to a fault in the calling code or in the plan, not
in the proof. -/
abbrev SubM : Type → Type := StateT Fork Blk

namespace SubM

/-- Changes the state by a step that may refuse. -/
def change (f : Fork → Option Fork) : SubM Unit := fun F c => (f F).map fun G => (((), G), c)

/-- Changes the state by a step that may refuse and that returns a value. -/
def take {α : Type} (f : Fork → Option (α × Fork)) : SubM α :=
  fun F c => (f F).map fun x => (x, c)

/-- Reads a value off the state by a function that may refuse. -/
def ask {α : Type} (f : Fork → Option α) : SubM α := fun F c => (f F).map fun a => ((a, F), c)

/-- A public condition: fails unless b is true, in the dry run and on a view. -/
def must (b : Bool) : SubM Unit := StateT.lift (Blk.must b)

/-- A condition on values: fails unless b is true; idle in the dry run. -/
def test (b : Bool) : SubM Unit := StateT.lift (Blk.test b)

/-- Unwraps x, for an x whose presence depends only on public numbers. Fails, in the dry run too, if
x is none. -/
def get {α : Type} (x : Option α) : SubM α := StateT.lift (Blk.get x)

/-! ### The routines on the chain -/

/-- Receives the next n elements of the prover's open message. It takes no slots; the caller does
(takeSlots). -/
def read (n : Nat) : SubM (Array E) := StateT.lift (trRead n)

/-- Receives the next element of the prover's open message as the sum of a hiding polynomial. It
must be the last element of that message. That is not tested here (trSum,
OnBytes/Model/Rounds.lean). -/
def readSum : SubM E := StateT.lift trSum

/-- Ends the prover's open message and returns the one element that the verifier drew. r: the
round's name, which must be that of the plan's next entry. -/
def answer (r : RoundName) : SubM E := StateT.lift (trAnswer r)

/-- As answer, for an element that is drawn by the rule that never gives 0. That rule is the strict
reader's. It is not tested here, and in the dry run the element is 0. -/
def answerNotZero (r : RoundName) : SubM E := StateT.lift (trAnswerNotZero r)

/-- Ends the prover's open message and returns the n elements that the verifier drew. r: as in
answer. -/
def point (r : RoundName) (n : Nat) : SubM (Array E) := StateT.lift (trPoint r n)

/-- The round that batches the given number of rows. Returns that many powers of the drawn element,
from its power 0. -/
def batch (rows : Nat) : SubM (Array E) := StateT.lift (trBatch rows)

/-- The round that batches rows, for a caller that makes the rows only after the draw. Returns the
drawn element. The caller must then call batchRows. -/
def batchOpen : SubM E := StateT.lift trBatchOpen

/-- On a view: fails unless the plan's entry of the round that was closed last batches this number
of rows. The dry run only notes that the question was asked. -/
def batchRows (rows : Nat) : SubM Unit := StateT.lift (trBatchRows rows)

/-- Ends the prover's message in a round in which the verifier draws nothing. -/
def empty (r : RoundName) : SubM Unit := StateT.lift (trEmpty r)

/-- Ends the prover's open message and returns the matrix that the verifier drew, column by column.
It has entries -1, 0 and 1 and the given number of columns. A column has one entry for each
combination. -/
def trits (columns combinations : Nat) : SubM (Array Int) :=
  StateT.lift (trTrits columns combinations)

/-! ### Slots and hidden values -/

/-- Fork.slots as a routine. -/
def slots (n : Nat) : SubM Unit := change fun F => some (F.slots n)

/-- Fork.rootTaken as a routine. -/
def rootTaken (t w : Nat) : SubM Unit := change fun F => some (F.rootTaken t w)

/-- The slot of the next scalar that is sent. -/
def slot : SubM Nat := ask fun F => some F.next

/-- Takes the next n slots. Returns the first of them. -/
def takeSlots (n : Nat) : SubM Nat := take fun F => some (F.next, { F with next := F.next + n })

/-- Fork.hide as a routine. -/
def hide (j : Nat) (shownScalar factor : E) : SubM Unit := change (·.hide j shownScalar factor)

/-- Fork.shown as a routine. -/
def shown (j : Nat) : SubM E := ask (·.shown j)

/-- Fork.publicPart as a routine. -/
def publicPart (a : Aff) : SubM E := ask (·.publicPart a)

/-- Receives n hidden values that are sent outside a sumcheck, as part of one message. What is sent
for each is the value plus its mask entry (factor 1). Returns the first one's slot. No claim is
added here; the name is the C++ routine's. -/
def claimsIn (n : Nat) : SubM Nat := do
  let v ← read n
  must (v.size == n)
  let j ← takeSlots n
  change (·.hideRun j v oneE)
  pure j

/-! ### Claims -/

/-- Fork.batchBy as a routine. -/
def batchBy (drawn : E) : SubM Unit := change (·.batchBy drawn)

/-- Fork.kap as a routine. -/
def kap : SubM E := take (·.kap)

/-- Fork.push as a routine. -/
def push (w : E) (a : Aff) : SubM Unit := change (·.push w a)

/-- Fork.lin as a routine. -/
def lin (f : Aff) : SubM Unit := change (·.lin f)

/-- Sets the number of claims in the plan. -/
def setPlanClaims (n : Nat) : SubM Unit := change fun F => some { F with planClaimsF := n }

/-- The number of claims added so far. -/
def claims : SubM Nat := ask fun F => some F.nClaim

/-- Fails unless the weight of every claim of the plan has been handed out. -/
def allTaken : SubM Unit := ask fun F => if F.kapAllTakenF then some () else none

/-- Fork.owe as a routine. -/
def owe (what : String) : SubM Nat := take fun F => some (F.owe what)

/-- Fork.paid as a routine. -/
def paid (i : Nat) : SubM Unit := change fun F => some (F.paid i)

/-- Fork.settle as a routine. -/
def settle (used : Nat) : SubM (Array E × E) := ask (·.settle used)

end SubM

end OnBytes.Model
