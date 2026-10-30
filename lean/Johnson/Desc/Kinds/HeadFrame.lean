-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadFrame.lean: a part of THE OUTPUT HEAD'S OWN ROUNDS (Head.lean): how the
kind's text meets the carried record of the format of a block (Johnson/Desc/Block.lean): the place's
public parameters; what the kind reads of the record and lays into it; and, written once, the way
from the record to the classes in which the kind's formulas find their letters. It shows nothing by
itself. Definitions with code; no theorem.

The carried record S is a letter: Seat S says what this kind reads of it and lays into it.
STAND-INS. The hearing runs on the sub-proof's ledger (`verify-on-bytes`'s Fork). In
front of it the stretch's rounds are held against their entries by a strict reading
(Johnson/Desc/First/Tape/Tape.lean: tapeT), whose value is not used.

-/
import Johnson.Desc.Block
import Johnson.Desc.Kinds.HeadIn
import Johnson.Desc.Kinds.HeadOk
import Johnson.Desc.First.Tape.Tape
import Johnson.Desc.Kinds.ReplyKind
import Decl.Declared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open OnBytes (E)
open OnBytes.Model (Fork)

/-- This kind in the format's list of kinds. -/
abbrev outputHead : KindName := .K6

/-- THE PLACE'S PUBLIC PARAMETERS: numbers of the plan alone. sT: the table's exponent. floor: the
least allowed logarithm of a call's number of keys. work: the setting's bits of work in front of a
challenge whose error is a field's. before: the oracle messages that must have been sent before the
place's first draw, each by its chain and its number of sending: those that hold the head's cells
and the stream's cells. -/
structure Par where
  sizes : Sizes
  policy : Policy
  sT : Nat
  floor : Nat
  work : Nat
  before : List (Nat × Nat)

/-- WHAT THE KIND ASKS OF THE CARRIED RECORD. Read: the request as far as it is public (its tokens
and two positions, laid where the record begins; never the client's next token); the one seat of the
heard next token (the next token's block lays it); the ledger; the lookup's point and its calls' key
points; where the reads lie. Laid at the hearing: the ledger; what was heard; the claim on the
weights, for the merge. THE SEAT HAS A SETTER FOR THAT CLAIM AND NO READER: at the proof file's
description's seat the setter leaves the record as it is (Johnson/Stored/HeadSeatAt.lean), and the
claim that the merge takes is laid by the quiet step behind the lookup on the digits
(Johnson/Desc/First/Look/K3Whole.lean: quietHead, from First.Look.weightsClaim). Handed to the seat
with the claims: the calls' key vectors (setKeyForms): THE SEAT HAS NO READER FOR THEM: the run
"join" makes the key vectors itself (HeadCaller.lean: callerKeys). THE LEDGER AND WHAT WAS HEARD ARE
LAID OR REFUSED: a record that has no place for them (it does not stand in the head's link) says so
under a name; nothing is laid aside in silence. -/
structure Seat (S : Type) extends Reply.Seat S where
  request : S → Request
  ledger : S → Fork
  lookup : S → Option (Point × (Nat → Point))
  reads : S → Option (FinalNorm.Reads × Reads)
  heard : S → Option HeardAll
  setLedger : S → Fork → Except String S
  setHeard : S → HeardAll → Except String S
  setWeightClaim : S → SumOnMatrix → S
  setKeyForms : S → List Form → S

variable {S : Type}

/-- The tests on the plan alone (HeadOk.lean). -/
def Par.ok (p : Par) : Bool :=
  let _ := p.sizes; let _ := p.policy
  planOk p.sT

/-- The kind's part of the test on the instance. -/
def Par.okStart (p : Par) (q : Request) : Bool :=
  let _ := p.sizes; let _ := q
  Request.ok

/-- For the lookup's test on the plan: the places that the key forms treat as padding. -/
def Par.paddingPlaces (p : Par) (perTree : Nat) : List Nat :=
  let _ := p.sizes
  Head.paddingPlaces p.floor perTree

/-- Rounds as data, as the plan's declared rounds; none opens a tree or a stored table. -/
def Par.declare (p : Par) (rs : List Round) : List Fmt.DeclaredRound :=
  rs.map fun r => { entry := r.entry p.work }

/-- The letters in front of the hearing. calls: for each call of the lookup its padding's term and
its keys. -/
class Given where
  sizes : Sizes
  policy : Policy
  request : Request
  token : Token
  normIn : FinalNorm.In
  headIn : In
  calls : List (E × List PlaceKey)
attribute [reducible, instance] Given.sizes Given.policy Given.request Given.token Given.normIn
  Given.headIn

/-- The letters behind the hearing. -/
class Behind where
  norm : Norm.Heard
  final : FinalNorm.Heard
  head : Heard
attribute [reducible, instance] Behind.norm Behind.final Behind.head

/-- The letters behind the sending of the reads. -/
class Places where
  final : FinalNorm.Reads
  head : Reads
attribute [reducible, instance] Places.final Places.head

/-- The letters in front of the hearing, out of the record: the next token through its one seat;
what comes in from the lookup by HeadIn.lean. A refusal bears its test's name. The third test is ON
THE CARRIED RECORD ALONE: it guards the text in front of this one, not the prover: the kind's
formulas take zl and zt off the end of the lookup's point, and of each call's key point its first
coordinates alone: that every key point has just these and lt more, and ends in (zl, zt), follows
from how the lookup makes them, at a plan that passes the lookup's own test; `verify-on-bytes` asks
it here once more, of its own record, and so does this text: no proof file can reach it. -/
def given (p : Par) (L : Seat S) (s : S) : Except String Given := do
  let z ← named "the lookup's points are laid" (L.lookup s)
  let y ← named "a next token was heard" (Reply.token L.toSeat s)
  let _ := p.sizes
  let i := fromLookup p.floor z.1 z.2
  need "the calls' key points end in the lookup's point" <|
    i.calls.zipIdx.all fun c =>
      (z.2 c.2).size == lJ p.floor c.1.2 + Norm.lt &&
        (z.2 c.2).last (Norm.ls + Norm.lt) == z.1.last (Norm.ls + Norm.lt)
  pure { sizes := p.sizes, policy := p.policy, request := L.request s, token := ⟨y⟩,
         normIn := i.norm, headIn := i.head, calls := i.calls }

/-- DECIDES, of a hearing and its rounds as data: the hearing on the place's own rounds, read
strictly; the rounds that batch rows ask for their rows themselves. No column is owed. The ledger,
what was heard and the claim on the weights are laid. (Of that claim the seat has a setter and no
reader: see Seat, above.) -/
def decideBy (rounds : Given → List Round) (hear : Given → Hear HeardAll)
    (weights : Given → Behind → SumOnMatrix) (p : Par) (L : Seat S) (s : S) (rs : List Fmt.RoundView) :
    Except String S := do
  let g ← given p L s
  let _ ← named "the rounds' shape" <|
    First.Tape.tapeT { rows := fun e => e.name == "BAT-sigma" } rs
      ((p.declare (rounds g)).map (·.entry))
  let (H, F, left) ← named "the hearing" (hear g (L.ledger s) rs)
  need "the hearing uses the rounds up" left.isEmpty
  let s1 ← L.setLedger s F
  let s2 ← L.setHeard s1 H
  pure (L.setWeightClaim s2 (weights g ⟨H.1, H.2.1, H.2.2⟩))

/-- All letters, at a record behind the hearing and the sending of the reads. -/
def lettersAt (p : Par) (L : Seat S) (s : S) : Except String (Given × Behind × Places) := do
  let g ← given p L s
  let H ← named "the place's rounds were heard" (L.heard s)
  let x ← named "the reads' places are laid" (L.reads s)
  pure (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩)

/-- CLAIMS, of named runs of forms and of the calls' key vectors: the first run also hands the key
vectors to the seat (setKeyForms), WHICH HAS NO READER FOR THEM: the lookup's join, next in the
link's order, takes the key vectors from callerKeys (HeadCaller.lean), which makes them itself. Cl:
the type of a claim, a letter; toCl: from a form. -/
def runsBy {Cl : Type} (names : List String)
    (runs : Given → Behind → Places → List (String × List Form))
    (keys : Given → Behind → Places → List Form) (toCl : Form → Cl) (p : Par) (L : Seat S) :
    List (String × (Nat → S → Except String (List Cl × S))) :=
  names.map fun name => (name, fun _ s => do
    let (g, b, x) ← lettersAt p L s
    let fs ← named "the run is there" ((runs g b x).lookup name)
    pure (fs.map toCl, if names.head? == some name then L.setKeyForms s (keys g b x) else s))

/-- The key vector of one call of the lookup, at the call's point: its padding's term, then its
keys: the normalization's by HeadNorm.lean (the row has 21 digits of the head's behind the
normalization's 99), the head's by the function handed in. -/
def keyVector [Sizes] [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]
    (key : Key → Form) (padding : E) (keys : List PlaceKey) : Form :=
  (keys.map fun | .inl k => FinalNorm.key 21 k | .inr k => key k).foldl (· + ·) (padding : Form)

/-- A guest, as a host takes it: handed before anything is heard. coords: which coordinates of the
host's point it borrows, and its degree in each. form: its test, which the host calls behind its
last borrowed draw. -/
structure GuestOf (S Cl : Type) where
  name : String
  coords : List (Nat × Nat)
  form : S → Except String Cl

end VerifiableInference.Desc.Kinds.Head
