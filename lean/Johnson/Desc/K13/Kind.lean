-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Kind.lean: kind K13, THE MEMBERS' BATCHING AND THE LINEAR CLAIM's FIRST PART, as
blocks (Johnson/Desc/Block.lean). Definitions with code; no theorem. The functions that decide are
Johnson/Desc/K13/Text.lean's. GENERAL IN THE STATE: a block is typed at any state T with a lens to
the part that the kind reads and writes; general in the type of claims: none has a claim. A refusal
bears the name of the test that refused.

ONE BLOCK FOR EACH OF THE CHAIN's END's NAMES: frontB (no round); claimCombinationBlock (2 + kCol rounds); quietB
(no round); then another kind's block, W's commitment; rowsB (no round). The seal is the fold's own.
frontB, claimCombinationBlock AND quietB BEAR ONE PLACE: as a list they fail the format's test that no two blocks
stand at one place: they stand joined, as one block (Johnson/Desc/K13/AtS.lean: atM3).
WHERE THE PILE HAS ONE ROW there is no batching: the plan has no such rounds, and the chain's table
of places has no place of this kind. oneRowB stands for frontB, claimCombinationBlock and quietB there: the one row
is the claim. It has run at a made-up state alone: no stored proof has such a plan.
"K13.rows-counted" asks of the pile what "K13.pile-count" has asked at the front: in the joined
block it is shadowed; it stays, because it pays the debt of rows that the batching's own entry
counts.
Compiled; run by the format's step at the real border of two stored proofs, and in the fold over
blocks at its place on a proof file's first chain.

What is not claimed. That a yes of these blocks means anything: that is the matter of the kind's
laws, and no theorem stands in this file. No block here tests a value: a false row on the pile shows
only as a false row handed on. That the rounds which claimCombinationBlock declares are the plan's: the format's
test on the plan asks it, not this file. Three tests of the functions that decide have no control
that reaches them: "K13.mask-sent", "K13.message-W" and "K13.a-coefficient-a-row". oneRowB has run
at a made-up state alone. That a word of a sent or drawn element is below the field's prime: that
test belongs to the fold. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.Block
import Johnson.Desc.K13.Text

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13
open OnBytes OnBytes.Params
open Johnson.Desc.First.ForkGround (RowsOwed)

/-- The numbers of the kind's places. -/
structure Where where
  chain : Nat
  /-- the number, behind the links, of the place of the front, the batching and the quiet part -/
  piece : Nat
  /-- the number of the place behind W's commitment -/
  pieceRows : Nat
  /-- the rows that the links leave on the table -/
  rows : Nat
  /-- a reply is due on this chain: a proof file's first chain hears one; a key file's hears none -/
  reply : Bool := true
  /-- the shape of the test on the table, a record of the plan's numbers; its kCol: the matrix has
  2 ^ kCol columns. Where it is read off the made plan, the test of the rounds against the plan's is
  idle for what hangs on it -/
  lin : LinShape
  /-- the bits of proof of work of "BAT-sigma", of "PSC epsilon", of a "PSC round" -/
  work : Nat × Nat × Nat := (0, 0, 0)
  /-- how many oracle messages the chain has sent in front of the batching -/
  sent : Nat

/-- What the kind reads and writes of the state. -/
structure Part where
  /-- the rows that are still owed a count -/
  owed : RowsOwed
  /-- the reply as it was heard; the message of index masks; the pile -/
  heard : Option E
  indexMasks : Nat
  pile : List TensorRow
  /-- what W's message holds; the numbers of the messages sent with W -/
  msg : Array OracleNotice
  ids : Array Nat
  /-- nothing in front of the batching; behind it the claim; behind W's commitment all five -/
  lin : Option LinFirst
  d : St

/-- The part inside a state T. enter: the chain comes to its end; nothing where it cannot: it stands
in a link, or at its end already. get?: nothing elsewhere than at the end. -/
structure Lens (T : Type) where
  enter : T → Option T
  get? : T → Option Part
  set : T → Part → T

variable {T Cl : Type}

/-- The part, or a refusal under a name. -/
def Lens.part (X : Lens T) (t : T) : Ans Part := there "K13.at-the-chain's-end" (X.get? t)

/-! ## ROUNDS -/

def sigmaEntry (p : Where) : Fmt.Entry :=
  { name := "BAT-sigma", work := p.work.1, drawE := 1, rows := p.rows }

/-- One element is sent: 24 bytes. -/
def epsEntry (p : Where) : Fmt.Entry :=
  { name := "PSC epsilon", work := p.work.2.1, msg := 24, drawE := 1 }

/-- Two elements are sent. -/
def roundEntry (p : Where) : Fmt.Entry :=
  { name := "PSC round", work := p.work.2.2, msg := 48, drawE := 1 }

def battRounds (p : Where) : List Fmt.DeclaredRound :=
  { entry := sigmaEntry p } :: { entry := epsEntry p } ::
    List.replicate p.lin.kCol { entry := roundEntry p }

/-! ## READS: nothing -/

/-! ## DECIDES -/

/-- A block of the kind without a round. -/
def still (name : String) (p : Where) (piece : Nat) (f : T → Ans T) : Block T Cl :=
  { name := name, place := ⟨p.chain, none, piece, .K13⟩, planOk := true, rounds := [], oracles := []
    before := [], decide := fun t _ _ => f t, claims := [], after := [] }

/-- **The front.** The chain comes to its end. -/
def frontB (X : Lens T) (p : Where) : Block T Cl :=
  still "K13: the front" p p.piece fun t => do
    let t₁ ← there "K13.comes-to-the-end-once" (X.enter t)
    let s ← X.part t₁
    front s.d.st p.lin s.indexMasks s.pile p.reply s.heard p.rows
    pure t₁

/-- **The batching.** FIXED BEFORE THE DRAW: every oracle message that the chain has sent so far. -/
def claimCombinationBlock (X : Lens T) (p : Where) : Block T Cl :=
  { name := "K13: the batching"
    place := ⟨p.chain, none, p.piece, .K13⟩
    planOk := decide (1 < p.rows)
    rounds := battRounds p
    oracles := List.replicate (2 + p.lin.kCol) []
    before := (List.range p.sent).map fun n => (p.chain, n)
    decide := fun t rs _ => do
      let s ← X.part t
      need "K13.batched-once" s.lin.isNone
      let o ← batt s.owed p.lin.kCol p.rows s.pile s.indexMasks s.d rs
      pure (X.set t { s with owed := none, lin := some { claim := memberClaim o.1 }, d := o.2 })
    claims := []
    after := [] }

/-- **In front of W's commitment.** -/
def quietB (X : Lens T) (p : Where) : Block T Cl :=
  still "K13: in front of W" p p.piece fun t => do
    let s ← X.part t
    need "K13.claim-laid" s.lin.isSome
    let msg ← quiet s.d.st.codes p.lin
    pure (X.set t { s with msg := msg })

/-- **Behind W's commitment.** -/
def rowsB (X : Lens T) (p : Where) : Block T Cl :=
  still "K13: the own group and (Eval)" p p.pieceRows fun t => do
    let s ← X.part t
    let l ← there "K13.claim-laid" s.lin
    let o ← rows p.lin l.claim s.ids s.d
    pure (X.set t { s with lin := some o.1, d := o.2 })

/-- **Where the pile has one row**: the front; the one row is the claim; in front of W. No round. -/
def oneRowB (X : Lens T) (p : Where) : Block T Cl :=
  { still "K13: the one row" p p.piece (fun t => do
      let t₁ ← (frontB (Cl := Cl) X p).decide t [] []
      let s ← X.part t₁
      let one ← there "K13.one-row" (match s.pile with | [r] => some r | _ => none)
      (quietB (Cl := Cl) X p).decide (X.set t₁ { s with lin := some { claim := memberClaim one } })
        [] []) with
    planOk := p.rows == 1 }

/-! ## SENDS: not written in this file (Johnson/Desc/ProofFile/Honest/K13/Part.lean) -/

end VerifiableInference.Desc.K13
