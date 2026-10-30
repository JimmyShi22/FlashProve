-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Kind.lean: kind K9, THE BATCHING DRAW AND THE ONE EQUATION, as blocks of a
segment (Johnson/Desc/Block.lean, where a segment is the record Link). Definitions
with code; no theorem. The functions that decide are Johnson/Desc/First/Batch/Text.lean's,
Johnson/Desc/First/Batch/Sums.lean's and, for the adding, Johnson/Desc/First/Batch/Add.lean's; a
claim is Johnson/Desc/Claim.lean's.
NONE OF THESE BLOCKS STATES A RUN OF CLAIMS OR A RUN BEHIND THE BATCHING (claims := [], after :=
[]): the format asks the batching's block and the closing's blocks to be bare.
GENERAL IN THE STATE: a block is typed at any state T with a lens to the part that the kind reads
and writes. A refusal bears the name of the test that refused.

A segment's flat list of blocks is: laid, the blocks that hear, THE BATCHING, the runs behind the
batching, the closing's blocks, cleared. K9 gives two of these: `batch`, the batching, and
`oneEquation`, the first block of the closing. `drawAlone` is the batching without the claims, and
`adds` a block without a round that runs a function of claims and adds them WHERE IT STANDS: for a
fold in which some kinds add their claims themselves. A claim takes its number when it is
added: so `adds` stands just where `verify-on-bytes`'s step adds these claims.
WHAT A ROUND HOLDS AND DRAWS IS ASKED ONCE, IN FRONT: the round is data of the block (ROUNDS), and
the format's step holds the view's round against it (roundsFit) before it decides. So the block's
decision does not call K9.draw, which asks seven such clauses of an entry and a round that are
handed to it, but K9.drawn: the five tests that are left, at the element read.
Johnson/Desc/First/Batch/Fits.lean proves that, where roundsFit has said yes, the two return the
same. THE LEDGER IS EMPTY WHEN chi IS DRAWN ("K9.ledger-empty"): no weight on an entry, no
coefficient on a slot, no constant. `verify-on-bytes` does not ask it. What stood in the ledger
would be added to the one equation under the weight 1 and could cancel the first claim: the kind's
lemma needs it. AND NO CLAIM HAS BEEN COUNTED YET ("K9.no-claim-yet"): the claims are numbered from
0. AND THE LEDGER HAS ONE COEFFICIENT FOR EACH SLOT ("K9.a-coefficient-a-slot"): the equation's own
test asks it again behind the adding.
Where.sent IS A BARE NUMBER OF THE PLACE: "fixed before the draw" is as true as whoever fills
it; no test of this kind ties it to the chain's declared sendings.
TWO TESTS ON VALUES (K9.no-weight-outside, K9.row-form-values) are, in `verify-on-bytes`, tests that
refuse at once on a view and are skipped in its dry run; here they are always asked. The state's
mark of a failed test is neither read nor written by this kind.
"EVERY SENT SCALAR STANDS IN A CLAIM" (K9.freeSlot, Johnson/Desc/First/Batch/Sums.lean) IS ASKED
ONCE, by the block of the tests behind the adding (Johnson/Desc/First/Batch/Tests.lean), the last of
the batching's place; not here. THIS TEXT HAS NOT RUN ON A PROOF.


-/
import OnBytes.Model.Tail
import Johnson.Desc.Block
import Johnson.Desc.Claim
import Johnson.Desc.First.Batch.Sums
import Johnson.Desc.First.Batch.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- The numbers of a place of the kind. -/
structure Where where
  chain : Nat
  link : Nat
  /-- the number of the batching's block inside its segment -/
  piece : Nat
  /-- the number of the equation's block inside its segment -/
  pieceEq : Nat
  /-- the rows that chi combines: the segment's claims and the smallness test's equations -/
  rows : Nat
  /-- the bits of proof of work of the round -/
  work : Nat := 0
  /-- how many oracle messages the chain has sent in front of the round -/
  sent : Nat

/-- What the kind reads and writes of the state. -/
structure Part where
  /-- the rows that are still owed a count -/
  owed : RowsOwed
  /-- the slots that the segment's messages have taken -/
  used : Nat
  /-- the indices that the smallness test's equations take; nothing before they are made -/
  laid : Option Nat
  /-- the segment's book-keeping; its ledger, which holds the sums; the statement -/
  L : LinkCtx
  F : Fork
  d : St Unit

/-- The part inside a state T; nothing where no segment is open. -/
structure Lens (T : Type) where
  get? : T → Option Part
  set : T → Part → T

variable {T Cl : Type}

/-- The part, or a refusal under a name. -/
def Lens.part (X : Lens T) (t : T) : Ans Part := there "K9.in-a-segment" (X.get? t)

/-! ## ROUNDS: one round; the prover sends nothing; one element is drawn -/

def entry (p : Where) : Fmt.Entry :=
  { name := "BAT-sigma", work := p.work, drawE := 1, rows := p.rows }

/-! ## READS: nothing -/

/-! ## DECIDES -/

/-- The batching draw behind the format's test on the round. rows: the rows that the entry counts.
chi: the element drawn. The tests are K9.draw's own five that speak of the state, under the same
names, in the same order. -/
def drawn (rows : Nat) (chi : E) (owed : RowsOwed) (used : Nat) (L : LinkCtx) (F : Fork) :
    Ans Drawn := do
  need "K9.nothing-owed" owed.isNone
  need "K9.slots-used" (L.list.planned && used == F.ns)
  need "K9.link-ready" (L.list.link && !L.handed && L.moments == L.check.momentsOf L.link)
  need "K9.drawn-once" !F.thetaDrawnF
  need "K9.claims-planned" (F.planClaimsF != 0)
  pure
    { owed := some rows
      L := { L with list := { L.list with used := used }, handed := true }
      F := { t2FillL F L.list with
        theta := chi, thetaDrawnF := true, kapMapF := Array.replicate F.planClaimsF false } }

/-- No weight on an entry, no coefficient on a slot, no constant. -/
def ledgerEmpty (F : Fork) : Bool :=
  (F.trees.all fun X => X.rows.all fun r => r.L.all isZeroE) && F.LS.all isZeroE && isZeroE F.c0

/-- The batching draw at an empty ledger: K9.drawn's five tests, then these three. -/
def drawnClean (rows : Nat) (chi : E) (owed : RowsOwed) (used : Nat) (L : LinkCtx) (F : Fork) :
    Ans Drawn := do
  let o ← drawn rows chi owed used L F
  need "K9.ledger-empty" (ledgerEmpty F)
  need "K9.no-claim-yet" (F.nClaim == 0)
  need "K9.a-coefficient-a-slot" (F.LS.size == F.ns)
  pure o

/-- The one element that the round has drawn: a reading of what roundsFit has passed. -/
def chiOf (r : Fmt.RoundView) : Ans E :=
  there "K9.one-element"
    (match r.drawn.elems with
     | [x] => some (E.ofTriple x)
     | _ => none)

/-- The draw alone: chi is stored; the entry's rows are owed. No claim is made or added. General in
the type of claims. -/
def drawAlone (X : Lens T) (p : Where) : Block T Cl :=
  { name := "K9: the batching draw"
    place := ⟨p.chain, some p.link, p.piece, .K9⟩
    planOk := p.rows != 0
    rounds := [{ entry := entry p }]
    oracles := [[]]
    before := (List.range p.sent).map fun n => (p.chain, n)
    claims := []
    after := []
    decide := fun t rs _ =>
      match rs with
      | [r] => do
        let s ← X.part t
        let chi ← chiOf r
        let o ← drawnClean p.rows chi s.owed s.used s.L s.F
        pure (X.set t { s with owed := o.owed, L := o.L, F := o.F })
      | _ => .error "K9.one-round" }

/-- Claims made and added where the block stands. No round. piece: the block's number. what: for a
refusal's words. claims: a function of claims, as Link.blocksInOrder hands one to the batching. -/
def adds (X : Lens T) (p : Where) (piece : Nat) (what : String)
    (claims : T → Except String (List Claim × T)) : Block T Cl :=
  { name := "K9: claims added: " ++ what
    place := ⟨p.chain, some p.link, piece, .K9⟩
    planOk := true
    rounds := []
    oracles := []
    before := []
    claims := []
    after := []
    decide := fun t _ _ => do
      let s₀ ← X.part t
      need "K9.draw-has-run" s₀.L.handed
      let x ← claims t
      let s ← X.part x.2
      let F ← addList s.F x.1
      pure (X.set x.2 { s with F := F }) }

/-- **The batching.** claims: the segment's claims, as one function: the other kinds' named runs,
in the order that the segment states. chi is stored; the claims are made; each is added under its
weight. FIXED BEFORE THE DRAW: every oracle message that the chain has sent so far. -/
def batch (X : Lens T) (p : Where) (claims : T → Except String (List Claim × T)) : Block T Claim :=
  { drawAlone X p with
    decide := fun t rs gs => do
      let t₁ ← (drawAlone (Cl := Claim) X p).decide t rs gs
      (adds (Cl := Claim) X p p.piece "the segment's" claims).decide t₁ [] [] }

/-- **The one equation**, added as a row to the segment's group. No round. -/
def oneEquation (X : Lens T) (p : Where) : Block T Cl :=
  { name := "K9: the one equation"
    place := ⟨p.chain, some p.link, p.pieceEq, .K9⟩
    planOk := true
    rounds := []
    oracles := []
    before := []
    claims := []
    after := []
    decide := fun t _ _ => do
      let s ← X.part t
      let o ← door s.owed s.laid s.L s.F s.d
      pure (X.set t { s with owed := o.owed, L := o.L, F := o.F, d := o.d }) }

/-! ## SENDS: not written in this file (Johnson/Desc/ProofFile/Honest/K9/Part.lean) -/

end VerifiableInference.Desc.K9
