-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/Hear.lean: THE SMALLNESS TEST, ITS FIRST HALF: THE DRAW OF THE MATRIX, as a
  kind of block (Johnson/Desc/Block.lean). One place in every link of the first chain, between the
  commitment to the reads and the commitment to the digits. DEFINITIONS, WITH CODE. NO THEOREM. NO
  SOUNDNESS IS CLAIMED.

ROUNDS. One round, "RNG". The prover sends nothing. Drawn: (the sum of all matrices' columns) x tau
  entries, each -1, 0 or 1, as ONE sequence: matrix by matrix in the list's order, column by column,
  the combination's number fastest.
READS. Nothing: no stored table, no tree is opened.
DECIDES. No byte belongs to this stretch, so no byte can fail a test here. What must hold BEFORE the
  draw:
  (a) the list of parts of the vector of reads, with every weight, is closed;
  (b) the round closed last has left no count of batched rows unasked;
  (c) the matrix has not been drawn in this link before;
  (d) the record expects as many matrices as the place's list has;
  (e) the record's own matrices are these: as many, each with the place's numbers of rows and of
      columns;
  (f) the record's number of combinations is the place's;
  (t) the closed list of parts has the place's shapes: as many tables, in this order, each on the
      place's matrix, with the place's number of rows to an entry, from the place's first entry on.
  WHY (e) AND (f): the round and the first columns below are made of THE PLACE's numbers; every
  later step of the test reads THE RECORD's: were the two to part, entries would be read that were
  never drawn.
  WHY (t): the list of parts is made and closed by the link's own kind, out of what it has heard;
  its weights hang on drawn points, its shapes on public numbers alone. What the test's error is
  reckoned over (how many tables, on which matrix, how long) is fixed before any proof is seen: so
  the shapes are numbers of the place, and the closed list is held against them here, once.
  Then the drawn sequence is laid into the record as it stands, with each matrix's first column.
  NOT ASKED HERE, AND WHY: that the round is the plan's next and draws exactly columns x tau
  entries, no element, no position, and counts no row: the round below IS the declared round: the
  fold holds it against the made plan's stretch (FileDescription.planOk) and the view's round against it
  (Block.step, roundsFit).
FIXED BEFORE THE DRAW. Every array which the matrix multiplies (each matrix of the list, the link's
  own or kept from an earlier link, and the vector of reads) must lie in an oracle message that was
  sent in this link, and whose sample was answered, in front of this round: the error 2 ^ -tau rests
  on it. That is a test ON THE PLAN ALONE: the block names these messages in `before`, and the fold
  asks the order (FileDescription.beforeOk). A link sends them in two prover's messages: its first (the own
  matrices; what was kept, sent anew at the switch) and the one with the reads. THAT IS COARSER
  THAN THE TEST OF THE PROGRAM `verify-on-bytes`, which looks each array up in the layout and asks
  that ITS message is past and sampled: nothing here asks that the arrays lie in the messages that
  are named. The finer test still stands in the quiet step in front of this place (behind the
  sending of the reads), with «one shape a matrix» and «one array a matrix»: THE MESSAGES' TENANTS
  ARE NOT NAMED HERE.
  THE BLOCK DRAWS NOTHING ITSELF: it takes the round's entries as the view has them: that they come
  from the hash is the reader's that makes the view; that each is -1, 0 or 1 is asked by the frame
  (Block.step, roundsFit).
TWO REFUSALS THAT NO RUN OF THE FOLD REACHES, AND WHY THEY STAND. "another number of rounds than
  one": Block.step calls decide behind roundsFit alone, which is false where the view's rounds and
  the declared ones (one) differ in number. The seat's own refusal in `lay`: the seat at the first
  chain's record refuses there where no link is open, and there (a) has refused before. Both close a
  match; each speaks in a control row that hands decide no round, or leaves the tests in front out.
CLAIMS. None here: the test's equations are its second half, behind the batching draw: another file.
THE TESTS ON THE PLAN ALONE. A matrix is there · a column is there · a combination is there · a
  message is named for the matrices and one for the reads · as many numbers of rows as of columns ·
  every family of tables has a matrix, and a row to an entry.
SENDS. Not written in this file (Johnson/Desc/ProofFile/Honest/K8/Part.lean).


-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

/-- The numbers of a place. -/
structure Par where
  /-- the link's number in the first chain, from 0 -/
  link : Nat
  /-- the place's number inside the link, from 1 -/
  piece : Nat
  /-- each matrix's number of columns, in the list's order (an earlier link's matrices among
  them) -/
  ks : List Nat
  /-- each matrix's number of rows, in the same order -/
  ms : List Nat
  /-- the number of random combinations -/
  tau : Nat
  /-- the families of tables in the vector of reads, in its order: the number of the family's first
  matrix · of how many matrices in a row it has a table · over how many rows one entry sums -/
  asks : List (Nat × Nat × Nat)
  /-- the oracle messages of the link's first prover's message, which hold the matrices: their
  numbers in the first chain's order of sending, from 0 -/
  matsIn : List Nat
  /-- the like for the prover's message with the vector of reads -/
  readsIn : List Nat

/-- What the kind asks of the carried record, and what it lays into it. -/
structure Seat (S : Type) where
  /-- (a) -/
  closed : S → Bool
  /-- (b) -/
  nothingOwed : S → Bool
  /-- (c) -/
  drawn : S → Bool
  /-- (d) -/
  matrices : S → Nat
  /-- (e): the columns of each of the record's matrices -/
  ks : S → List Nat
  /-- (e): their rows -/
  ms : S → List Nat
  /-- (f) -/
  tau : S → Nat
  /-- (t): of each table of the closed list: its matrix · the rows to an entry · its first entry -/
  tabs : S → List (Nat × Nat × Nat)
  /-- the matrix, as one sequence; each matrix's first column, and the number of all columns
  behind them -/
  lay : S → Array Int → Array Nat → Except String S

/-- All matrices' columns together. -/
def columns (p : Par) : Nat := p.ks.foldl (· + ·) 0

/-- Each matrix's first column; at the end the number of all columns. -/
def firstColumns (p : Par) : Array Nat :=
  p.ks.foldl (fun a k => a.push (a.getD (a.size - 1) 0 + k)) #[0]

/-- One family's tables, laid from entry `e` on: of each its matrix, the rows to an entry and its
first entry; and the first entry behind them. A table has one entry for each column and each run of
`a.2.2` rows. -/
def layFamily (p : Par) (a : Nat × Nat × Nat) (e : Nat) : List (Nat × Nat × Nat) × Nat :=
  (List.range a.2.1).foldl
    (fun x q => (x.1 ++ [(a.1 + q, a.2.2, x.2)],
      x.2 + p.ks.getD (a.1 + q) 0 * (p.ms.getD (a.1 + q) 0 / a.2.2)))
    ([], e)

/-- (t): the shapes of all tables, family by family, from entry 0 on. -/
def tabs (p : Par) : List (Nat × Nat × Nat) :=
  (p.asks.foldl (fun x a => let y := layFamily p a x.2; (x.1 ++ y.1, y.2)) ([], 0)).1

/-- ROUNDS. -/
def round (p : Par) : Fmt.DeclaredRound := { entry := { name := "RNG", trits := columns p * p.tau } }

/-- **The kind.** -/
def approximateRangeProofDrawKind {S Cl : Type} (seat : Seat S) : Kind Par S Cl := fun p =>
  { name := "the smallness test: the draw of the matrix"
    place := ⟨1, some p.link, p.piece, .K8⟩
    planOk :=
      !p.ks.isEmpty && columns p != 0 && p.tau != 0 && !p.matsIn.isEmpty && !p.readsIn.isEmpty &&
        p.ms.length == p.ks.length && p.asks.all fun a => a.2.1 != 0 && a.2.2 != 0
    rounds := [round p]
    oracles := [[]]
    before := (p.matsIn ++ p.readsIn).map fun n => (1, n)
    decide := fun s rs _ =>
      match rs with
      | [r] =>
        if !seat.closed s then .error "the smallness test: the list of parts is open"
        else if !seat.nothingOwed s then .error "the smallness test: a count of rows is owed"
        else if seat.drawn s then .error "the smallness test: the matrix is drawn already"
        else if seat.matrices s != p.ks.length then
          .error "the smallness test: the record expects another number of matrices than \
            the place's list has"
        else if seat.ks s != p.ks then
          .error "the smallness test: the record's matrices have other numbers of columns than \
            the place's list"
        else if seat.ms s != p.ms then
          .error "the smallness test: the record's matrices have other numbers of rows than \
            the place's list"
        else if seat.tau s != p.tau then
          .error "the smallness test: the record has another number of combinations than the place"
        else if seat.tabs s != tabs p then
          .error "the smallness test: the closed list of parts has other shapes than the place's"
        else seat.lay s r.drawn.trits.toArray (firstColumns p)
      | _ => .error "the smallness test: the block was handed another number of rounds than one"
    claims := []
    after := [] }

end VerifiableInference.Desc.First.K8
