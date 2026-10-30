-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/ForKinds.lean: what the honest parts of all kinds share, so that they
count and name things in the same way. Executable definitions, and tests; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

  1  `maskRowRun`, `indexMaskRun`, `foldMaskRun`, `splitMaskRun`, `Addr.words`, `runName`,
     `carriedName`   the names of blocks of coins. A part states each block that it spends or
     carries by name and count (`Part.spends`, `Part.carries`), `lend` (Honest/Frame.lean) compares
     both with the book's entry, and no two entries of a book have the same name
  2  `Cells`, `Weights`, `TableRand`   one form for the witness, for the index and for the stored
     tables' pads and encoding randomness: readers
  3  `roundsInFront`, `heardFrom`, `heardJust`   how a part finds a challenge that is not among the
     last ones
  4  `eOfF`   from an element of the base field to the program's element of the extension field
  5  `quietPart`, `quietSim`, `scalarsPart`, `scalarsSim`   two small parts that many kinds have,
     each with a candidate simulator: rounds that send nothing; a round that sends scalars, each as
     its value plus a mask entry

A block that is spent is named by whose message its coins are (one of four), the address of the part
that is given it, and what it is used for. A block that is carried is one oracle message's share of
its sender's coins: tails, pad and mask rows. It is named by the sender's address, the message's
number in its sending, from 0, and the address of the part that is given it. It is not all of the
sender's coins: one sending can hold messages of two groups (the first segment's sending holds the
index-mask message too), and the book rejects a coin that is given to a part before the part that
spends it.

How a part reads witness and index. Type the part at a small structure W' of its own: the functions
that the kind needs. Put it into a list of parts by `Part.lift`, whose `wit` computes W' from the
prover's input. Of the witness `wit` reads `Cells.cell` alone, of the index `Weights.entry` alone,
of the stored tables' pads and encoding randomness `TableRand` alone. So no kind depends on how the
model's forward pass is written, and what its `wit` names there is what it asks of them.

The two small parts. `quietPart` and `scalarsPart` are general in a part's
three type parameters (they are typed at every V, W and X), so they need no
`Part.lift`.


Limits.
  * Nothing compares a name with the function that computes the book, which has to call the same
    functions.
  * Nothing compares a matrix's name or a cell's range with the format's pages: a cell beyond a
    matrix is whatever the reader returns.
  * `heardFrom` counts in `State.heard`, which in the second chain begins with the first chain's
    challenges and then the shared chain's.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

/-! ## 1 The names of blocks of coins -/

/-- The four messages from whose mask rows later parts take entries. -/
def maskRowRun : String := "the segment's mask row"
def indexMaskRun : String := "the index-mask message"
def foldMaskRun : String := "the fold's fresh mask"
def splitMaskRun : String := "the split's mask message"

/-- An address in words: chain, link ("-" if there is none), piece, part. -/
def Addr.words (a : Addr) : String :=
  s!"{a.place.chain}.{(a.place.link.map toString).getD "-"}.{a.place.piece}.{a.part}"

/-- **The name of a block that is spent**: whose message; the part that is given it; what it is used
for. The uses: "sum" (a masked sumcheck's first block: the lead's entries and the hiding
polynomial's), "ends" (its second: the end values'), "fold" (the coefficients of a fold's hiding
polynomial), "split" (the shared split's one coin), "scalars" (scalars that are sent by themselves
in a round, each under a mask entry). -/
def runName (owner : String) (dest : Addr) (use : String) : String :=
  owner ++ " to " ++ dest.words ++ ": " ++ use

/-- **The name of a block that is carried**: all coins of oracle message number `msg`, from 0, of
the sending that the part at `sender` holds; the part that is given it. -/
def carriedName (sender : Addr) (msg : Nat) (dest : Addr) : String :=
  s!"message {msg} of " ++ sender.words ++ " to " ++ dest.words ++ ": carried"

/-- An address for the tests. -/
def toyTo (part : Nat) : Addr := ⟨⟨1, some 2, 3, .K4⟩, part⟩

#guard runName maskRowRun (toyTo 5) "sum" == "the segment's mask row to 1.2.3.5: sum"
#guard runName indexMaskRun ⟨⟨1, none, 0, .K13⟩, 0⟩ "ends" ==
  "the index-mask message to 1.-.0.0: ends"
-- two parts of a place, two uses, two owners: different names
#guard runName maskRowRun (toyTo 5) "sum" != runName maskRowRun (toyTo 6) "sum"
#guard runName maskRowRun (toyTo 5) "sum" != runName maskRowRun (toyTo 5) "ends"
#guard runName maskRowRun (toyTo 5) "sum" != runName foldMaskRun (toyTo 5) "sum"
-- carried to one part: two senders, two messages of one sender: different names
#guard carriedName (toyTo 0) 1 (toyTo 9) == "message 1 of 1.2.3.0 to 1.2.3.9: carried"
#guard carriedName (toyTo 0) 1 (toyTo 9) != carriedName (toyTo 1) 1 (toyTo 9)
#guard carriedName (toyTo 0) 1 (toyTo 9) != carriedName (toyTo 0) 2 (toyTo 9)

/-! ## 2 One form for the witness and for the index -/

/-- **The witness as all kinds read it**: the cell of a committed matrix, by four arguments. The
segment's number, from 0. The matrix's name as the verifier's own plan has it (the field
`TMat.name`, OnBytes/Model/Frame.lean; set by the plans: at an attention segment "as" with the
part's number, "ah", "ao", "bA", "qa": OnBytes/Model/AttentionPlan.lean); where the format's pages
name a whole matrix that the plan cuts into parts, it is the part's name. The row. The column. -/
structure Cells where
  cell : Nat → String → Nat → Nat → Cb.Gl.F

/-- **The index as all kinds read it**: the entry of the matrix of all committed weights' digits
(docs/format/11-5-weights-in-the-table.md), by row and column. -/
structure Weights where
  entry : Nat → Nat → Cb.Gl.F

/-- **One stored table's pads and encoding randomness, as all kinds read them.** -/
structure TableRand where
  /-- row, then the pad's entry, from 0: three for each out-of-domain answer -/
  pad : Nat → Nat → Cb.Gl.F
  /-- row, then the tail's entry, from 0 -/
  tail : Nat → Nat → Cb.Gl.F

/-! ## 3 A challenge that is not among the last ones -/

/-- How many rounds of a chain come before the sub-protocol at a place: public data, to be put into
a kind's own parameters. `none` if there is none at the place. -/
def roundsInFront {S Cl : Type} : List (Block S Cl) → Place → Option Nat
  | [], _ => none
  | b :: bs, a =>
    if b.place == a then some 0 else (roundsInFront bs a).map (· + b.rounds.length)

/-- The `n` challenges from number `i` on, of all that were heard. In the first and in the shared
chain number `i` is the chain's round number `i`, from 0. If fewer than `n` have been heard from
number `i` on, it returns a shorter list and no error: a move calls `heardJust`. -/
def heardFrom {W X : Type} (t : State W X) (i n : Nat) : List Fmt.Drawn := (t.heard.drop i).take n

/-- **The same, or an error if fewer than `n` have been heard from number `i` on**: for a move,
whose `say` returns an `Except`. A fault of the definition or of where it is placed then shows,
where `heardFrom` would pass on an empty list. A wrong number within what was heard is as silent as
before: so whoever places a part computes such numbers by `roundsInFront`, from the description's
own list, and never writes them by hand. -/
def heardJust {W X : Type} (t : State W X) (i n : Nat) : Except String (List Fmt.Drawn) :=
  if (heardFrom t i n).length == n then .ok (heardFrom t i n)
  else .error "fewer challenges have been heard than the part reads"

#guard heardFrom (⟨(), [⟨[], [1], [], none⟩, ⟨[], [2], [], none⟩, ⟨[], [3], [], none⟩], ()⟩ :
  State Unit Unit) 1 1 == [⟨[], [2], [], none⟩]
-- beyond what was heard: `heardFrom` is short or empty; `heardJust` returns an error
#guard heardFrom (⟨(), [⟨[], [1], [], none⟩], ()⟩ : State Unit Unit) 1 1 == [] &&
  (heardJust (⟨(), [⟨[], [1], [], none⟩], ()⟩ : State Unit Unit) 1 1).toOption.isNone &&
  (heardJust (⟨(), [⟨[], [1], [], none⟩], ()⟩ : State Unit Unit) 0 2).toOption.isNone
#guard (heardJust (⟨(), [⟨[], [1], [], none⟩], ()⟩ : State Unit Unit) 0 1).toOption ==
  some [⟨[], [1], [], none⟩]

/-! ## 4 The two classes of elements -/

/-- An element of the base field, as the library types it, as the program's element of the extension
field: what the lists of `SumJob` hold. (For an element of the extension field:
`OnBytes.E.ofTriple (OnBytes.Slice.ofE x)`; back: `OnBytes.Slice.toE x.triple`.) -/
def eOfF (x : Cb.Gl.F) : OnBytes.E := OnBytes.E.ofTriple (OnBytes.Slice.ofF x, 0, 0)

#guard eOfF (OnBytes.Slice.toF 7) == OnBytes.E.ofTriple (7, 0, 0)

/-! ## 5 Two small parts -/

section
variable {V W X Pb : Type}

/-- **`n` rounds in which the prover sends nothing.** No coin, no stop. It is typed at every V, W
and X, so it needs no `Part.lift`. A kind whose quiet round has a first stop can supply it:
`{ quietPart with bad := … }`. Such a part does not go with `quietSim`: where the first stop
stops the part, the part shows `none` and `quietSim` does not, so `Good.exact` (Honest/Side.lean)
fails there. It needs another candidate simulator, or a condition `On` that excludes these
challenges. -/
def quietPart (n : Nat := 1) : Part V W X :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := List.replicate n ⟨fun _ _ _ => .ok ⟨[], []⟩, fun t => t.own⟩ }

/-- A candidate simulator for it: it takes no coin and reads none of its arguments. It never outputs
`none`. Nothing ties its `n` to the part's; both default to 1. -/
def quietSim (a : Addr) (n : Nat := 1) : Sim Pb :=
  { addr := a, takes := ⟨0, 0⟩, tell := fun _ _ _ _ _ => some (List.replicate n ⟨[], []⟩) }

/-- **One round that sends `n` scalars, each as its value plus a mask entry.** `name`: the block
that it spends: `n` coins of the extension field, in the order in which the scalars are sent.
`vals`: the values, from the input and from what comes before the part (`Front`, Honest/Sum.lean); a
list that is too short or too long is padded with 0 or cut. No coin of its own, no stop. -/
def scalarsPart (name : String) (n : Nat) (vals : W → Front X → List OnBytes.E) : Part V W X :=
  { takes := ⟨0, 0⟩, spends := [(name, ⟨0, n⟩)], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c s t =>
        .ok (sayE (addL (padTo n (vals t.input ⟨t.heard, t.own, s⟩)) (coinsE c.2.1.1))),
      fun t => t.own⟩] }

/-- A candidate simulator for it: `n` coins of its own, each output as it is; it reads none of its
other arguments. -/
def scalarsSim (a : Addr) (n : Nat) : Sim Pb :=
  { addr := a, takes := ⟨0, n⟩
    tell := fun _ _ _ _ c => some [⟨(coinsE c).map fun x => .e x.triple, []⟩] }

end

end ProofFile.Honest
