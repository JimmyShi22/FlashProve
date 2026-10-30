-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Parts.lean: the honest side of the kind "the batch's shared
rounds" (K14), in the form of Honest/Frame.lean: the kind's own four sub-protocols that have a
round. The kind's own text says: "SENDS is not written in this file" (Johnson/Desc/K14/Text.lean).
This is that text for these four. Definitions with code; no theorem.

What is sent. "LIN point", "LOC" and "LIN zeta" have one round each, in which the prover sends
nothing. "SPLIT" has one round, where the shape splits: one element in the clear, the scalar mu:
omega_col at the point z_fd, over the matrix's rows, plus one entry of the split's mask message
(muAtE, Johnson/Desc/K14/Honest/Coded.lean). No part here takes a coin of its own or has a stop. The
part at "SPLIT" spends one coin of the part that sends the split's mask message.

THE PARTS ARE CALLS OF THE TWO SMALL PARTS OF Honest/ForKinds.lean: quietPart, and scalarsPart at
one scalar: "its value plus a mask entry". The simulator beside "SPLIT" is that file's scalarsSim at
one scalar. The index committer's coins are read through that file's TableRand.

  Ask          the small input over which the parts are stated: the committed table's rows before
               encoding
  entriesOf    these rows at the places that hold the matrix, of the matrix of all committed
               weights' digits; 0 at all other places
  rowsOf       for the two sendings (Honest/K14/Sendings.lean): the rows whole, with each row's pads
               and random tail as TableRand hands the index committer's coins. No part of this file
               calls it
  Data         the public data: the shape; the numbers, among the chain's rounds, of the two rounds
               whose challenges the scalar reads
  dataOf       the public data MADE: the two numbers by roundsInFront (Honest/ForKinds.lean), of the
               shared chain's own list of sub-protocols: whoever lays the halves is to call it, and
               to write no number
  elems        the elements that challenges hold
  place, splitRun, splitValue, splitPart   the part at "SPLIT": splitValue is the scalar without the
               mask entry
  splitSim     the form of a simulator beside the part at "SPLIT": one coin of its own, sent as it
               is; of what it is handed it reads nothing but that coin
  proverSidesOfSharedRounds       the halves, lifted to the shared chain's type parameters: four where the shape
               splits, else three

What the four parts read. Of the index: Weights.entry at every row below the matrix's rows and every
column below 2 ^ kCol. Of the challenges: psi_sh and z_fd. No coin of the index committer's, no
witness, no instance, no key.

Limits. THE PART AT "SPLIT" IS TOTAL: where fewer challenges have been heard than the two numbers
name, or the numbers are another round's, shorter or other lists go into the scalar's value, without
a word; the mask entry is an addend there too. The guard is dataOf, where the halves are laid. The
two sendings of the shared rounds (places 2 and 5) are not here. What stands in a row between the
matrix's entries and the pads is laid as 0 in rowsOf, and held against no page. rowsOf IS THE
COMMITTED ROWS' TEXT ONLY WHERE THE LIBRARY's TEST ON THE SHAPE ACCEPTS (LinShape.ok,
OnBytes/Iop/Lin.lean: the matrix's places lie in front of the pads): elsewhere its first clause lays
an entry of the matrix where a pad is due, without a word. NO DEFINITION OF THIS FILE ASKS THAT
TEST. Nothing holds entriesOf or rowsOf against the program that makes a committed table. The
simulator is data: nothing is said of what it is good for. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.K14.Honest.Coded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE)
open OnBytes.Params (LinShape)
open OnBytes.Slice (toE)
open VerifiableInference.Desc (Place Block)
open Desc.K14.Law (sumE eqE)

variable {W₀ Rc Ky X Pb S Cl : Type}

/-- **The small input**: row r of the committed table before encoding, at the place k, laid out as
the folded row is: the message (pads among it) below ell, the random tail from tailFirst on. The
halves of this file lay entriesOf here, which has the matrix's places alone: the parts of this file
read no other. -/
structure Ask where
  rows : Nat → Nat → E

/-- **The rows at the places that hold the matrix.** Entry (y, t + 2 ^ kLo r) of the matrix stands
at the place t + 2 ^ kLo y of row r (OnBytes/Iop/Lin.lean's head; it undoes matOf,
Johnson/Desc/K14/Law/OmegaTable.lean). -/
def entriesOf (S : LinShape) (w : Weights) (r k : Nat) : E :=
  if k < S.matrixRows * 2 ^ S.kLo then
    eOfF (w.entry (k / 2 ^ S.kLo) (k % 2 ^ S.kLo + 2 ^ S.kLo * r))
  else zeroE

/-- **The rows, whole.** -/
def rowsOf (S : LinShape) (w : Weights) (c : TableRand) (r k : Nat) : E :=
  if k < S.matrixRows * 2 ^ S.kLo then entriesOf S w r k
  else if S.fold.index.plain ≤ k ∧ k < S.fold.index.code.ell then
    eOfF (c.pad r (k - S.fold.index.plain))
  else if S.fold.tailFirst ≤ k ∧ k < S.fold.entries then eOfF (c.tail r (k - S.fold.tailFirst))
  else zeroE

/-- **The public data.** -/
structure Data where
  S : LinShape
  /-- the number, from 0, among the shared chain's rounds, of "LIN point" -/
  atPoint : Nat
  /-- the like of "LIN zeta" -/
  atZeta : Nat

/-- The elements that challenges hold, in order. -/
def elems (ds : List Fmt.Drawn) : List E := ds.flatMap fun d => d.elems.map E.ofTriple

/-- The kind's place at a piece of the shared chain. -/
def place (piece : Nat) : Place := ⟨2, none, piece, .K14⟩

/-- **The public data, made**: bs: the shared chain's own list of sub-protocols, whole, from its
first. Nothing where one of the two places is not in the list. -/
def dataOf (shape : LinShape) (bs : List (Block S Cl)) : Option Data :=
  (roundsInFront bs (place 1)).bind fun a =>
    (roundsInFront bs (place 7)).map fun z => { S := shape, atPoint := a, atZeta := z }

/-- The name of the one coin that "SPLIT" spends. -/
def splitRun : String := runName splitMaskRun ⟨place 8, 0⟩ "split"

/-- **The scalar without the mask entry**: omega_col at the point z_fd, over the matrix's rows. h:
the challenges heard. With the entry kappa added it is muAtE … kappa, by that function's own
text. -/
def splitValue (P : Data) (a : Ask) (h : List Fmt.Drawn) : E :=
  sumE P.S.matrixRows fun j =>
    OnBytes.mulE (eqE (elems (heardFrom (⟨a, h, ()⟩ : State Ask Unit) P.atZeta 1)) j)
      (Desc.K14.Honest.omegaAtE P.S (elems (heardFrom (⟨a, h, ()⟩ : State Ask Unit) P.atPoint 1))
        a.rows j)

/-- **The part at "SPLIT"**: one round, one element in the clear: scalarsPart
(Honest/ForKinds.lean) at one scalar. -/
def splitPart (P : Data) : Part Empty Ask Unit :=
  scalarsPart splitRun 1 fun a fr => [splitValue P a fr.heard]

/-- The form of a simulator beside it: scalarsSim (Honest/ForKinds.lean) at one scalar. -/
def splitSim : Sim Pb := scalarsSim ⟨place 8, 0⟩ 1

/-- **The halves**, lifted. weights: it reads the index off the input. Three where the shape does
not split: there "SPLIT" has no round. -/
def proverSidesOfSharedRounds (P : Data) (weights : W₀ → Weights) : List (Placed Empty (Common W₀ Rc Ky) X) :=
  let lifted (p : Part Empty Ask Unit) : Part Empty (Common W₀ Rc Ky) X :=
    p.lift (fun v => v) (fun c => ⟨entriesOf P.S (weights c.w₀)⟩) (fun _ => ()) fun x _ => x
  [⟨place 1, [lifted quietPart]⟩, ⟨place 4, [lifted quietPart]⟩, ⟨place 7, [lifted quietPart]⟩] ++
    if P.S.sharedSplitNeeded then [⟨place 8, [lifted (splitPart P)]⟩] else []

end ProofFile.Honest.K14
