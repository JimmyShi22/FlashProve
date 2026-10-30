-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/PubOf.lean: what the proof file's and the key file's protocols take beside the size,
from what the verifier program itself computes of the three public files.

Definitions, and one equation. p is what `Model.Verify.planned` (OnBytes/Model/Verify.lean) returns
at the three public files. An instance is an `Instance' P` (Johnson/Flat/Instance.lean). The block
of the links at an instance, the reply, the instance at which the dry runs are made and the instance
with the reply 0: Johnson/Flat/LinksAt.lean.

Main names:
  `replyPlace rounds`: the place of the round REPLY in a list of rounds' names, from 0.
  `keyChains p`, `proofChains p`, `blankTable p`, `zeroKey p`, `slots p`: the two files' chains as
    read back, a table's name of no content, a table's key of no content, the number of a binding
    tree's leaves.
  `pubOf p P hV`, `pubLateOf p P hV`: two values of `Pub (Instance' P)` (OnBytes/Flat/BigOf.lean),
    for the two typings of the reply. In both the first query binds the instance with the reply's
    word 0 (`early` := `withoutReply`), as the programs' request item has it. `pubOf`: `late` :=
    none: the reply is a plain message of the prover in the round REPLY. `pubLateOf`: `late` :=
    `replyRound` + 1: the query of that round holds the whole instance. THE FIRST, `pubOf`, IS THE
    ONE TO LAY; why, and the one condition to keep in sight: the section "The two typings of the
    reply".
  `pubOf_block`: the first chain's block at an instance, the same in both.
Limits: nothing on a protocol. That `bigOf` returns a value at `pubOf` is not shown and not tested
here. That no round before REPLY is left out of a file's joined rounds is read, not shown. THE
ROUNDS ARE TAKEN FROM THE DRY RUN AT `firstInstance` ALONE, and serve as the description's shape at
every instance; the program takes them from the dry run at the call's own block: that the two lists
are one at every request is shown nowhere. THAT P IS THE SIZES OF p's PARAMETER FILE IS NOT ASKED
HERE, AND IS LEFT TO THE PLACE OF USE (P := `sizesAt` of that file): at another P.T the first step
refuses the words; P.V is met in the second step alone, token by token against p's; the other eight
sizes are read by no step.

-/
import Johnson.Flat.LinksAt
import OnBytes.Flat.BigOf
import OnBytes.Params.KeyLayout

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model

/-- The place of the round REPLY in a list of rounds' names, from 0. -/
def replyPlace (names : List String) : Option Nat :=
  let i := names.findIdx (· == "REPLY")
  if i < names.length then some i else none

/-- The key file's three chains as the program has read them back. -/
def keyChains (p : Verify.Planned) : Params.KeyChains := p.chains.key

/-- The proof file's three chains as the program has read them back. -/
def proofChains (p : Verify.Planned) : Params.ProofChains := p.chains.proof

/-- A table's name of the tables' shape and of no content. -/
def blankTable (p : Verify.Planned) : Params.TableName :=
  Params.blankTableOf p.chains.proof.first.lin.fold.index

/-- A table's key of no content, under the statement's item 0: a record of zeros, seeds with points
of zeros and the factor one (`Params.sizeKey`, OnBytes/Params/EntryLayout.lean). -/
def zeroKey (p : Verify.Planned) : TableKey := Params.sizeKey p.chains.proof.first.lin.fold.index 0

/-- The leaves of a proof file's binding tree. -/
def slots (p : Verify.Planned) : Nat := 2 ^ p.chains.proof.first.binding.logLeaves

/-! ## The two typings of the reply

What the bytes are: in the request item, which a proof's first query binds, the next token's word is
0 (docs/format/FORMAT.md, R15.7; `Proof.requestItem`, OnBytes/Proof/RequestItem.lean); the prover
sends the token in the round REPLY, and the first chain's block compares what it has received with
the caller's reply (`Proof.firstBlock`, OnBytes/Proof/File.lean). So in both values below `early` is
`withoutReply`. They part in `late`; the sense of the two fields: `BatchInteractiveOracleProof.SndBL`
(Iop/Batch.lean).

THE FIRST TYPING, `pubOf`, IS THE ONE TO LAY: in it every typed query holds what the programs'
string holds: by reading, and through the coding that writes `early x` into the request item, which
is elsewhere and is no finding of this file. The second would want a late query that holds the reply
alone, where the library's holds the whole instance.

ONE CONDITION TO KEEP IN SIGHT under the first typing: the reply is named before the head commits
and before the head's challenges are drawn; no check whose soundness is counted lets the prover
choose the reply after a challenge it answers. In the verifier's text: the checks before the round
REPLY are given the request's tokens or nothing of the request; every check of a round that reads
the reply's token reads the message of REPLY, and every draw that it uses is later; the relation's y
is that message by the decision's comparison, no free late part. TWO TESTS INSIDE `linksOf p x` READ
THE INSTANCE's OWN y BEFORE ANY ROUND: the reader refuses unless y = 0 where e is before the
window's end, and `Head.coveredOf` refuses unless y is an entry of the vocabulary
(OnBytes/Model/HeadLayout.lean); `linksOf` turns either refusal into a block that fails. They are
tests on the instance alone, they can only refuse, and no soundness is counted on them. All this is
by reading of the pages and of the verifier's text (R15.7, `Proof.firstBlock`, `Verify.linksOf`, the
order of the links' rounds), and no law. THAT A DESCRIPTION MADE OF THESE VALUES MEETS THE CONDITION
IS NOT SHOWN HERE: the head's check reads a window whose last entry is the token that the prover
names (`winOf`, OnBytes/Model/HeadHeard.lean), and no law here ties that token to the message that
the comparison reads. `linksOf p x` and `linksOf p (withoutReply hV x)` are not one term: the
covered positions hold the caller's reply in one entry. That the two blocks are one holds AT AN
INSTANCE THAT THE READER TAKES, AND WHERE P.T AND P.V ARE p's; it is a law on `Head.coveredOf` and
the head's routine, and is not here. Elsewhere it is false: at e before the window's end and y not 0
the one block fails and the other is the program's. The words of the two files at `withoutReply hV
x`: Johnson/Flat/PubWiped.lean [not in this library].

A value with `early` := id would say that the first query binds the reply too: that is not what the
programs hash, and no such value is here. -/

/-- **What is public about the two big files**, from what the program computes of the three public
files. FIRST TYPING, THE ONE TO LAY: `late` := none: no later query holds the instance; the reply is
a plain message of the prover in the round REPLY, and the decision compares it with the instance's.
The dry runs are made at `firstInstance` and at `zeroKey`. The most roots in one message:
two. -/
def pubOf (p : Verify.Planned) (P : Params) (hV : 0 < P.V) : Pub (Instance' P) where
  k := keyChains p
  c := proofChains p
  table := blankTable p
  links := linksOf p
  reply := replyOf
  x₀ := firstInstance P hV
  key₀ := zeroKey p
  maxRt := 2
  N := slots p
  early := withoutReply hV
  late := none

/-- The place of the round REPLY among the rounds that the dry run of the proof file's first block
notes at `firstInstance`, from 0. -/
def replyRound (p : Verify.Planned) (P : Params) (hV : 0 < P.V) : Option Nat :=
  (((pubOf p P hV).block (firstInstance P hV)).dryRun (Proof.firstStart p.chains.proof.first)).bind
    fun d => replyPlace (d.1.map (·.1.entry.name))

/-- The same. SECOND TYPING, kept for comparison, NOT THE ONE TO LAY: `late` := the place of the
round REPLY in the file's joined rounds, which begin with one silent round: the query of that round
holds the whole instance. The programs' string at that round holds the reply and nothing else of the
instance. -/
def pubLateOf (p : Verify.Planned) (P : Params) (hV : 0 < P.V) : Pub (Instance' P) :=
  { pubOf p P hV with late := (replyRound p P hV).map (· + 1) }

/-- The first chain's block at an instance is the program's `Proof.firstBlock` at `linksOf` and the
reply. It is the same in both typings. -/
theorem pubOf_block (p : Verify.Planned) (P : Params) (hV : 0 < P.V) (x : Instance' P) :
    (pubOf p P hV).block x = Proof.firstBlock p.chains.proof.first (linksOf p x) (replyOf x) := rfl

end OnBytes.Flat
