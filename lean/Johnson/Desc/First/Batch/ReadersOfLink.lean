-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/ReadersOfLink.lean: THE READERS OF A LINK, AS ONE TERM, ON THE GATHERER's
ROAD: the filling of the
letter `Readers` (Johnson/Desc/First/Batch/FormsIn.lean) at a link of a chain
(Johnson/Desc/Block.lean: `Link`): THE RUNS ARE
WHAT THE LINK's HEARING BLOCKS STATE. Definitions with code. No Mathlib.
  `statesOfLink l b`: the runs of claims that block number b of `l.hear` states.
  `readersOfLink H l`: for a pair (block, name) of the link's order: THE READER IS THE RUN ITSELF
    (`readerOf`, Johnson/Desc/First/Batch/ReaderOf.lean), BUT AT TWO HOLES, WHICH ARE LETTERS
    (`LinkHoles`):
      `small`: the smallness test's equations: that run refuses at every border in front of the
        batching's place (by a run over another text of the chain), and its claims are more than
        forms: their reader is a term of its own over what the smallness test has heard.
      `silent`: where the run itself gives nothing (by the same run: five runs of the head, at the
      one
        border behind the head's own block): the reader there is another term.
  `LinkHoles.none`: both holes empty.
No table of a seat's stands between: the very functions that `claimsInBy` calls at the batching are
the readers.
Limits: definitions. `silent` speaks only where the run is silent, and at `small` the run is never
asked: so the two never speak together. AT `LinkHoles.none` THE SMALLNESS TEST's ITEM HAS NO READER:
its sentence is then false of every witness: aloud, not idle. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.ReaderOf
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- **The letters of the term.** -/
structure LinkHoles where
  /-- THE FIRST HOLE: the reader of the smallness test's single equations -/
  small : S → Option Read
  /-- THE SECOND HOLE: the reader of a run (block, name) where the run itself is silent -/
  silent : Nat → String → S → Option Read

/-- Both holes empty. -/
def LinkHoles.none : LinkHoles := ⟨fun _ => Option.none, fun _ _ _ => Option.none⟩

/-- What block number b of the link's hearing blocks states. -/
def statesOfLink (l : Link S Claim) (b : Nat) : List (RunOf S) :=
  ((l.hear[b]?).map fun x => x.claims).getD []

/-- **THE READERS OF A LINK.** -/
def readersOfLink (H : LinkHoles) (l : Link S Claim) : Readers :=
  ⟨fun b name s =>
    if name == "K8.equations" then H.small s
    else
      match readerOf (statesOfLink l) b name s with
      | some R => some R
      | Option.none => H.silent b name s⟩

end VerifiableInference.Desc.K9
