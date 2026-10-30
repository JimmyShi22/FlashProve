-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AsksDoor.lean: THE LOOKUPS' THREE TESTS ON PUBLIC DATA IN THE FORM OF THE
PROOF FILE's ENTRY TESTS: each a function of the public plan Z alone (ProofFile.Pub → Bool),
bare. Definitions alone; no theorem. NO SOUNDNESS IS CLAIMED. Nothing is evaluated in this file.

How. The list of entry tests computes the public plan of the three public files once, at its head,
and asks each row at it. Each function here takes the public parameters Z.p.X, and the data beside
them, off that plan, and asks a row of Johnson/Desc/First/Look/K3Asks.lean or K3AsksHead.lean.

OBJECT: no sub-protocol's text.
USER: the proof file's entry tests 11 to 13 (LPFD.lawsAsk, Johnson/Desc/Laid/ProofAsks.lean), each
asked at every size.
LETTERS: Z : ProofFile.Pub.
Compiled with the whole library.


Main names:
  `sentOf Z`: the data beside the public parameters: the first chain's codes, the request's shape
    and the rows' layout, and link by link the table of arrays of the built links.
  `digEntry`, `readsEntry`, `headEntry`: THE THREE: digRow, readsRow at Z.p.X and sentOf Z; headRow
    at Z.p.X.

THE WORDS UNDER WHICH EACH REJECTS, AND THE LAW THAT NEEDS IT:
  digEntry: "the public files do not lay the digits of an approximate range proof where its lookup
    reads them": DigOK (Johnson/Desc/First/Look/K3Caller.lean), the premise on public data of the
    laws on the lookup on a link's digits: by asks_dig (Johnson/Desc/First/Look/K3AsksLaw.lean).
  readsEntry: "the public files do not lay an attention step's cells where its lookup reads them":
    three of the four fields of AttReadsOK (K3CallerAtt.lean): by asks_reads. NO THEOREM THAT IS
    CALLED TAKES AttReadsOK AS A PREMISE: attCells_eq (K3CallerAtt.lean) and symsOK_of
    (Johnson/Desc/First/Att/K05AddrTieOf.lean) take it, and no file calls either.
  headEntry: "the public files do not give a call of the output head's lookup room for its keys":
    HeadOK (K3CallerHead.lean), the premise on public data of the law on the lookup on the head's
    calls: by asks_head (Johnson/Desc/First/Look/K3AsksHeadLaw.lean).

Limits. None of the three reads the proof.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Asks
import Johnson.Desc.First.Look.K3AsksHead
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Asks

/-- **The data beside the public parameters.** -/
def sentOf (Z : ProofFile.Pub) : Sent :=
  ⟨Z.first.codes, Z.first.shape, Z.first.layout, Z.p.built.links.map (·.arrayOf)⟩

/-- **THE TEST ON THE DIGITS.** -/
def digEntry (Z : ProofFile.Pub) : Bool := digRow Z.p.X (sentOf Z)

/-- **THE TEST ON THE GUARDS OF ATTENTION's CALLERS' READING.** -/
def readsEntry (Z : ProofFile.Pub) : Bool := readsRow Z.p.X (sentOf Z)

/-- **THE TEST ON THE OUTPUT HEAD's CALLS.** -/
def headEntry (Z : ProofFile.Pub) : Bool := headRow Z.p.X

end VerifiableInference.Desc.K3Asks
