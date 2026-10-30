-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestRecordToyCompiledFalseLenient.lean: the compiler's verifier of the link behind the
lenient reader: the seven stored false entries in which every hash is right. Tests alone.

The run function `run`, its outcomes and the controls are those of
OnBytes/Tie/TestRecordToyCompiled.lean; its head says how a file is judged. The files are those of
Fmt/MustBeRefused/RecordToy.lean whose refusal by Entry.check has a name that begins "decision-"
(OnBytes/Entry/TestRecordToy.lean): made by the honest prover on a copy that differs from the first
table, or by a prover that cheats in one named way. The same files behind the strict reader:
TestRecordToyCompiledFalse.lean.

What is checked when the file compiles (#guard). For each of the seven, two tests.
   The file is refused by the compiled verifier, not by the reader.
   Control: with the decision replaced by "always yes" it is accepted. So for the compiled verifier
   every hash, proof of work, point of form and Merkle path of the file is right, and the decision
   alone refuses. The decision is the one that Entry.check asks, here on the view that the protocol
   makes of the typed string.
   Behind this reader the compiled verifier itself tests the work, hashes the leaves, walks the
   paths and compares the roots.

The control is not a verifier: it accepts these seven false entries.

What is not claimed. What part 3 of the head of OnBytes/Tie/TestRecordToyCompiled.lean lists as not
claimed holds here too. Above all: what runs is `verifyOneProtocol` of Compile/Batch at a protocol that takes
no instance, one protocol for each pair of records, and not the verifier of the link inside
`innerCompiledVerifier`; the tests are evaluations at made-up toy data and leave no theorem on a run. Nothing on
soundness, completeness or hiding.
-/
import OnBytes.Tie.TestRecordToyCompiled

open OnBytes.Tie.RecordToyCompiled Run.PQ Fmt.MustBeRefused.RecordToy

#guard voice .lenient .nothing linkOneCell == some .verifier
#guard voice .lenient .decision linkOneCell == some .accepted

#guard voice .lenient .nothing baseWrongWord == some .verifier
#guard voice .lenient .decision baseWrongWord == some .accepted

#guard voice .lenient .nothing foldeqOtherRow == some .verifier
#guard voice .lenient .decision foldeqOtherRow == some .accepted

#guard voice .lenient .nothing linkFarTable == some .verifier
#guard voice .lenient .decision linkFarTable == some .accepted

#guard voice .lenient .nothing linkOtherCopyRow == some .verifier
#guard voice .lenient .decision linkOtherCopyRow == some .accepted

#guard voice .lenient .nothing linkOtherCopyTail == some .verifier
#guard voice .lenient .decision linkOtherCopyTail == some .accepted

#guard voice .lenient .nothing linkShortCut == some .verifier
#guard voice .lenient .decision linkShortCut == some .accepted
