-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/TestRecordToyStrictFalseB.lean: the second compiler's strict verifier of the link on
stored false entry files: linkOtherCopyRow, linkOtherCopyTail, linkShortCut
(Fmt/MustBeRefused/RecordToy.lean, whose head says where each comes from: all three were made in
house by a prover that cheats in one named way).
What is expected, and why. OnBytes/Entry/TestRecordToy.lean holds that Entry.check refuses each of
these files at a check of the decision, which it reaches only where Entry.read has read the file
whole: form, work and every opening. The strict converter is Entry.read: so it reads the file; the
same hashes, asked through the typed oracles, make the seeds agree, the chain return and thirteen
lines say yes; the file must be refused, so the last line, "after 5", the protocol's whole
acceptance, says no. Control: with the decision taken out the run ends in "yes": so the three other
conjuncts of that line (work, the number of draws, the stored symbols at them) pass, every hash,
point of form and path is right for the compiled verifier, and the decision alone refuses.
What that adds, and what not. The decision is the port's own, by which Entry.check refuses the same
files (OnBytes/Entry/TestRecordToy.lean): on the decision itself these guards hold Lean against the
same Lean. What they add: the compiled verifier hands that decision the view at which it says no,
and finds all else right.
What is run, what the stages' names and the two switches mean, and what is not claimed:
Johnson/RunOne/TestRecordToyStrict.lean's head.
-/
import Johnson.RunOne.TestRecordToyStrict

open Johnson.RunOne.RecordToyStrict Fmt.MustBeRefused.RecordToy

#guard voice false false linkOtherCopyRow == some "after 5"
#guard voice false true linkOtherCopyRow == some "yes"
#guard voice false false linkOtherCopyTail == some "after 5"
#guard voice false true linkOtherCopyTail == some "yes"
#guard voice false false linkShortCut == some "after 5"
#guard voice false true linkShortCut == some "yes"
