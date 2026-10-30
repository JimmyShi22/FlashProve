# Credits: third-party sources of the Lean library

This page lists the third-party material that is in this directory: what it is, where it came from,
its copyright line and its licence. For what this library's pages call its statements, see
[TERMS.md](TERMS.md). `CREDITS-FILES.tsv` lists the Lean files among it, one by one.
`STATEMENTS.html` prints definitions and statements out of Lean files, files of this list among
them; `LIMITS.md` and `TERMS.md` quote single definitions and statements out of Lean files; these
and other pages and texts under `lean/` that print definitions or statements out of Lean files may
print out of files of this list too. `NOTICE` and `THIRD_PARTY.md` at the top of the repository list
the third-party material of the whole repository; paths of licence texts that do not begin with
`ThirdParty/` are counted from there. This page's sections bear the numbers by which comments in
this library cite them ("lean/CREDITS.md, section 4"); a number that is not here has no entry.

## The texts on the protocol

The library follows texts of four kinds, which this page keeps apart. Comments in the Lean files
call them by the names of the four headings that follow, or by the other names that are told under
the headings. Several of these words also appear in comments in their plain sense. There "was asked"
refers to a query, a test or a question among the library's makers; "advice", to what a machine is
given; "the print", to what a run printed; "that work", to a proof of work; and "worked example", to
an example in the file or in the format's documents. The published works:
[PUBLISHED-WORKS.md](../PUBLISHED-WORKS.md).

### The paper that this protocol builds on

A. Chiesa, G. Fenzi, G. Weissenberg. Zero-Knowledge IOPPs for Constrained Interleaved Codes. Revised
version, 2026; an earlier version: ePrint 2026/391. ([CFW26]) Below it is called the cited paper.

The library also follows advice and requests of the cited paper's authors. Comments at these places
speak of "advice", or say that a thing "was asked" (for example "follows advice", "goes back to
advice", "was asked for", "it was asked that").

### Further work that this protocol builds on

"Further work that this protocol builds on" is further work of the cited paper's authors.

In comments, "the work that this protocol builds on" and "the further work that this protocol builds
on" mean this work, and so does "that work" where it follows either of them. "The cited definition"
is that work's definition of the primitive.

No comment in `Johnson/Face/Protocol.lean` or `Johnson/Face/Compiler.lean` names this work. Their
notions, among them `compile` and the type of protocol that they take, `Iop.HolographicProtocol`,
follow the further work that this protocol builds on. `Iop.HolographicProtocol` is declared in
`Hiop/RecInterface.lean`, whose own comment names the worked example, this protocol's technical
report (which, it says, follows the paper that this protocol builds on) and advice as its sources,
and not this work. The idea is public: holographic IOPs and their compilation to arguments in the
random oracle model are defined in A. Chiesa, D. Ojha, N. Spooner, "Fractal: Post-Quantum and
Transparent Recursive Proofs from Holography", ePrint 2019/1076.

### The worked example

A worked example of a protocol of this kind.

### This protocol's technical report

Our own write-up of the protocol. The technical report is not in this repository. The Lean files
that cite it are not checked against the report as it stands.

Comments name further texts that are not in this repository. "A print of this protocol's technical
report" and "the print" mean this report, in a printing that may differ from the report as it
stands. "A write-up of ours", "the write-up", "a write-up of ours that is not in this repository",
"a paper of ours and its supplement" (`Cm/TargetPLayers.lean`) and "our own paper"
(`Fmt/M2Types.lean`) mean other texts of the library's makers on the protocol; comments also call
such a text "one of our own texts on this protocol". A comment that compares the Lean text with the
report, with a print of it or with one of these other texts cannot be checked from this repository;
the prints and the other texts may differ from the report as it stands, so what a comment says of
the report may not be true of the report as it stands. "The copied library", in some files of `Cm/`,
means directories of this library itself, such as `Blocks/`, `Iop/` and `Inst/`.

## Who wrote the library

AI systems wrote nearly all of the Lean library, part of it adapted from credited third-party code
([LIMITS.md](LIMITS.md), L43). This page lists those parts.

A comment in `Johnson/Top/SoundReads.lean` points here for the source of
`VerifiableInference/Statements.lean`: that file is this project's own work. In the comments of
`Ladder.lean`, `Ladder/Stored.lean` and Lean files under `Johnson/` and `AtFullSide/`, in
`ShapeLines/README.md`, and in the comments and messages of `scripts/check_stored_examples.py`, "the
package" means this repository as it is released. "The packages", in the plural, are the Lean
packages of section 2.

## 2. Lean, Mathlib and the other packages

### Mathlib

- What: the 13 Lean files under `ThirdParty/MathlibBackport/`: 18 declarations, adapted; in
  `Johnson/AtFull/ProofPlan/WrittenDesc.lean` `piecesBy` (`List.splitLengths`) and `init_last`
  (`List.dropLast_append_getLast`). In `Johnson/Desc/First/TailClaims/LayAtTest.lean` a comment
  names `Mathlib/Logic/Equiv/Fin/Basic.lean`.
- From: Mathlib (https://github.com/leanprover-community/mathlib4), tag v4.34.0, commit
  5ed2965256430c3649e86755f9576b54eca72435 (the 13 files); commit
  5e932f97dd25535344f80f9dd8da3aab83df0fe6 (`WrittenDesc.lean`). File by file:
  `ThirdParty/TAKEN-OVER.tsv`.
- Copyright, as the files' heads have it:
  - Copyright (c) 2017 Johannes Hölzl. All rights reserved.
  - Copyright (c) 2018 Chris Hughes. All rights reserved.
  - Copyright (c) 2021 Johan Commelin. All rights reserved.
  - Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
  - Copyright (c) 2021 Kim Morrison. All rights reserved.
  - Copyright (c) 2020 Anne Baanen. All rights reserved.
  - Copyright (c) 2025 Andrew Yang. All rights reserved.
  - Copyright (c) 2026 Yongle Hu. All rights reserved.
  - Copyright (c) 2024 Fangming Li. All rights reserved.
  - Copyright (c) 2024 Daniel Weber. All rights reserved.
  - Copyright (c) 2014 Parikshit Khanna. All rights reserved.
  - Copyright (c) 2018 Kenny Lau
- Licence: Apache-2.0 (`ThirdParty/MathlibBackport/LICENSE`; `LICENSE`).

### batteries

- What: in `Johnson/Desc/First/TailClaims/LayAtTest.lean` a comment names
  `Batteries/Data/Nat/Lemmas.lean`.
- From: batteries (https://github.com/leanprover-community/batteries).
- Copyright: "Copyright (c) 2016 Microsoft Corporation"
- Licence: Apache-2.0 (`LICENSE`).

## 3. ArkLib

- What:
  - the 126 Lean files under `ThirdParty/ArkLib/`, adapted (100 cut to the declarations that are
    used, 26 whole), with `ThirdParty/ArkLib/AUTHORS`. Each of the 126 begins with the first comment
    of its source.
  - in `Cb/Bridge/CodeListRSFromLines.lean` and `Cb/Bridge/CodeListRSProved.lean` one formula and
    one definition written out, and two theorems' statement and premises restated.
  - the notice in the heads of the 26 Lean files under `Johnson/Bridge/`.
  - in 14 further files a comment speaks of ArkLib itself, not only of the adapted files under
    `ThirdParty/` or of the two theorems taken from them: `Cb/G9/Split.lean`, `Code/Half.lean`,
    `Code/Lines/BerlekampWelch.lean`, `Code/Lines/Bivariate.lean`, `Code/Lines/Interpolation.lean`,
    `Code/Lines/Multiplicity.lean`, `Code/Lines/PolishchukSpielman.lean`,
    `Code/Lines/RelPrime.lean`, `Code/Lines/RelPrimeCase.lean`, `Code/Lines/ResultantDegree.lean`,
    `Code/Lines/Tight.lean`, `Code/Third.lean`, `Johnson/Desc/First/TailClaims/LayAtTest.lean`,
    `Johnson/Desc/Lens.lean`. Of `coeff_swap` in `Code/Lines/Bivariate.lean` its comment says that
    the statement "is the same text, but for one qualified name, as a line in an older, undated
    extract of ArkLib's source".
  - three of the adapted files say in ArkLib's own comments that parts are "adapted, with
    permission, from" kz99/rs-ld-mca: `ThirdParty/ArkLib/Data/MvPolynomial/WeightedOrder.lean`,
    `ThirdParty/ArkLib/Data/Polynomial/Differential/Types.lean`,
    `ThirdParty/ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/ConstraintMap.lean`.
    In three more, ArkLib's own comments mention earlier revisions of ArkLib, and in one of these
    three also proximity-prize: `ThirdParty/ArkLib/Data/MvPolynomial/WeightedDegree.lean`,
    `ThirdParty/ArkLib/Data/Polynomial/ResultantDegree.lean`,
    `ThirdParty/ArkLib/Data/Polynomial/FractionFieldResultant.lean` (`ThirdParty/TAKEN-OVER.tsv`
    quotes them).
- From: ArkLib (https://github.com/Verified-zkEVM/ArkLib), from a copy marked as commit
  2817d8c7d2f28d706b17f8de0f885880d0b2eb13. File by file, with what was changed:
  `ThirdParty/TAKEN-OVER.tsv`; `ThirdParty/README.md`.
- Copyright, as the files' heads have it:
  - "Copyright (c) 2026 ArkLib Contributors. All rights reserved." (125 adapted files)
  - "Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved." (1 adapted file)
  - "Copyright ArkLib Contributors" (the notice in the heads of the Lean files under
    `Johnson/Bridge/` and of the two files of `Cb/Bridge/` that are named above)
  - "Copyright (c) 2024-2026 ArkLib Contributors", "Copyright (c) 2024-2025 ArkLib Contributors"
    (`Cb/G9/Split.lean`; the first also `Johnson/Desc/First/TailClaims/LayAtTest.lean`)
- Licence: Apache-2.0 (`ThirdParty/ArkLib/LICENSE`; the same text: `ThirdParty/LICENSE`).

### CompPoly

- What: `ThirdParty/ArkLibShim/BivariateDegreeX.lean`: "Stands in for two names of the package
  CompPoly".
- From: CompPoly (https://github.com/Verified-zkEVM/CompPoly), module
  CompPoly.ToMathlib.Polynomial.BivariateDegree.
- Copyright: "Copyright 2025 Demerzel Solutions Ltd (t/a Nethermind)"
- Licence: Apache-2.0 (`LICENSE`).

## 4. VCV-io

- What: in 15 Lean files a comment names VCV-io: `Hash/OctopusFacts.lean`,
  `Johnson/Bind/RejectsAll.lean`, `Johnson/Desc/First/TailClaims/LayAtTest.lean`,
  `Johnson/LinkSim/Shift.lean`, `Prob/Count.lean`, `Prob/Linear.lean`, `Prob/Tv.lean`,
  `Rom/Eager.lean`, `Rom/EagerLazy.lean`, `Rom/Measure.lean`, `Rom/OComp.lean`, `Rom/OSpec.lean`,
  `Rom/Prefix.lean`, `Rom/UpToBad.lean`, `ZKCP/Defs.lean`. Where a comment says "Shared with
  VCV-io", this page does not say what is shared: it has VCV-io's address, copyright line and
  licence alone.
- From: VCV-io (https://github.com/Verified-zkEVM/VCV-io).
- Copyright, as `NOTICE` has it:
  - "Copyright (c) 2026 Quang Dao" (for `Johnson/Desc/First/TailClaims/LayAtTest.lean`, whose head
    has it)
  - The authors of each source file of VCV-io are named in its header.
- Licence: Apache-2.0 (`LICENSE`).

## 5. Lean's own source

- What: `Johnson/Unfolds/MergeSort.lean` (two definitions, adapted);
  `Johnson/Unfolds/SliceFoldl.lean` (two definitions, adapted; one comment, restated);
  `Johnson/Unfolds/SplitOn.lean` (one definition and the body of a second, adapted);
  `Johnson/AtFull/ProofPlan/WrittenDesc.lean` (`initOf`: `List.dropLast`; `lastOf`: `List.getLast`);
  `Johnson/AtFull/Desc/SpotsWritten.lean`, `Johnson/PV/EntryInKey.lean`,
  `Johnson/Unfolds/KernelRfl.lean`.
- From: Lean (https://github.com/leanprover/lean4; the toolchain leanprover/lean4:v4.29.1). Which
  routines, files and lines: the first four files' heads.
- Copyright, as the files' heads or `NOTICE` have it:
  - Copyright (c) 2016 Microsoft Corporation. All rights reserved.
  - Copyright (c) 2024 Lean FRO. All rights reserved.
  - Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
  - Copyright (c) 2022 Microsoft Corporation. All rights reserved.
- Licence: Apache-2.0 (`LICENSE`).

## 6. BLAKE2b

- What:
  - adapted: `Run/Blake2b/Compress.lean`, `Run/Blake2b/Hash.lean`, `Run/Blake2b/Salted.lean`,
    `Run/Blake2b/Spec.lean`.
  - definitions or statements of these, written out again: `Fmt/Blake2bFast.lean`,
    `Johnson/Unfolds/SecondHashFunctionList.lean`, `Run/Blake2b/CompressThm.lean`,
    `Run/Blake2b/LoadThm.lean`, `Run/Blake2b/ResumeThm.lean`, `Run/Blake2b/SaltedPlain.lean`,
    `Run/Blake2b/SpecThm.lean`, `Run/Blake2b/WordsThm.lean`.
  - the notice in the heads of `Johnson/Unfolds/SecondHashFunctionChain.lean`,
    `Johnson/Unfolds/SecondHashFunctionTree.lean`, `Johnson/Unfolds/SecondHashFunctionWords.lean`.
  - expected digests in `Run/Blake2b/Spec.lean` and `Run/Blake2b/KnownThm.lean`; six in
    `Run/Blake2b/Test/Vectors.lean`, which "come from blake2b-ref.c of the BLAKE2 reference source
    code package"; in `Fmt/Blake2bKnown.lean` expected "words were computed with blake2b_compress of
    blake2b-ref.c".
- From: BLAKE2 reference source code package (https://github.com/BLAKE2/BLAKE2): `blake2b-ref.c`,
  `blake2.h`, `blake2-impl.h`; the expected digests from `blake2-kat.h` of libb2 0.98.1.
- Copyright:
  - `Copyright 2012, Samuel Neves <sneves@dei.uc.pt>.` The head of `Run/Blake2b/Compress.lean` has
    the reference's own notice as it is. Of the other heads, those that bear this line have it as
    `Copyright 2012, Samuel Neves`, except that of `Run/Blake2b/Spec.lean`, which has it as
    `Copyright 2012 Samuel Neves`; those of `Run/Blake2b/CompressThm.lean`,
    `Run/Blake2b/LoadThm.lean` and `Run/Blake2b/SpecThm.lean` have both forms.
  - `Written in 2012 by Samuel Neves <sneves@dei.uc.pt>` (libb2 0.98.1)
- Licence: CC0-1.0 (`licenses/BLAKE2-54f4faa4.COPYING`).

Comments also name RFC 7693, as the specification of BLAKE2b and for one expected digest:
[PUBLISHED-WORKS.md](../PUBLISHED-WORKS.md).

### CPython

- What: expected digests, computed with its `hashlib`, in 7 Lean files: `Fmt/Blake2bKnown.lean`,
  `OnBytes/Hash/TestBlake2b.lean`, `Run/Blake2b/Test/KnownAnswers.lean`,
  `Run/Blake2b/Test/OtherOrigin.lean`, `Run/Blake2b/Test/Salted.lean`,
  `Run/Blake2b/Test/SpecKnown.lean`, `Run/Blake2b/Test/Vectors.lean`.
- From: CPython.
- Copyright: "Copyright (c) 2001-2024 Python Software Foundation; All Rights Reserved"
- Licence: PYTHON SOFTWARE FOUNDATION LICENSE VERSION 2 (`licenses/CPython-3.13.16.LICENSE.txt`).

## 7. Constants

### plonky2

- What: `OnBytes/Field/Word.lean`: "These are the steps of the function reduce128 of the plonky2
  library".
- From: plonky2 (https://github.com/0xPolygonZero/plonky2), `field/src/goldilocks_field.rs`.
- Copyright: "Copyright (c) 2022-2025 The Plonky2 Authors"
- Licence: Apache-2.0 or MIT; this repository takes MIT (`licenses/plonky2.LICENSE-MIT`).

### SplitMix64

- What: in three Lean files a comment names it: `OnBytes/Model/Frame.lean`,
  `OnBytes/Model/TestFrame.lean`, `OnBytes/Model/TestLookProver.lean`.
- From: splitmix64.c by Sebastiano Vigna (https://prng.di.unimi.it/splitmix64.c).
- Copyright: "Written in 2015 by Sebastiano Vigna (vigna@acm.org)"
- Licence: public domain, with a permission notice (`NOTICE`).

## 8. The model

What the release holds that depends on Meta's models: `THIRD_PARTY.md`, "What depends on Meta's
models". In Lean files under `lean/` that is: the value 53,687 (35 files), the parameter line "s 15"
(8), `s 15` as a field (2), the reference scales written out (8), some but not all of them (37), the
reference scale 2,307 (47), the reference table that is made from them (1), a table of scales made
by a written rule from Lean's ranges and these files' tests, two of whose shifts, and the norms'
bits - shift, have the reference table's number, or numbers reckoned from them (5), the value 25,856
(33), SHA-256 digests of the full-size example's `policy.txt`, `layout.txt` and `KL.bin` (13),
SHA-256 digests of the small configurations' `policy.txt`, `layout.txt` and `KL.bin` (3), the
planner's digest of `policy.txt`, `layout.txt` and `KL.bin` in examples/full-size/config/ together
(4), the model's sizes or configuration keys (9), the full-size example's parameter file whole (3),
a small configuration's parameter file whole (4), the layout file of a configuration whole (5), a
piece of layout.txt of the full-size configurations, as decimal bytes (14), `S 12`, `rx 8`, and the
digest lines `texp0` to `texp7` that follow from them (23), and bytes of a small configuration's
`KL.bin` (7): 172 files in all (a file may hold several), each with a row in `CREDITS-FILES.tsv`.
One made page (`STATEMENTS.html`) and one text from which it is made
(`scripts/statements-html/front/rows.txt`) print some of these. Other pages and texts under `lean/`
that print definitions or numbers out of Lean files may print some too, the model's sizes above all;
they are not listed one by one here. The scale file of the full-size example stands whole in the
Lean files `Johnson/G/KitFull.lean`, `Johnson/Road/FormsKeysRunK.lean`,
`OnBytes/Tie/Pv/Plan/PlanKits.lean`; this page and `CREDITS-FILES.tsv` themselves write several of
these values; `GAPS.md`, `LIMITS.md` and `THEOREM.md` each have 25,856 and a run's finding that
every range condition held on each of some hundreds of windows of 1,024 tokens. Where the reference
scales' numbers come from (`Inst/Model/Scales.lean`, `Inst/Model/Program.lean`,
`Cm/Rel2Guards.lean`): the same table of `THIRD_PARTY.md`; [LIMITS.md](LIMITS.md), "The reference
table.". The head of `Inst/Model/Program.lean`: "The sizes in `ppref` are those of the text model of
Llama 4 Maverick". The sentences that follow, to the end of this paragraph, are those of
`THIRD_PARTY.md` and speak of its table under "What depends on Meta's models". The table may lack a
place, above all under lean/, for the numbers of the model's shape, and for a value in another
coding or unit, a value that is reckoned and not written out, or a short run of small numbers. Under
lean/ the searches behind this table reach, of its values, 53,687, 25,856, the parameter line
"s 15", the lines S 12, rx 8 and texp0 to texp7 and the scales, and not most of the others; the rows
on the model's sizes are not all their places: the vocabulary's size alone, 202,048, stands in 163
Lean files; no search covers the other numbers of the model's shape; S = 12 and rx = 8, written as
equations, stand in 32 Lean files beside those listed; the rotary base 500,000 stands in 44 Lean
files, and no row names it under lean/; numbers that the planner reckons from the full-size files
(plans, ranges, counts, the layout as read values) stand written out in many more Lean files and are
not listed; and the searches do not reach every figure that a run on the public weight files gave.
What the table says of where each value comes from rests on the records of how the files were made,
which are not in this repository, and on what the repository's own files and pages say of it.

### Hugging Face transformers

- What: `IntegerModel/Model.lean`: "The same as the public code (transformers 5.17.0,
  modeling_llama4.py)".
- From: Hugging Face transformers, version 5.17.0 (https://github.com/huggingface/transformers):
  `modeling_llama4.py`.
- Copyright: "Copyright 2018- The Hugging Face team. All rights reserved."
- Licence: Apache-2.0 (`LICENSE`).

## 9. Published works that the files cite

See [PUBLISHED-WORKS.md](../PUBLISHED-WORKS.md). A key in round brackets in a Lean file, such as
(BCFW25), names the row of that page that begins with that key; "the row on Token-DiFR" in a comment
is a row of that page; where the idea of `Doomed` comes from is told there too.

## The audit page

The design of `STATEMENTS.html`, and its paragraph "Checking the proofs yourself", are modelled on
veil.succinct.xyz (Succinct).

- What: `scripts/statements-html/shell/page.css`, `scripts/statements-html/shell/page.js`,
  `scripts/statements-html/shell/page_template.html`, `scripts/statements-html/front/setting.txt`,
  `STATEMENTS.html`.
- From: adapted from succinctlabs/veil-formal-verification (frontend/ and README).
- Copyright: "Copyright 2026 Succinct Labs"
- Licence: Apache-2.0 (`LICENSE`).

## Acknowledgments

We thank Alessandro Chiesa, Giacomo Fenzi, Guy Weissenberg, Miranda Christ, Rahul Dalal, and
Ben Mayer for their input and collaboration on FlashProve.

## If you take only this directory

`LICENSE` in this directory is the text of Apache-2.0. This directory has no `NOTICE` of its own:
take the repository's `NOTICE`, `THIRD_PARTY.md`, `PUBLISHED-WORKS.md` and `licenses/`, whole, with
it.
