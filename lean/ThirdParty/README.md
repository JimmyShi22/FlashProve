# lean/ThirdParty: Lean text taken over from ArkLib and Mathlib

Terms: [TERMS.md](../TERMS.md).

This folder holds Lean files that were written by others and adapted for this library.

## Why it is here

The library's bound on agreement of Reed-Solomon codes below the Johnson radius, `Cb.BCHKS46` (and its
form at one pair of fields, `Cb.BCHKS46At F E`), is proved in `lean/Cb/Bridge/CodeListRSFromLines.lean` and
`lean/Cb/Bridge/CodeListRSProved.lean` from two theorems of ArkLib:

| theorem | file here |
|---|---|
| `ReedSolomon.exists_johnson_line_exactCorrelatedPair` | `ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Agreement.lean` |
| `ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate` | `ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/Johnson/FiniteBounds.lean` |

AI systems adapted and built the 139 files of this folder that were taken over. The adapted files
were compared with their sources by program; the mathematics was not followed line by line. The
library's full check builds and replays these files with the rest. What has run over this tree:
`lean/CHECK-RESULTS.md`. Lean checks these proofs. It does not check that the adapted statements and
definitions mean what the sources' do; that has not been independently reviewed (`lean/LIMITS.md`,
L15).

ArkLib is built on a newer Lean and a newer Mathlib than this library, so it cannot be imported as a
package. This folder holds the two theorems and what they rest on, adapted to this library's versions.

The mathematics is described in the long comment (`/-! ... -/`) at the top of each of ArkLib's files. Those
comments cite papers by key. The keys, from ArkLib's `blueprint/src/references.bib`:

- [DKT26] Quang Dao, Scott Duke Kominers, Justin Thaler. *Reed-Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs.* Cryptology ePrint Archive, Paper 2026/2056.
- [BCPZZ26] Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng. *Algorithmic List
  Decoding of Reed-Solomon Codes up to Capacity in the Low-Rate Regime.* ECCC Report TR26-164.
- [BCHKS25] Eli Ben-Sasson, Dan Carmon, Ulrich Haböck, Swastik Kopparty, Shubhangi Saraf. *On Proximity Gaps
  for Reed-Solomon Codes.* Cryptology ePrint Archive, Paper 2025/2055.
- [DKTZ26] Quang Dao, Scott Duke Kominers, Justin Thaler, Kai Zhe Zheng. *Reed-Solomon List Decoding and
  Mutual Correlated Agreement up to Capacity.* Manuscript, 2026.
- [Kop15] Swastik Kopparty. *List-Decoding Multiplicity Codes.* Theory of Computing 11(5), 2015.

## What is in it

| folder | what | from |
|---|---|---|
| `ArkLib/` | 126 files (100 trimmed to the declarations that are used, 26 whole), 1,032 declarations (of the 1,722 in those files) | [ArkLib](https://github.com/Verified-zkEVM/ArkLib), from a copy marked as commit `2817d8c7d2f28d706b17f8de0f885880d0b2eb13` (Lean v4.34.0, Mathlib v4.34.0) |
| `MathlibBackport/` | 13 files, 18 declarations that this library's Mathlib does not have and that ArkLib's proofs use: by name, through `simp`, or through another of the 18 | [Mathlib](https://github.com/leanprover-community/mathlib4), tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435` |
| `ArkLibShim/` | 1 file that stands in for two names of the package CompPoly, `Polynomial.Bivariate.degreeX` and `Polynomial.Bivariate.coeff_natDegree_le_degreeX`, which ArkLib imports from it. Three of the theorems that the two theorems rest on name them, two of them in their statements. The statements of the two theorems themselves do not. | [CompPoly](https://github.com/Verified-zkEVM/CompPoly), module `CompPoly.ToMathlib.Polynomial.BivariateDegree` |
| `ArkLibCheck/` | 1 file of our own: the build fails unless the two theorems rest on `propext`, `Classical.choice` and `Quot.sound` alone | |
| `scripts/` | the program that compares this folder with its sources, and its three tables | |

This library is on Lean v4.29.1 and Mathlib commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.

`TAKEN-OVER.tsv` has one row for each Lean file here: what was taken over, from which file and commit, and
what was changed. Six rows also give the further sources that ArkLib's own comments name (see "Licences"
below). Its last two rows are for two files outside this folder. `lean/Cb/Bridge/CodeListRSFromLines.lean`
writes out ArkLib's `johnsonComparisonEstimate` (in `estM` and `est`) and restates in Mathlib's terms what the two
theorems give together (`LineFact`). `lean/Cb/Bridge/CodeListRSProved.lean` applies the two theorems by name
(`lineFact`, `arkLibCount_le_est`) and proves that `est` is ArkLib's estimate (`est_eq_arkLib`). Both rows also
name a file of ArkLib that is not in this folder and that the two files' heads name
(`ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean`). The program wrote
the list, and checks that it is still what it would write.

`lean/Johnson/Bridge/` is a further folder, for files that apply this library's
own statements on codes and on lists to the format's code: `FoldErrLin.lean` and the two files `Point*.lean` to the
fold of the test on a stored table, the others to the base cases, the folds, the code switches and the rounds of
positions of the proximity tests (`lean/CREDITS-FILES.tsv` has a row for each). Such a file stands above files of
`OnBytes/` by its imports, which a file under `Cb/` may not (`lean/scripts/IMPORTS.txt`). Where it uses
`Cb.Bridge.bchks46At`, by name or through a file that it imports, it rests on this folder's proofs. It has no row
in `TAKEN-OVER.tsv`; the long comment at its head has a notice on ArkLib.

## What was cut

ArkLib's file with the first theorem reaches 203 of ArkLib's files through its imports, itself included.
Most of what they hold is not used by the two theorems. The declarations kept are:

1. every declaration that Lean finds under the two theorems, by following all constants in their
   statements and in the proof terms that Lean builds (966: 961 under their own names, 5 through
   constants that Lean generates from them; run on ArkLib at its own versions);
2. declarations that the text of a kept declaration names although the term that Lean builds does not
   contain them, such as an unused entry of a `simp` list, with what those name in turn (10);
3. `simp` lemmas and instances in whose statements a search of the text finds a declaration of ArkLib and
   none that was cut, with what their own proofs name (56). `simp` can use a lemma that is proved by `rfl`
   without leaving a trace in the proof term, so step 1 does not find such lemmas. The search does not see a
   name written with dot notation, so it is not complete: four `simp` lemmas that speak of kept declarations
   or of Mathlib's alone were cut (`MvPolynomial.coe_basisRestrictSupport_apply`,
   `MonomialOrder.standardExponents_top`, `MonomialOrder.standardQuotientEquiv_apply`,
   `Ideal.coe_minimalPrimesFinset`). That the cut builds shows that no kept proof needs them.

`scripts/kept_declarations.tsv` lists all 1,032, and the 18 of Mathlib. The same cut of ArkLib also builds on
ArkLib's own versions (Lean v4.34.0, Mathlib v4.34.0), with the same stand-in for CompPoly's two names and the
same answer on axioms.

The long comments (`/-! ... -/`) of a file are ArkLib's, unchanged; the one at the top may name declarations
that were cut. The long comments of Mathlib's files are not taken over.

## What was changed

In every file: the import lines are replaced, and the words of Lean's module system (`module`,
`public import`, `@[expose] public section`) are removed. Each file begins with the first comment of the
file it came from (copyright, licence, authors). A note below it says where the file came from and what
was changed.

Beyond that, by count (the program prints these numbers):

| change | `ArkLib/` | `MathlibBackport/` |
|---|---|---|
| statements of theorems | 2 | 0 |
| definitions | 0 | 0 |
| proofs | 29 | 3 |
| files with changed lines between declarations (`namespace`, `section`, `open`, `variable` and the like) | 2 | all 13 |
| doc comments | 1 | 0 |
| places where one of 11 renamed lemmas of Lean or Mathlib is called by its older name | 36 | 1 |

`scripts/listed_changes.tsv` has a row for each change of the first five kinds, with the reason (and a row for
each of the two files of `ArkLibShim/` and `ArkLibCheck/`).
`scripts/renamed_lemmas.tsv` has the 11 names. A proof that differs from its source by those names alone is
counted in the last row and not as a changed proof. A renaming inside a changed proof is counted with that
proof. One definition, `MvPolynomial.supportWeightLE`, calls a renamed lemma in a proof argument; it is
counted in the last row.

- **The two statements** are `Polynomial.separable_map_of_irreducible_of_derivative_ne_zero` and
  `Polynomial.resultant_derivative_ne_zero_of_irreducible`
  (`ArkLib/Data/Polynomial/FractionFieldResultant.lean`). Their premise `[IsGCDMonoid R]` (greatest common
  divisors exist) became `[NormalizedGCDMonoid R]`, because this library's Mathlib has no `IsGCDMonoid`, and its
  Gauss lemma, which the first of the two proofs calls, asks for `NormalizedGCDMonoid`. In this
  library's Mathlib that class is a chosen gcd with a normalization that respects products; Mathlib v4.34.0
  calls this `StrongNormalizedGCDMonoid` and gives the name `NormalizedGCDMonoid` to less. So the premise here
  asks more than ArkLib's, and the two lemmas say less than ArkLib's, never more. Both are among the
  declarations that the two theorems rest on. The name `NormalizedGCDMonoid` also stands, word for word as in
  the source, in the premises of `Finset.gcd_eq_sum_mul` (`MathlibBackport/RingTheory/PrincipalIdealDomain.lean`)
  and of three of the four declarations of `ArkLib/ToMathlib/LinearAlgebra/Matrix/PrimitiveKernel.lean`
  (`Finset.span_gcd`, `Ideal.span_range_eq_top_iff_univ_gcd_eq_one`,
  `Matrix.exists_primitive_kernel_vector_eq_smul`). There too it asks more here than in the source, although the
  table counts those statements as unchanged. `TAKEN-OVER.tsv` says so in the two files' rows.
- **The rest of the statements.** The statements of the two theorems, and every definition that those
  statements use, are ArkLib's, word for word. Lean reads the same words against this library's Mathlib, so
  equal words are not a proof of equal meaning. That bears on the credit, not on the truth of `Cb.BCHKS46`,
  which Lean checks from this folder as it stands.
- **The proofs** were changed where the older Lean or Mathlib behaves differently. The kinds of change:
  a `beta_reduce` added; a `positivity`, `field_simp`, `simpa` or `rw` step helped along or replaced by a term;
  `.isPrime` and `.le` on a minimal prime written as `.1.1` and `.1.2`; a lemma called by another name;
  `funext` written as `_root_.funext`; two lines removed after a `convert` that already closes the goal; an
  instance of `NormalizedGCDMonoid` supplied; a hypothesis supplied that the older lemma asks for; higher limits
  (`maxHeartbeats`, `synthInstance.maxHeartbeats`).
  The changes are small: in each of the 32 proofs at most 8 words of the source were removed and at most 25
  added (a word is text between spaces; `TAKEN-OVER.tsv` has the two numbers for each proof). One short proof
  takes another route: `Ideal.height_eq_zero_iff_eq_bot` in `MathlibBackport/` is proved from the definition
  of height, because the lemmas that Mathlib's proof calls are not taken over.
- **The lines between declarations.** In `ArkLib/`: `open Polynomial CoreDefinitions` became `open Polynomial`
  in one file, and a section that the cut left empty was removed from another. In `MathlibBackport/` these
  lines are our own, since only a few declarations of each file are taken over. The program holds them
  to a fingerprint but cannot compare them with Mathlib's. They give each of the 18
  statements the variables that it has in Mathlib, in the same order (by reading; not machine-checked).

## How to check

Lean checks the mathematics. `lake build` builds this folder with the rest of the library (the library's
`lakefile.toml` names the folder as `"ThirdParty.+"`), and `ArkLibCheck/Axioms.lean` fails the build if either
theorem rests on anything but Lean's three standard axioms, an unfinished proof below it among them. Beyond
that check, a build alone does not fail on an unfinished proof or on a new axiom: the full check does
(`lean/CHECKING.md`).

The program compares the text with its sources:

```
git clone https://github.com/Verified-zkEVM/ArkLib
git -C ArkLib checkout 2817d8c7d2f28d706b17f8de0f885880d0b2eb13
git clone https://github.com/leanprover-community/mathlib4
git -C mathlib4 checkout v4.34.0
python3 lean/ThirdParty/scripts/compare_with_sources.py --arklib ArkLib --mathlib mathlib4
```

It compares every declaration here with the declaration of the same name in the outside file (statement,
proof, doc comment), the lines between declarations and ArkLib's long comments, word for word (white space
does not count), and the first comment of every file, byte for byte. It also checks that our files hold no
other code, that they import nothing but modules of Mathlib, Batteries and this folder, that each note begins
with the right file and commit, that the `LICENSE` and `AUTHORS` files are the projects' own, that the folder
holds no further file, and that `TAKEN-OVER.tsv` is the list that it would write.
Every difference must have a row in `listed_changes.tsv`, and every row there must be a difference, but for
the two rows of those two files. A row carries a fingerprint of our text, so it covers that text and no other.
Its last line begins `RESULT: all as listed`, with exit status 0, or it names what does not fit. Where it cannot
read a checkout's commit (no git), that line says so.
With `--write-list FILE` it writes that list to FILE instead of comparing it. FILE must not exist yet: the program
overwrites no file.

The two Lean files outside `ArkLib/` and `MathlibBackport/` (`ArkLibShim/`, `ArkLibCheck/`) are compared with no
outside file; the program holds them to a fingerprint, and what the list says of them is fixed in the program. It
does not look at
other comments, at the rest of the note under the first comment of each file (what was changed), at this page,
at which modules of Mathlib a file imports, or at `lean/Cb/Bridge/` (the last two rows of the list are fixed in
the program). The list's sentences on further sources are fixed in the program too; it checks only that the mark
of each such source (the name of a repository, or a commit) stands in the files for which the list names it, and
in no other file taken over. The sentence on `NormalizedGCDMonoid` in two rows is fixed in the program as well; it
checks only that the letters `[NormalizedGCDMonoid`, with a blank behind them, stand outside every comment somewhere
in each of the two files. But for that, `--help` says exactly what is compared and how a fingerprint is made.

The program was run not on fresh clones but on the copy of ArkLib named under "What is in it", which is marked
as that commit, and on the copy of Mathlib that Lake fetches for that tag. Where the list and the notes in the
files say "commit" of ArkLib, they go by that mark.

## If this library's Mathlib is raised

The 18 declarations of `MathlibBackport/` bear Mathlib's own names. If the library's Mathlib has one of them,
Lean refuses the second declaration of the name. Then:

1. Remove that declaration here, or its file with the imports of it. A file that imported it may then need
   Mathlib's own module.
2. In `scripts/`, take the declaration's row out of `kept_declarations.tsv`, and its rows, if any, out of
   `listed_changes.tsv`.
3. If the file is gone, take out its row `(lines between declarations)` as well. If it stays, put into that row
   the fingerprint that the program's complaint prints: that fingerprint covers the names of the file's
   declarations.
4. Write the list to a new file outside this folder (`--write-list NEW.tsv`), put it in the place of
   `TAKEN-OVER.tsv`, and set right the file's note and the numbers 18 and 13 on this page, which the program does
   not read.
5. If this library's Mathlib has `StrongNormalizedGCDMonoid`, take `ASKS_MORE` and its two files out of the
   program, and the lines on it out of "What was changed".

## Licences

ArkLib and Mathlib are released under the Apache License, Version 2.0. Its text is in `LICENSE` in this folder;
`ArkLib/LICENSE` and `MathlibBackport/LICENSE` are the two projects' own copies, and `ArkLib/AUTHORS` is
ArkLib's list of authors. Neither our copy of ArkLib nor the release archive of Mathlib at v4.29.1 has a NOTICE
file; whether Mathlib's repository at tag v4.34.0, from which the files under `MathlibBackport/` were taken, has one
is not known here.
The copyright and author lines of each of the 139 files taken over stand at its start, as in the source. CompPoly's
copyright line and licence: `lean/CREDITS.md`, "CompPoly". The long comments of six of the files taken over from
ArkLib name sources of their own (`TAKEN-OVER.tsv` names the same sources in the six files' rows):

- `ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/ConstraintMap.lean`,
  `ArkLib/Data/MvPolynomial/WeightedOrder.lean` and `ArkLib/Data/Polynomial/Differential/Types.lean`: the
  formalization `kz99/rs-ld-mca` (in the first two files: "Kai Zhe Zheng's"). In ArkLib's words, parts of the first
  two files, and the definitions of the third, are "adapted, with permission, from" it.
- `ArkLib/Data/MvPolynomial/WeightedDegree.lean`: ArkLib at revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
- `ArkLib/Data/Polynomial/ResultantDegree.lean`: ArkLib at revisions `66f3d089a41704597f54d641b78254d2a8f361f8`
  ("Alexander Hicks and Aleph's field-only result") and `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
- `ArkLib/Data/Polynomial/FractionFieldResultant.lean`: ArkLib at revision
  `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, and commit `19bc7d3e21b2261257e1961acd720b2c395d87e1` of
  https://github.com/proximity-prize/proximity-prize ("Remco Bloemen's BCHKS formalization").
