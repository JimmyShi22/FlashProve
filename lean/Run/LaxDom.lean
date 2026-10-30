-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/LaxDom.lean: the lenient reader gives the same result at two hash functions that agree on the
hash function's domain, given four bounds on sizes, the answers of one having their length.

The format's hash function `Fmt.formatHash` has a domain (Fmt/Rules23.lean: `hDom`). Theorems on the run of
"the lenient reader, then the verifier" (Run/ParserHash.lean) have on their right side the reader
at `Fmt.HO Fmt.oracle`, the format's hash function rebuilt from the format's oracle; an evaluation
takes `Fmt.formatHash` itself. The two agree on the domain (Fmt/Rules23Laws.lean: `HO_oracle`), and beyond
it no agreement of the two is stated in Run/ or Fmt/ (see part 4). This file states that, under
four bounds that can be tested, either hash function may stand for the other. The reason is in the
proofs: under these bounds the reader never leaves the domain. (The lenient reader, `laxWhole` in
Run/ParseLax.lean, only cuts the file into its parts. The lenient reader also refuses some files
(what it refuses: part 1 of the head of Run/ParseLax.lean). It still recomputes the hash chain,
because the drawn positions say how long the parts are; it tests no proof of work, walks no path
and compares no root. Behind it the compiled verifier walks the paths and compares the roots
itself; proof of work is tested where the protocol's `accept` tests it.)

1. What the file contains.
   `smallB S b`: four bounds that no test of the reader gives, not even `Spec.ok`. (But
      `Spec.small`, the first clause of `Spec.ok` in Fmt/Rules8.lean, has the first, the second and
      the fourth of them, and in place of the third a bound on each round's message. The statements
      here assume all four.) The parameters' bytes number at most 2^32 − 144. The statement's bytes
      + 88 are at most that (what is hashed for the first chain value: two digests of 32 bytes,
      three words of 8, the statement). The file's bytes + 16 are at most that (a round's message
      is cut out of the file; 16 bytes follow it in a call). There are fewer than 2^63 rounds (the
      index under the number 162 is the round's number). `smallB` can be run: at a given
      description and file it is one test.
   Two statements (`Run.Spec.lax_dom`, `Run.Spec.lax_HO`).
   What the domain asks of the lenient reader's four kinds of calls (the parameters' digest, number
      169; the run's value, 172; the first chain value, 160; a round's calls, 162), and where each
      condition comes from:
      the number, the tree's place, a start of 32 bytes, zero where the number takes none: the
         constants of the calls; for 162 the reader's own test (Fmt/Rules5.lean: `askOK`: the label
         below 2^48, the chain value of 32 bytes);
      the index under 172 and 160, which is the label: the reader's own test (below 2^32);
      the digests that enter later calls have 32 bytes: the hash function's answers have their
         length, a hypothesis on h in the general statement, true of `Fmt.formatHash`;
      the bounds on the number of bytes and on the round's number: `smallB`.

2. What is checked when the file compiles. Nothing beyond the types; there are no tests (#guard)
here.

3. Theorems. Both statements are proved in Run/LaxDomProofs.lean.
   `parseLaxW` is the lenient reader followed by the step that types its output. `Spec.ok` is not
   asked (the reader tests it itself).

4. What is not claimed.
   The strict reader is not treated here: it also hashes leaves and vertices, for which two more
   bounds are needed (a column's bytes; 2^depth + position below 2^63). That is done in
   Run/OpenDom.lean (an opening; its test `smallSh` has five clauses), Run/FullDom.lean (the reader
   that fills in whole paths) and Run/StrictDom.lean (the strict reader).
   It is not claimed that the bounds are needed. Outside the domain no agreement of the two hash
   functions is stated in Run/ or Fmt/; it is not shown that they then differ, but for one test at
   the reserved number 177 (see below). (See 1 on `Spec.small`: the reader tests `Spec.ok` before
   it hashes, and that test has three of the four bounds and, in place of the third, a bound on
   each round's message.) (On the oracle outside the format's image (`Fmt.inImage`,
   Fmt/Rules23.lean): `Fmt.oracle_out`, Fmt/Rules23Laws.lean; and two tests of `Fmt.HO Fmt.oracle`
   at the reserved number 177, which the lenient reader never calls: Fmt/Rules23.lean.)
   Nothing is said on what the reader computes.

Sources. Written against the format page (docs/format/FORMAT.md, which comes with the programs) at
an edition that is not the one that ships, rules R2.3 and R2.4 on the domain; these were reported
the same at a second edition by a second, independent reading. Also seen (not held against the page
that ships): at a third edition R2.3 has one further clause (a column has at least one word), and at
a fourth R2.4 has one further clause, on the leaves of stored trees; both concern leaves, which the
lenient reader does not hash.

Terms: lean/GLOSSARY.md.
-/
import Run.ParseLax
import Fmt.Rules23Laws

set_option autoImplicit false

namespace Run
open _root_.Fmt (hDom dlen Kind Chain Plan Spec St)

/-- The type of a hash function in the identity monad: number, tree, index, start, bytes. -/
abbrev HId : Type := Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray

/-- The sizes that the hash's domain asks and no test of the reader gives (but see the head, 1, on
`Spec.small`). -/
def smallB (S : Spec) (b : ByteArray) : Bool :=
  decide (S.params.size ≤ 2 ^ 32 - 144) && decide (S.statement.size + 88 ≤ 2 ^ 32 - 144) &&
    decide (b.size + 16 ≤ 2 ^ 32 - 144) && decide (S.rounds.length < 2 ^ 63)

namespace Spec

/-- States: if h' and h agree on the domain, the answers of h have `dlen n` bytes and
`smallB S b = true`, then `parseLaxW` gives the same at h' and at h. What is not claimed: the head,
4. -/
def lax_dom : Prop :=
  ∀ (h h' : HId), (∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b) →
    (∀ n t i s b, ByteArray.size (h n t i s b) = dlen n) →
    ∀ (Y : Type) (E : Iop.ExtSpec) (Q : Iop.BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
        (T : Typing Q) (b : ByteArray),
      smallB S b = true → parseLaxW (m := Id) h' S T b = parseLaxW (m := Id) h S T b

/-- States the equation of `lax_dom` at h' := `Fmt.HO Fmt.oracle` and h := `Fmt.formatHash`; its only
hypothesis is `smallB S b = true`. What is not claimed: the head, 4. -/
def lax_HO : Prop :=
  ∀ (Y : Type) (E : Iop.ExtSpec) (Q : Iop.BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    smallB S b = true →
    parseLaxW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) S T b =
      parseLaxW (m := Id) _root_.Fmt.formatHash S T b

end Spec
end Run
