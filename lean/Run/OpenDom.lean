-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OpenDom.lean: the reader of a Merkle opening gives the same result at two hash functions that
agree on the hash function's domain, given bounds on the tree's shape and the hypotheses under 3.

This is a companion of Run/LaxDom.lean, whose head explains why the hash function's domain
(Fmt/Rules23.lean: `hDom`) matters. The reader of an opening (Fmt/Rules7.lean: `readOpeningW`)
hashes leaves and inner vertices. A second statement concerns the lenient reader with the reader of
openings as a parameter (Run/ParseLax.lean: `cutWhole`; its fold over rounds is `cutFold`) when it
is given two readers of openings that agree at the arguments named under 3 (these cover all that
occur).

Sources. The rules of the format page (docs/format/FORMAT.md, which comes with the programs) that
matter here are R2.1 to R2.4 (rendered in Fmt/Rules23.lean: hDom, leafPlace, leafOK) and R7.3, R7.4,
R7.7,
R7.16 (Fmt/Rules7.lean). The file follows an edition of the page that is not the one that
ships, through restatements of these rules and the renderings of these rules in Fmt/.
The rules named were compared with the page's whole text at a second such
edition in a second, independent reading, except for R2.4's image. By the same reading, each of the
first four clauses of smallSh is a condition of the page on a shape, exactly at its border (R2.3,
R7.16; that W is at least 1 stands in R2.3's words in the edition that the file follows; not
held against the page that ships); they are not all of the page's conditions on a shape. The fifth
clause follows R2.4 and R7.4 at a third edition and was compared with the page at that edition in
the same way. By a comparison by program, R2.1, R7.3, R7.7, R7.16 are the same in the edition
that the file follows and in that third one; not held against the page that ships.

1. What the file contains.
   `smallSh sb sh`: the bounds on a tree's shape: sh.tree < 2^16; sh.a ≤ 48 (the page's own bound
      on depths, R7.16; the reader's test on the list of positions gives x < 2^a); 1 ≤ sh.W; sh.W <
      2^24; a stored tree has the number 0 (the rule: under the numbers 173 and 174 the place for
      the tree's number in a label holds 0, which `leafOK` asks; of these two numbers the reader of
      an opening uses 174, for the leaves of a stored tree). `smallSh` can be run. The argument sb
      is not read; it stays so that no caller has to change.
   Two statements (`Run.Spec.open_dom`, `Run.Spec.fold_dom`).
   What the domain asks of the two kinds of calls, and where each condition comes from:
      A leaf (number 164, or 174 for a stored tree): h number (Fmt.leafPlace tree W s8) (2^a + x)
         start (the column's bytes, the fill, the salt), where W is the number of the column's
         words and s8 that of the salt's words. The place must be below 2^48: the tree's number
         below 2^16, W below 2^24, s8 below 2^8. 2^a + x must be below 2^63. And what lies behind a
         leaf's label must fit it (`leafOK`): W at least 1; s8 from 5 to 8; 8 W bytes, the fill,
         all zeros, 8 s8 bytes. These follow from `smallSh`, with three remarks. The domain's bound
         on the number of bytes (at most 2^32 − 144) follows: 8 W + 127 + 64 with W below 2^24. The
         salt's length is not in `smallSh`: the reader of an opening tests it itself (`saltLenOK`:
         a multiple of 8 from 40 to 64 bytes) before it hashes, and what the reader without a hash
         hands out has columns of W words and salts of that length. That the fill's bytes are zeros
         holds by the way a leaf is spelled. A start of 32 bytes is a hypothesis.
      A vertex (number 166): h 166 0 0 cfg (left ++ right). That cfg has 32 bytes is a hypothesis.
         The bytes' number, 64, is within the domain's bound: the leaves' digests and the vertices
         below are answers of h, whose answers have their length by a hypothesis on h; the given
         digests are read as 32 bytes.

2. What is checked when the file compiles. Nothing beyond the types; there are no tests (#guard)
here.

3. Theorems. Both statements are proved in Run/OpenDomProofs.lean.
   `open_dom`: for two hash functions h, h' in the identity monad that agree on the domain, h's
      answers having the right length: cfg.size = 32, start.size = 32, smallSh sb sh → readOpeningW
      h' cfg f sb sh start xs b i = readOpeningW h cfg f sb sh start xs b i.
   `fold_dom`: for the same two hash functions: smallB S b (Run/LaxDom.lean), and two readers of
      openings ops', ops that give the same on the file b, at every run's value that is none or has
      32 bytes, at the list of openings of every round of S, for all roots, positions and places →
      cutWhole h' ops' S b = cutWhole h ops S b. Run/LaxDom.lean's `lax_dom` follows from the case
      ops' = ops, at the reader that only parses. The statement is meant for readers that hash,
      such as the reader that fills in whole paths.

4. What is not claimed.
   The strict reader of Fmt/Rules8.lean as a whole is not treated here (its fold over rounds is
   another text); it is treated in Run/StrictDom.lean.
   It is not claimed that the bounds are needed.
   Nothing is said on what these readers compute.

Terms: lean/GLOSSARY.md.
-/
import Run.LaxDom
import Fmt.Rules7

set_option autoImplicit false

namespace Run
open _root_.Fmt (hDom dlen)

/-- The bounds on a tree's shape that the hash's domain asks; the head, 1, tells where each clause
comes from. The first argument is not read. -/
def smallSh (_sb : Nat) (sh : _root_.Fmt.Shape) : Bool :=
  decide (sh.tree < 2 ^ 16) && decide (sh.a ≤ 48) && decide (1 ≤ sh.W) &&
    decide (sh.W < 2 ^ 24) && (!sh.stored || sh.tree == 0)

namespace Spec

/-- States: if h' and h agree on the domain, the answers of h have `dlen n` bytes, cfg and start
have 32 bytes and `smallSh sb sh = true`, then `Fmt.readOpeningW` (an opening, read and hashed)
gives the same at h' and at h. What is not claimed: the head, 4. -/
def open_dom : Prop :=
  ∀ (h h' : HId), (∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b) →
    (∀ n t i s b, ByteArray.size (h n t i s b) = dlen n) →
    ∀ (cfg : ByteArray) (f : _root_.Fmt.Fld) (sb : Nat) (sh : _root_.Fmt.Shape) (start : ByteArray)
        (xs : List Nat) (b : ByteArray) (i : Nat),
      cfg.size = 32 → start.size = 32 → smallSh sb sh = true →
      _root_.Fmt.readOpeningW (m := Id) h' cfg f sb sh start xs b i =
        _root_.Fmt.readOpeningW (m := Id) h cfg f sb sh start xs b i

/-- States, of the lenient fold with two readers of openings: if h' and h are as in `open_dom`,
`smallB S b = true`, and ops' and ops give the same on b at the arguments that the statement names,
then `cutWhole` gives the same at h', ops' and at h, ops. What is not claimed: the head, 4. -/
def fold_dom : Prop :=
  ∀ (h h' : HId), (∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b) →
    (∀ n t i s b, ByteArray.size (h n t i s b) = dlen n) →
    ∀ (ops' ops : ByteArray → OpsW Id) (S : _root_.Fmt.Spec) (b : ByteArray), smallB S b = true →
      (∀ run : Option ByteArray, (∀ x, run = some x → x.size = 32) →
        ∀ r ∈ S.rounds,
          ∀ roots poss j, ops' b run roots poss r.opens j = ops b run roots poss r.opens j) →
      cutWhole (m := Id) h' ops' S b = cutWhole (m := Id) h ops S b

end Spec
end Run
