-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GuardFast.lean: the test `okJ` of Guard.lean ("the table `P` writes a byte string
for this query") written a second time, as explicit conditions, so that a program builds no string
for the test where `P`'s own rules decide.

States. Definitions only. `okJF P` tests a query's oracle, head, round and block (in the request
tree: its length) where `P`'s own rules would write, and evaluates `P`'s five supplied functions
besides (under the key file's tag `seeds` first). `fbTailF F q` is its part for the last block of a
hash-chain query. `runGuardF P O` is `detG` at `okJF P` and `gJ P O`. Why: compiled Lean is strict,
so `okJ` would build every block's string only to see that there is one.
Under. No hypotheses: the file has no theorem.
Does not show.
  1. A saving at the five fields of `P` supplied as functions (`leaf`, `leafX`, `link`, `seeds`,
     `other`): they are evaluated as in `okJ`, under the tag `.link` at all K + 1 blocks.
  2. That a run under `runGuardF` ends in practical time: its oracle functions are `gJ P O`,
     unchanged.
  3. What evaluating one of the five fields costs: that depends on the functions that are given
     there (`leafOf`, Trees.lean, builds the call's bytes).
  4. Any theorem: that `okJF` is `okJ` (`okJF_eq`) and `runGuardF` is `runGuard` (`runGuardF_eq`) is
     proved in GuardFastLaws.lean.
  5. How long a run takes.
  6. Whatever the notes of Guard.lean list as not shown.
  7. Anything on soundness.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.Page.Guard

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- **The file's rows have a call for the tail's block of the answer to a chain query.** The
conditions of `fbCallJ`, head by head, at the last block. -/
def fbTailF {t : Tag} (F : FileJ L t) (q : FbIn 256 L t) : Bool :=
  match q.head with
  | .f1 _ _ _ => decide (q.round = 0)
  | .f2 none _ =>
    decide (1 ≤ q.round ∧ q.round ≤ F.n₁) ||
      decide (F.J3 + 1 ≤ q.round ∧ q.round ≤ F.J3 + F.n₃)
  | .f2 (some _) _ => false
  | .f4 _ _ => decide (q.round = F.J)
  | .f5 _ => decide (F.J + 1 ≤ q.round ∧ q.round ≤ F.J + F.n₂)
  | .f3 _ _ => decide (q.round = F.J3)

variable {K : ℕ}

/-- **The page writes a string for the query**, by conditions. -/
def okJF (P : PageJ L K) : (o : OracleName) → domOf 256 L o → Bool
  | .leaf, q => (P.leafX q).isSome || (P.leaf q).isSome
  | .node, _ => true
  | .rleaf, q => decide ((q : Bits).length = 256 + 8 * P.sR + 64)
  | .rnode, _ => true
  | .fb .test, q =>
    ((P.seeds (q, Fin.last K)).isSome || fbTailF P.key q) &&
      (tailOnly (t := .test) q || fbTailF P.key q ||
        (List.finRange K).all fun k => (P.seeds (q, k.castSucc)).isSome)
  | .fb .onl, q => fbTailF P.proof q
  | .fb .link, q =>
    (P.link (q, Fin.last K)).isSome &&
      (tailOnly (t := .link) q ||
        (List.finRange K).all fun k => (P.link (q, k.castSucc)).isSome)
  | .fbw _ _, _ => false
  | .g .test, q => decide ((q : JoiningRoundQuery 256 L .test).round = P.key.J)
  | .g .onl, q => decide ((q : JoiningRoundQuery 256 L .onl).round = P.proof.J)
  | .g .link, _ => false
  | .ann, _ => true
  | .other, q => (P.other q).isSome

/-- The run under the page's family that refuses at a query which `okJF` turns away: `runGuard` with
the test by conditions. -/
def runGuardF {α : Type} (P : PageJ L K) (O : ByteArray → ByteArray) :
    OComp (typedOracleFamily 256 K L) α → Option α :=
  detG (S := typedOracleFamily 256 K L) (okJF P) (gJ P O)

end OnBytes.Maker.Page

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Maker/Page/GuardFast.lean: the test "the page writes a string for this query" (`okJ`,
OnBytes/Maker/Page/Guard.lean), said once more by the conditions under which the page's rows write,
so that a run that makes the test builds no string for it at the page's own rows (chain queries
under the proof file's and the key file's tag, the slot value, the request tree, vertices). The five
given fields are asked as in `okJ`: under the link's tag at all K + 1 blocks. Definitions alone.

Why. `okJ P` asks whether `codeJ P` has a value, at every block of a chain query's answer. Compiled
Lean is strict: it would build each block's call and string, only to see that there is one. The rows
of the page (`fbCallJ`, `gCallJ`, `rleafCall`, OnBytes/Maker/Page/Frame.lean) write or do not write
by a condition on the query's head, its round, the block and, at a leaf of the request tree, the
length. These conditions are written here again.

Main definitions.
  `fbTailF F q`: the file's rows have a call for the tail's block of the answer to the chain
    query q.
  `okJF P`: the test.
    Vertices of both kinds of tree: passed, as these two rows always write.
    A leaf of the request tree: the one length.
    A query for the slot value: the joining round; under the link's tag: turned away.
    A chain query under the proof file's tag: `fbTailF`.
    A chain query under the key file's tag: the spelling `seeds` goes first, as in `codeJ`. At a
      query that the key file's own rows write, the spelling is asked at the tail's block alone.
    A chain query under the link's tag, a leaf, a string of the spare oracle: these are fields of
      the page, so they are asked whether they have a value, as in `okJ`.
  `runGuardF P O`: `detG` (OnBytes/Maker/Page/Guard.lean) at `okJF P` and `gJ P O`: `runGuard` with
    the test by conditions. Its family is `gJ P O` unchanged: whether a run under it ends is not
    known.

To be minded. The page's fields `leaf`, `leafX`, `link`, `seeds` and `other` are functions that are
given: what asking one of them costs hangs on what is laid there. `leafOf`
(OnBytes/Maker/Page/Trees.lean) builds the call's bytes; `leafOf_isSome`
(OnBytes/Maker/Page/GuardFastLaws.lean) says by which condition it has a value.

What is not claimed. No law is stated here: that `okJF` is `okJ` is `okJF_eq`, that `runGuardF` is
`runGuard` is `runGuardF_eq` (OnBytes/Maker/Page/GuardFastLaws.lean). How long a run takes. What the
head of OnBytes/Maker/Page/Guard.lean does not claim. Nothing on soundness.


-/
