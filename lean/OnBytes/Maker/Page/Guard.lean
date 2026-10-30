-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Guard.lean: a way to run an oracle algorithm under a function on byte strings
that stops, with no result, at the first query which a test rejects; and one such test.
GuardVerify.lean puts the compiled verifier under it.

States. Definitions only. `detG ok g` runs an oracle algorithm under the oracle functions g, with
every random sample set to 0, and returns no value as soon as a query fails the test `ok`. `okJ P`
is the test "the table `P` (a `PageJ`) writes a byte string for this query" (a query to `ann`, whose
answer type has one value, passes without one). `runGuard P O` is `detG` at `okJ P` and `gJ P O`,
the oracle functions that hash `P`'s strings with O. Why: `gJ P O` answers a query without a string
by 256 zero bits, and a prover's data can reach one (a wrong length of the field `rsalt`).
Under. No hypotheses: the file has no theorem.
Does not show.
  1. A value for a run that queries an oracle `fbw`: `okJ` rejects every such query.
  2. A string for every block at the first query of a hash chain: only the last block needs one; the
     K blocks before it get zeros where neither `seeds` nor `link` writes: always under the proof
     file's tag (`.onl`).
  3. That the verifier reads none of these K blocks: whether it does depends on the map from answers
     to verifier messages (`ProtocolQueryLayout`), which this file does not fix.
  4. Anything about O: it is any function on byte strings.
  5. That a query which passes is well formed: the coding is one to one on well-formed queries alone
     (nonces n and n + 2 ^ 64 share a string; so do the first queries of two records of a request).
  6. A run to which the theorems about the soundness theorem's encodings apply: such a run must also
     reject ill-formed queries; GuardFit.lean takes a second test for that as a parameter.
  7. Any theorem: the theorems are in GuardLaws.lean.
  8. That all queries of an honest file have strings.
  9. That the strings are those that the programs hash.
 10. That a string holds everything that its query holds (`Frame.lean`'s notes name what it omits).
 11. Anything on soundness.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.Page.Frame

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

/-- **The run that refuses at the first query which `ok` turns away.** -/
def detG {S : OSpec} {α : Type} (ok : ∀ o : S.ι, S.Dom o → Bool) (g : Fam S) :
    OComp S α → Option α
  | .pure a => some a
  | .query o q k => if ok o q then detG ok g (k (g o q)) else none
  | .sample _ k => detG ok g (k 0)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- A chain's first call: the head f1, f3 or f4. -/
def tailOnly {t : Tag} (q : FbIn 256 L t) : Bool :=
  match q.head with
  | .f1 _ _ _ => true
  | .f3 _ _ => true
  | .f4 _ _ => true
  | .f2 _ _ => false
  | .f5 _ => false

/-- **The page writes a string for the query.** -/
def okJ (P : PageJ L K) : (o : OracleName) → domOf 256 L o → Bool
  | .leaf, q => (codeJ P .leaf q (0 : Fin 1)).isSome
  | .node, q => (codeJ P .node q (0 : Fin 1)).isSome
  | .rleaf, q => (codeJ P .rleaf q (0 : Fin 1)).isSome
  | .rnode, q => (codeJ P .rnode q (0 : Fin 1)).isSome
  | .fb t, q =>
    (codeJ P (.fb t) q (Fin.last K)).isSome &&
      (tailOnly (t := t) q ||
        (List.finRange K).all fun k => (codeJ P (.fb t) q k.castSucc).isSome)
  | .fbw _ _, _ => false
  | .g t, q => (codeJ P (.g t) q (0 : Fin 1)).isSome
  | .ann, _ => true
  | .other, q => (codeJ P .other q (0 : Fin 1)).isSome

/-- The run under the page's family that refuses at a query which `okJ` turns away. -/
def runGuard {α : Type} (P : PageJ L K) (O : ByteArray → ByteArray) :
    OComp (typedOracleFamily 256 K L) α → Option α :=
  detG (S := typedOracleFamily 256 K L) (okJ P) (gJ P O)

end OnBytes.Maker.Page

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Maker/Page/Guard.lean: a run of an oracle algorithm that refuses at the first query which a
test turns away, and the test "the page writes a string for this query". Definitions alone.

Why. `gJ P O` (OnBytes/Maker/Page/Frame.lean) answers a typed query that has no string by 256
zeros, whatever the query holds. A prover's string can reach such a query: the input of the request
tree's leaf is the slot value with the field `rsalt` behind it, `rleafCall` writes a string at one
length alone, and the compiled verifier tests the length of `rsalt` nowhere once the chain has
joined (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, `reqCheck`, `proofHasStrictFormat`). At another length the
leaf's digest is a constant, which does not hang on the slot value. So a verdict by
`(verifyOneProtocol ..).det (gJ P O)` is no verdict to lean on. Here a query that `okJ` turns away ends the
run with no value, and no value is a no: a query of which a block lacks a string; at a chain's first
call: of which the tail's block lacks one.

Main definitions.
  `detG ok g`: the run under the oracle functions g in which every sample is 0 (`Rom.OComp.det`,
    Rom/Cache.lean), but with no value from the first query on that `ok` turns away. It is the
    library's test `Rom.OComp.askedOK` (Run/DetAlong.lean) and `det` in one pass
    (`detG_eq_asked`, OnBytes/Maker/Page/GuardLaws.lean).
  `tailOnly`: a chain query with the head f1, f3 or f4: a chain's first call. The page writes a
    string for the tail's block of its answer alone.
  `okJ P`: the page writes a string for the query: for every block of its answer; at a chain's
    first call for the tail's block. The oracle `ann` has one answer by its type: passed. The
    oracles `fbw`: turned away.
  `runGuard P O`: `detG` at `okJ P` and `gJ P O`.
OnBytes/Maker/Page/GuardVerify.lean lays the compiled verifier of a slot under it.

To be minded. At a chain's first call the K blocks in front of the tail's are still answered by
zeros, at every wire, where no taken spelling (`seeds`, `link`) writes them: so always under the
proof file's tag. In a file of three joined chains these calls belong to the three silent rounds,
whose verifier's message has one value (`plainRound`, Compile/Joined/Types.lean) and whose wire
makes it of no block (`wireSilent`, OnBytes/Maker/Wire.lean). That the verifier reads none of these
blocks is shown nowhere here; at another wire it may. O is a letter: any function on strings.

THE LIMIT OF THIS TEST. `okJ` asks that a string is written, not that the query fits. The byte
coding of typed queries is one to one only on the set of queries that fit the encodings' own tests
(OnBytes/K/Arm/FileInj.lean, `fitFb`, `fitG`; OnBytes/Maker/Page/FitAt.lean,
`fitRow`): a round's nonce n and n + 2 ^ 64 spell one string, and across
calls two records with one request spell one first query. So a run that is to stand where the
statements on these encodings stand must refuse where an asked query does not fit, not only where
`okJ` turns it away:
OnBytes/Maker/Page/GuardFit.lean takes such a test as a letter.

What is not claimed. No law is stated here (OnBytes/Maker/Page/GuardLaws.lean). That an honest
file's queries all have strings. That the strings are those that the programs hash. That a string
holds all that its query holds (the head of OnBytes/Maker/Page/Frame.lean names what a call does not
read). Nothing on soundness.


-/
