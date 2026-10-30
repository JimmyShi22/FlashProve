-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseLaxXIs.lean: the lenient reader for files that open stored tables, compared with the strict
reader. One direction only. One definition and four statements; the proofs are in
Run/ParseLaxXIsProofs.lean. Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

The strict reader (Fmt/Rules8X.lean, `wholeChainX`) is this library's rendering of the format
page's verifier up to its decision: it cuts the file, recomputes the hash chain, tests the proof of
work and checks every Merkle opening against its root. The lenient reader (Run/ParseLaxX.lean,
`laxWholeX`) only cuts the file and checks the form of its parts. To cut it, it too recomputes the
hash chain (`laxQueryW`, Run/ParseLax.lean). What the lenient reader refuses: part 1 of the head of
Run/ParseLaxX.lean. The record of vertices met lists the nodes of a tree whose values the strict
reader has met: root by root (`Fmt.Seen`, Fmt/Rules8.lean) and opening by opening (`OpenOut.seen`,
Fmt/Rules7.lean). The typing (`toBPrfX`) is the step from a reader's output to the compiled
verifier's typed argument string.

1. What the file contains.
     `stripX o`: a reader's output without its records of vertices met.
2. What is checked when the file compiles.  Only the types.
3. Statements (namespace `Run.PQ.Spec`).
     `laxX_reads`: let the description S (`Fmt.SpecX`) meet the two hypotheses below. Then, for
       every hash function h and every string b: if `Fmt.wholeChainX h S b = some o'` then
       `laxWholeX h S b = some (stripX o')`. The first hypothesis is that every opening that a round
       of S lists (`r.opens` for r in `S.base.rounds`) is of an own tree (`x.2 = .own n`; `Src`,
       Fmt/Rules8.lean). The second is that the random bytes stand in the file
       (`S.base.rand = .inFile`). Beside these two there is no hypothesis: none on the values of the
       roots and none on the hash function. Both readers are taken at the identity monad.
     `toBPrfX_strip`: `toBPrfX .. (stripX o) = toBPrfX .. o`. Of a reader's output the typed string
       takes the run value, the rounds' values (the roots sent among them) and nonces, and each
       opening's shape, list, columns, salts and given digests alone.
     `entry_lax`: for every description D (`XD`, Run/PlanQXRun.lean), decision, root and file: if
       `runEntryK D dec r0 file` is not "reader", then
       `runEntryLax D dec r0 file = runEntryK D dec r0 file`.
     `entry_half`: if `runEntryK D dec r0 file` is "accepted", so is `runEntryLax D dec r0 file`.
4. What is not claimed. The converse: that a file which the compiled verifier accepts behind the
   lenient reader is read by the strict one. So it is not claimed that the two run functions
   (`runEntryK`, `runEntryLax`) are one. What the lenient run answers where the strict reader
   refuses is not proved. (For files without stored tables the like of the converse is `pi_strict2`,
   stated in Run/PageIs.lean and proved in Run/PageIsStrict2.lean: what the lenient reader reads,
   with all proof-of-work tests passed (`passL`) and all openings leading to their roots
   (`rootsAll`), the strict reader reads, under the further hypotheses of its statement, among them
   that the roots that the file sends differ (`rootsDiffer`); it depends on the strict reader's
   record of vertices met.)
   No statement on soundness follows.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Sources. The pattern is Run/PageIsReaders.lean's pi_strict1, the same direction for files without
stored tables; stripR is taken from there.

Terms: lean/GLOSSARY.md.
-/
import Run.ParseLaxX
import Run.PageIsReaders

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch
open _root_.Fmt (ChainOut SpecX)

/-- a reader's output without its records of vertices met -/
def stripX (o : ChainOut) : ChainOut := ⟨o.pd, o.run, o.rho0, o.rho, [], o.rounds.map stripR⟩

namespace Spec

/-- States: what the strict reader reads, the lenient one reads, if the own openings of S (`r.opens`
for r in `S.base.rounds`) are all of own trees (`.own n`) and the random bytes are in the file. -/
def laxX_reads : Prop :=
  ∀ (h : HId) (S : SpecX) (b : ByteArray) (o' : ChainOut),
    (∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n) → S.base.rand = .inFile →
    _root_.Fmt.wholeChainX (m := Id) h S b = some o' → laxWholeX (m := Id) h S b = some (stripX o')

/-- States: the typing does not look at the vertices met. -/
def toBPrfX_strip : Prop :=
  ∀ (salt : ℕ) (cfg : ByteArray) (C : CK) (ds : List RD) (a : ℕ) (xs : List XO)
      (dec : View → Bool) (o : ChainOut),
    toBPrfX salt cfg C ds a xs dec (stripX o) = toBPrfX salt cfg C ds a xs dec o

/-- States: where the run behind the strict reader does not answer `.reader`, the two runs give one
outcome. -/
def entry_lax : Prop :=
  ∀ (D : XD) (dec : View → Bool) (r0 file : ByteArray),
    runEntryK D dec r0 file ≠ .reader → runEntryLax D dec r0 file = runEntryK D dec r0 file

def entry_half : Prop :=
  ∀ (D : XD) (dec : View → Bool) (r0 file : ByteArray),
    runEntryK D dec r0 file = .accepted → runEntryLax D dec r0 file = .accepted

end Spec
end Run.PQ
