-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecGrind.lean: the compiler theorem for records of protocols whose rounds may have
proof-of-work bits ("grinding"). Terms of the bounds and one statement (index binding). Nothing is
proved here.

Of what this header describes, this library has `grFail`, `failOf`, `cFail`, `alphaBG` and the
statement `Spec.bindingBatchG` (index binding). Not in this library: the statements on completeness
and privacy of the scheme `argB`, and its term ζ.

The scheme `argB` only (Compile/Batch/Star.lean: fresh coins in C, the entry in each proof, empty
slots hashed). The proof of index binding: Compile/Batch/BindingG.lean (`bindingBatchG`). The other
forms of the scheme have statements of their own for wire records with proof-of-work bits (`W.OKG`),
since an L with such bits has no `Props` (not proved: Iop/BatchGrind.lean, Limits): entries in the
key (the simulator: Compile/Batch/SpecPubGr.lean; the theorem: Compile/Batch/PubProgMainBGr.lean,
`mainBatchKEGrWithBOf`), no query for an empty slot (Compile/Batch/SpecUGr.lean); for seed and lazy
prover and for pruned Merkle paths, of the compiler theorem only the steps to it
(Compile/Batch/StepSGr.lean, Compile/Batch/StepL.lean, Compile/Batch/StarO.lean), which are
implications: the compiler theorems on these forms are not part of this library. (Words of this
library: lean/GLOSSARY.md.)

What a round with a test is. StarkWare, "ethSTARK Documentation", version 1.2, section 6.3: the
prover's message ends in a nonce, the verifier's message holds b further uniform bits, the test
bits, and the verifier rejects unless all of them are 0. Below the test bits are called
proof-of-work bits, one query with a nonce an attempt, and the honest prover's attempts in one round
a search. As a transformer that is Iop/BatchGrind.lean (`L.grind`). The compiler sees it through two
records in the wire record of a round (Iop/BatchWire.lean: `grJ` for the Fiat-Shamir query of a slot
in a local round, `gr0` for the shared query of a shared round).

The scheme is `argB`, for a wire record with such records. V is the compiled verifier of the scheme
without proof-of-work bits: the nonce is in the plain part, the check of the bits in the interactive
verifier of L. What differs is the honest prover (and committer): in such a round it makes the
round's Fiat-Shamir query with the nonces 0, 1, 2, .., at most more + 1 of them, and goes on with
the first answer whose proof-of-work bits are all 0; if there is none, with the last
(Compile/Batch/Prover.lean: `fbTG`). The search depends on the proof-of-work bits only and takes no
sample. A failed search gives no notice: the proof string is made all the same. (That V then rejects
it is neither assumed nor concluded here; it is so (by reading: no theorem states it) for `L.grind`,
whose verifier checks the bits.)

The statements are generic: for every record of protocols L and every wire record W with well-formed
proof-of-work records (`W.OKG`) that fit L (`GrFitB`; `Spec.bindingBatchG` does not take `GrFitB`).
They do not name `L.grind`. That at a wire record without such records they are the statements for
the scheme without proof-of-work bits is not proved in this library (those statements are not in
this library either).

Hypotheses.
  `L.PropsNoAcc`   (Iop/BatchGrind.lean) all clauses of `BatchProtocol.Props` but (Acc), under the uniform
                   distribution of the verifier randomness, proof-of-work bits included. For L =
                   L'.grind .. they hold with the numbers of L' but for εs, which is supplied:
                   soundness is a hypothesis (`Spec.grindPropsB`)
  `GrFitB`   (Compile/Batch/SpecFit.lean) (1) nothing on the honest side depends on the
             proof-of-work bits: withheld sets, the honest prover's messages, the positions read;
             (2) the positions read do not depend on nonces; (3) (Acc) where all proof-of-work bits
             are 0: outside the withheld set the verifier accepts the honest prover's messages with
             any nonces written in

Bounds.
* ε = `epsB W M` (Compile/Batch/SpecBinding.lean), the same formula as without proof-of-work bits:
  (tC + tP + tV + 1) εs + 2 (tC + tP + tV + 2)² / 2^λ, with εs = M.εs a bound on every
  round-by-round error of the compiled L, that is, of the protocol with the proof-of-work bits.
* α = `alphaBG W M` (a union bound over the slots, as for pO: a shared search, which runs once, is
  counted N times). The probability for each single search (`grFail`) is exact: its attempts are
  queries with different inputs.
* ζ (not defined in this library, nor is the ζ of the scheme without proof-of-work bits) = that ζ
  with xFbG in place of xFb: every attempt is counted, at the worst case more + 1 for each search.
  No other term changes; there is no term for failed searches (in the answer of a final attempt the
  verifier message without its proof-of-work bits and the chaining value are uniform and independent
  of the proof-of-work bits and of the number of attempts).
  The factor more + 1 in the part of ζ that is linear in t comes from the proof, not from the
  scheme. It comes from the way back from the ghost names `fbw` (Compile/Batch/SpecGhost.lean): the
  lemma on deferred programming has a budget of queries for each oracle, and at each ghost name the
  adversary's whole budget is counted. A query of the adversary names one chaining value and one
  nonce; no attack is known that gains from failed attempts.
  A form of the lemma for a total budget (t times the largest count of an oracle) removes the
  factor: it is proved (Rom/SpecDeferTotal.lean, Rom/DeferTotal.lean). Index privacy of this scheme
  with the sharper ζ (`zetaBGTot`, Compile/Batch/SpecTotalG.lean: no number of attempts in the part
  linear in t) is not proved in this library. The ζ described here is the form with a budget for
  each oracle.
  At the model, by calculations made outside Lean (tests of 20, 28, 32 bits, caps 2^27, 2^35, 2^39,
  2^64 queries): the bound stays below 2^-128 at a million batches, but the number of batches up to
  which it does falls to about a third to a half of what it is without tests (reckoned outside Lean,
  and not for the release; no theorem of this library states it of this ζ; the lengths of both
  salts, the environment's hypothesis and the other parameters of that calculation are not told
  here). No numeral of a scheme without tests may be quoted beside a scheme with tests.

What ε means. Every attempt is one of the tC + tP queries. A round without proof-of-work bits must
lie below εs by itself, and the collision term gets no factor. At a round with proof-of-work bits, b
of the bits of εs are the cheating prover's work, at one query an attempt: the interactive protocol
without them has error up to 2^b εs in that round. With lists of opened positions shortened by b
bits' worth, in the query model nothing is gained and nothing is lost in ε: the same formula, the
same numerals; what is gained is bytes. A query costs 1 whatever it is: the model never saw what a
new attempt cost before, and does not see that it now costs one hash. No number here is a security
level. More: Iop/Grind.lean, what "128 BITS" means.

The two forms of "128". In the field, "128 bits" that include "b bits of grinding" means: with that
work reckoned in, no round's error exceeds c = 2^-128. Under the clause `sound` of `L.PropsNoAcc`
(M.εs bounds every round-by-round error), M.εs ≤ c says it. That is a condition that the reader
adds: `Spec.bindingBatchG` takes no bound on M.εs. "For all tC, tP: ε ≤ (tC + tP + tV + 1) c + 2 (tC
+ tP + tV + 2)² / 2^λ" is the conclusion (not stated in this library: not for every W, c and λ at
once; for every W, at λ = 256 and one fixed c (not the c = 2^-128 above), under
the hypothesis M.εs ≤ c, as one fraction: Cm/ParBounds.lean; there a bound on tV stands for tV).


Because of tV + 1, queries divided by chance is below 1 / c for every number of queries, with tests
and without.

What is counted, and in what. All counts are in typed queries (one Fiat-Shamir query = one query,
whatever the number of hash blocks of its answer). C and P in the worst case (more + 1 attempts a
search); V as without proof-of-work bits. The statement on the queries of this scheme is not in this
library. (Of C alone: `Spec.honestKey_typed`, CompileK/HonestKeyWalk.lean; of V alone: `detBound_V`,
Compile/Batch/GlueBinding.lean.)

Notation: `tC`, `tP`: natural numbers: in `HasIndexBindingWith` (ZKCP/Gen.lean): `Ct.QueryBound tC`,
`(Pt st).QueryBound tP`; tV: `tVB W` (Compile/Batch/SpecBinding.lean): "a bound on the queries of V
on one proof: Test, Link, one slot of Batch"; N: `L.maxBatchSize`: "the number of slots" (`BatchProtocol`,
Iop/Batch.lean); b, more: fields of `GrW` (Iop/BatchWire.lean): "the number of test bits"; "the
honest prover tries the nonces 0, .., more: at most more + 1 tries"; `M`: an `LH.Nums`
(Iop/InteractiveOracleProof.lean): "All numbers of the interface"; εs, pO: its fields `M.εs`, `M.pO`; `xFb`, `xFbG`:
natural numbers (Compile/Batch/Counts.lean); λ: `lam`; `WP`: a `WireBP L` (Iop/BatchWireP.lean):
"the prover's data for the three protocols, and the enumeration of the encoding randomness"; `p`: a
`Params` (Compile/Star.lean); `Ryes`, `Rno`: of type `I → X → Prop`: arguments of `BatchProtocol.Props`
(Iop/Batch.lean).

What is not said.
* The mean number of attempts (at most 2^b a search), or a tail bound. α is exact in each search; ζ
  and the counts of queries are stated with the worst case, which overstates the honest work by the
  factor (more + 1) / 2^b (128 at more + 1 = 2^(b + 7)). No bound on the mean number of queries of
  this scheme is proved in this library.
* Counts in queries to one hash function: the steps to it read a fixed set of hash blocks of an
  answer, so a failed attempt is counted with all hash blocks of its round. (Exactly: the steps that
  are not adaptive: Rom/OverOneN.lean. Adaptive steps on the way to it: Rom/SpecCut.lean; counted
  for another form of the scheme: Compile/Batch/CutQueriesSum.lean; not claimed for `argB`:
  Compile/Batch/SpecOneCall.lean.)
* A stop at a failed search. The implementation outputs nothing if a search reaches its cap (the
  request, or in a shared round the whole batch, fails; C is run again under a fresh seed). Here the
  proof string is output; a failed search of Test or of Link leaves a key under which V rejects
  (after Test: every proof; after Link: every batch that samples that copy), and nothing signals it
  to anybody. (That V rejects: for `L.grind`, by reading: no theorem states it.) Theorems on schemes
  that stop a request at a failed search of Batch are not in this library.
* With b > 0 there are oracle functions for which every attempt fails. So "V accepts for every
  oracle", refined completeness (0, 0) and adaptive completeness 0 have no form here.
* That the nonce sent is the least that passes is a property of the honest prover; V does not check
  it, and knows no cap.
* Where the proof-of-work bits come from. Here they are part of the one typed answer that also gives
  the verifier message and the chaining value. The implementation makes a separate hash call for the
  check and, for the final nonce only, a second one for the new state (known at second hand: the
  head of Rom/SpecCut.lean). Over one hash function that is a difference still to be declared.
* isk of `argB` holds the strings of all tokens of C, the chaining values of its failed attempts
  among them. No size statement is about isk. The numbers of the tokens now depend on the path.
* In `argB` an empty slot is hashed like a full one: it runs its searches too, and is counted.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.Spec
import Compile.Batch.SpecGhost
import Compile.Batch.SpecFit
import Iop.BatchGrind

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Compile.GlueB Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## The bounds -/

/-- the probability that no attempt of a search passes: (1 - 2^-b)^(more + 1) -/
def grFail {C P : Type} (g : GrW C P) : ℝ≥0∞ := (1 - ((2 : ℝ≥0∞) ^ g.b)⁻¹) ^ (g.more + 1)

def failOf {C P : Type} : Option (GrW C P) → ℝ≥0∞
  | none => 0
  | some g => grFail g

/-- the sum, over the rounds of one slot's transcript, of the probability that the round's search
fails: the slot's own search in a local round, the shared search in a shared round -/
def cFail {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℝ≥0∞
  | [], _, _ => 0
  | _ :: s, (a, A), (w, W) =>
      (match a.kind with
        | .lo => failOf w.grJ
        | .sh => failOf w.gr0) + cFail s A W

/-- α: a batch also fails if a search of Test, of Link for the sampled copy, or of the transcript of
some slot fails. A union bound over the slots, as for pO: so a shared search is counted N times,
though it runs once -/
def alphaBG (W : QueryLayout lam L) (M : LH.Nums) : ℝ≥0∞ :=
  alphaB L M +
    (cFail L.offline.shape _ W.T.sh + cFail L.link.shape _ W.Lk.sh +
      L.maxBatchSize * cFail L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh)

variable (W : QueryLayout lam L) (p : Params)


variable {W p}

/-! ## The statement -/

/-- Under `L.PropsNoAcc`, `W.OKG`: index binding, with the extractor named: the bound of the scheme
without proof-of-work bits, at the εs of the compiled L. -/
def Spec.bindingBatchG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Prop) (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M),
    W.OKG → Gen.HasIndexBindingWith (relPair Ryes Rno h.sub) (argB W WP p) (extractorB W) (epsB W M)





end Compile.Batch
