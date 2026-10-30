-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/Bits.lean: the goals of Ladder.lean on soundness and binding with a security level.
Definitions only: no proof is in this file. `D`, the verifier, the argument system, the scope and
the claims are those of Ladder.lean; what is new is the error, and a bound on the verifier's own
queries. Ladder.lean names this file and its four goals: their names, and that they are the same
four with a security level, are fixed by that.

IN PLAIN WORDS. An adversary that asks the hash function t times gets a false claim accepted, in one
call of the verifier behind a parser that asks it n times, with probability at most about
(t + n + 2^23) / 2^124. That is 124 BITS FOR EACH QUERY, NOT 128: about 2^-60 at 2^64 queries, and
never below about 2^-101. THE 128 IS THE BAR ON EACH ROUND: for these goals to follow by the road
below, every round's error has to be at most about 2.57 / 2^128. The four bits between go to the
compiler's own bound, which charges a query five times a round's error, and to its square term. WORK
IS COUNTED: a try at a proof of work is a query like any other, and a round whose error is small
only with its work has to hold that work. There is one level here: no goal speaks of an error with
the work not counted.

The goals.
  G7bits     Soundness at exact match at the error function `soundnessErrorInQueries`.
  G7'bits    The same whatever function stands in the second hash function's place.
  G8bits     Soundness under the policy, at `D`'s extractor, at `soundnessErrorInQueries`.
  G9bits     The commitment binds to the weights that the extractor gives, at `bindingErrorInQueries`.
Both errors are 16 / 2^128 for each query, and about 2^-101 at no query.

What each is worth alone. What Ladder.lean's head says of `G7`, `G7'`, `G8` and `G9` in its points
2, 3, 6 to 10, 12, 13 and 14 holds of these four too. Its points 4, 5 and 11 read here:
1. These goals have no budget for the adversary. A protocol that checks nothing but a proof of work
   of 124 bits meets all four; `G3'pol` alone, with its budget for the honest side, rules it out, at
   the two named sets of files alone (14 (e) there).
2. A gate that is open at a share of the hash functions above the error fails these goals. A gate at
   a smaller share can still meet them: thirteen bytes of a digest are enough, since 2^-104 < `soundnessErrorInQueries
   0 0`.
3. Whether the protocol checks enough is tested by `G7bits`, `G7'bits` and `G8bits` alone: at a
   drawn hash function and fixed files, a protocol that checks too little cannot be sound at `soundnessErrorInQueries`.

Units. t and n in `soundnessErrorInQueries` count queries to the hash function, one query counting as one. `verifierQueryAllowance`
stands for the verifier's own queries, of which those of `innerCompiledVerifier` are counted as the compiler
counts them: in typed queries (`VerifierWithin`). A typed query costs one query to the hash function
for each digest of its answer, and how many digests an answer has is `D`'s choice. So the sum t + n
+ `verifierQueryAllowance` adds unlike things; it is an upper bound of the number of queries that the compiler's
own bound counts (and charges five times), and no goal bounds the number of strings that the
verifier hashes. `honestBudget` (Ladder.lean) counts queries to the hash function and `verifierQueryAllowance`
mostly typed ones: the two numbers cannot be compared.

The road that the numbers are chosen for: the compiler's own bound (`compiledSoundnessError`,
Johnson/Top/InnerCompiledVerifier.lean), carried over the two public readings without loss. It leaves duties to
a proof of the proof file's soundness for a `D`.
a. At the proof file a shared round's error has to bound the event that some request of the batch
   turns (`JointLaw`, Iop/Batch.lean); a request's own round is counted for that request alone. The
   library has two ways to a bound for a shared round: from each request's own law, at the cost of a
   factor N, the number of requests of a batch (`jointLaw_of_verLaw`, Iop/BatchSound.lean); and from
   the union of the requests' sets of bad messages (`jointLaw_of_jWithin`, Blocks/Batch/Kit.lean),
   which costs nothing where these sets are one set. They are one set where they are functions of a
   key and the requests share that key (`SameKey`, `knowB_of_key`, Ior/BatchSeq.lean;
   `knowB_peek_key`, Cb/Ld/LdLinBProofs.lean). The numbers can be reached, if at all, by the second
   way alone, with N paid at the one round at which the requests' claims meet (`errPtB`,
   Cb/Ld/LdLinB.lean). This file does not say that the rounds of a `D` meet that way's premises (see
   also the head of Johnson/Flat/TwoSizes.lean).
b. The goals speak of one proof. For several proofs under one commitment, "some proof is wrong and
   accepted" has the same error at t plus, for each proof, the verifier's queries
   (`SoundForWith.manyProofs`, VerifiableInference/ManyProofs.lean). That theorem takes a bound on
   the verifier's queries to the hash function, which no goal here gives (Units).

The numbers are choices of this project. No theorem yields them.
-/
import Ladder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat
open scoped ENNReal

/-! ## 1. The numbers -/

/-- The factor in `soundnessErrorInQueries`. -/
def errorFactorPerQuery : ℕ := 16

/-- What `soundnessErrorInQueries` adds to the adversary's and the parser's queries: the allowance for the verifier's
own (see `VerifierWithin` for what is counted, and in which unit). The number is a choice; apart
from `VerifierWithin` no statement says that it is enough. `finalSound`, a theorem, has it in its
error and takes no premise on it. In `bindingErrorInQueries`, where no verifier runs, it is slack. -/
def verifierQueryAllowance : ℕ := 2 ^ 23

/-- The soundness error, where t bounds the adversary's queries and n the
parser's: with T = t + n + `verifierQueryAllowance` it is `errorFactorPerQuery` · T / 2^128 + (T + 2)² / 2^256. That is 16
/ 2^128, or 124 bits, for each query, and about 2^-101 at t = n = 0. -/
def soundnessErrorInQueries (t n : ℕ) : ℝ≥0∞ :=
  ((errorFactorPerQuery * (t + n + verifierQueryAllowance) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
    (((t + n + verifierQueryAllowance + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- The binding error, where t bounds the committer's and the opener's queries together:
`errorFactorPerQuery` · (t + `verifierQueryAllowance`) / 2^128 + (t + `honestBudget` + `verifierQueryAllowance` + 2)² / 2^256. That is
about 2^-101 at t = 0. The experiment of `SoundAndBinding`'s second clause runs the honest committer
once more, and these queries are not the adversary's; `honestBudget` stands for them in the square
term. The harm that such a run can do is that one of its answers equals another answer, or a value
that the adversary wrote. A bound by such events alone has the form 3 · (t + 2 q + 2)² / 2^256,
where q bounds one run of the committer. Wherever this error is below 1, that bound lies below it
thanks to the linear term, not to the square term: without the linear term the square term would
have to take that form. The linear term may also have to pay for events that a committer can search
for, such as a collision at a seed. -/
def bindingErrorInQueries (t : ℕ) : ℝ≥0∞ :=
  ((errorFactorPerQuery * (t + verifierQueryAllowance) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
    (((t + honestBudget + verifierQueryAllowance + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-! ## 2. The verifier's own queries -/

/-- At all public files in scope the queries of `D`'s own verifier, its parser's among them, are at
most `verifierQueryAllowance`. Counted as queries to the hash function: the one of `readConfig`, those of
`readMore`, those of `D`'s own parser, and the one that `innerCompiledVerifier` asks at the code of the key
(`verifyDigestKey`, ZKCP/DigestKey.lean). Counted as the compiler counts them, in typed queries: all
others of `innerCompiledVerifier`. They are those of the compiled verifier `verifyAtKeyRoot`, which `tVC` of the wire in
`D`'s input (Johnson/TypedOracleCompiler/RecCompile/Cms.lean) bounds at every key, instance and proof
(`detBound_VRA`, Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean). The bound is asked at every digest c and
every value m, whether a run gives them or not. The compiler's own bound counts `tVC` + 1 queries
for the verifier (`compiledSoundnessError`, Johnson/Top/InnerCompiledVerifier.lean). The goals on soundness at
`soundnessErrorInQueries` ask this too: t in `soundnessErrorInQueries` counts none of these queries, and n only a parser's. With it the
error of `D`'s own verifier is at most `soundnessErrorInQueries t verifierQueryAllowance`: about 2^-100 at t = 0. (`SoundAt` alone
would allow that parser `honestBudget` queries: about 2^-76.) -/
def VerifierWithin (D : Description) : Prop :=
  ∀ Z : PublicFiles, InScope Z = true →
    ∃ qMore qParse : ℕ, (∀ c, (D.readMore Z c).toRandomized.QueryBound qMore) ∧
      Parser.Within (D.parse Z) qParse ∧
      ∀ c m, 2 + qMore + qParse + TypedOracleCompiler.Compile.Batch.Cms.tVC (D.input Z c m).queryLayout ≤ verifierQueryAllowance

/-! ## 3. The goals -/

/-- **G7bits. Soundness at exact match at the error "soundnessErrorInQueries".** It bounds the error of one whole call
of the verifier, and the verifier's own queries (`VerifierWithin`). The public files are fixed
before the hash function is drawn: a provider that picks or grinds them with the hash function in
hand is not covered; nor is a `D` ruled out that branches on a value of the real hash function (the
head of Ladder.lean, 12 and 10). This file does not say how the bound follows from the protocol's
rounds, nor that it can be reached at the stored security settings. Were it out of reach there,
`errorFactorPerQuery`, `verifierQueryAllowance` or the stored parameter file would have to change, and all three are fixed
text of these goals.
The numbers are chosen for one road (the head of this file): the compiler's own bound
(`compiledSoundnessError`, Johnson/Top/InnerCompiledVerifier.lean), carried over the two public readings without
loss. That bound is stated at an input that is fixed before the hash function is drawn; bounds that
go file by file have larger constants. In it each query costs five times a number εs, which has to
bound every round's error and the seeds' law. A shared round of the key file or the entry file
counts once for each leaf of that call's request tree. No factor is typed at the proof file: there a
shared round's error has to bound the event that some request of the batch turns (`JointLaw`,
Iop/Batch.lean), which is a duty of whoever shows that file's soundness; a request's own round is
counted for that request alone. For `soundnessErrorInQueries` to follow, εs has to be at most about 2.57 / 2^128: the
bar binds where t + n is near 2^124, through the square term, whose coefficient is 50 in the
compiler's bound and 1 in `soundnessErrorInQueries`; the error of the commitment's code has to come out of the same
room. No field of the compiler's input names bits of proof of work: where a round's error is small
only with its work counted, the round itself has to hold that work (nonce and test). `G8bits` gives
`G7bits` (`g7bits_of_g8bits`, Ladder/BitsTies.lean). -/
def G7bits (D : SecondHashFunctionType → Description) : Prop :=
  VerifierWithin (atSecondHashFunction D) ∧ SoundAt (atSecondHashFunction D) soundnessErrorInQueries

/-- **G7'bits. Soundness at exact match at the error "soundnessErrorInQueries", whatever function stands in the second
hash function's place.** See `G7'` and `G7bits`: the four limits of `G7'` hold likewise, and
`VerifierWithin` is asked at every function too. The public files are fixed before the hash function
is drawn: a provider that picks or grinds them with the hash function in hand is not covered; nor is
a `D` ruled out that branches on a value of the real hash function (the head of Ladder.lean, 12 and
10). -/
def G7'bits (D : SecondHashFunctionType → Description) : Prop :=
  ∀ o : SecondHashFunctionType, VerifierWithin (D o) ∧ SoundAt (D o) soundnessErrorInQueries

/-- **G8bits. Soundness under the files' acceptance policy, at D's extractor, at the error "soundnessErrorInQueries".**
See `G8` and `G7bits`. The public files are fixed before the hash function is drawn: a provider that
picks or grinds them with the hash function in hand is not covered; nor is a `D` ruled out that
branches on a value of the real hash function (the head of Ladder.lean, 12 and 10). -/
def G8bits (D : SecondHashFunctionType → Description) : Prop :=
  VerifierWithin (atSecondHashFunction D) ∧ SoundUnderPolicyAt (atSecondHashFunction D) soundnessErrorInQueries

/-- **G9bits. The commitment binds to what D's extractor gives, at the error "bindingErrorInQueries".** No
parser and no verifier run here. `honestBudget` stands for the queries of the committer's one
further run, which `BindsAt` asks to stay within it at all files in scope. The public files are
fixed before the hash function is drawn: a provider that picks or grinds them with the hash function
in hand is not covered; nor is a `D` ruled out that branches on a value of the real hash function
(the head of Ladder.lean, 12 and 10). -/
def G9bits (D : SecondHashFunctionType → Description) : Prop := BindsAt (atSecondHashFunction D) bindingErrorInQueries

end VerifierAndGoals
