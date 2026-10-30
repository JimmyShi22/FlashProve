-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Zeta.lean: THE ERROR ζ(t, n) of the statement of index privacy for the scheme with
the whole key published (Johnson/WholeKey/Statement.lean), WRITTEN OUT. t: the adversary's queries
to all typed oracles together. n: the requests. One function for all t and n.

General definitions. This file states no goal of the release, and it proves nothing. No number is
evaluated here: whether ζ is small at given letters is not said.

ζ t n = TAIL + PARTS + STOPS + SEEDS + HASH, with M + 1 the number of copies.
  TAIL = (M + 1) · Pr[Bin(n, 1/(M + 1)) > s1]   (Prob.pOver, Prob/Tail.lean, an exact finite sum)
       The prover has no state and draws its copy at random. Beyond s1 sessions on one copy that
       copy's budget of reads is overrun, and the encoding is no longer known to hide the index. The
       simulator counts and stops a copy there; so the term stands once.
  PARTS = zT + (M + 1) · zL + n · zO
       The errors of the simulators of the interactive protocols, outside the stops: one proof on
       the first table, M + 1 link proofs, n sessions (Sims.Good, Johnson/WholeKey/Premises.lean).
  STOPS = hT + (M + 1) · hL + n · hO
       The measure of that part of the honest side's abort sets which may hang on the private input,
       so on the index (StopsSmall, same file). Whether a run stops there can tell something of the
       index; a simulator cannot know that part. A TERM OF ITS OWN, not folded into PARTS.
  SEEDS = (M + 2) · δ
       Each of the M + 2 tables has a seed; δ bounds the chance that a seed made from uniform
       digests lies outside the public set Gs at whose seeds the premises on hiding are asked. Where
       Gs is all seeds, δ = 0 serves.
  HASH = Rom.costTotal e m ℓ os t   (Rom/SpecHopCost.lean)
     = t · max over o in os of m o / 2^(ℓ o)  +  sum over o in os of m o · (e o + m o) / 2^(ℓ o)
       The price of answering the honest side's hash queries that hold a secret string (a salt, a
       chain value, a slot's value) without a look at the oracle's table. NO FREE LETTER: e, m, ℓ
       and os are written below.
         m o (mW)  how many such queries the honest side asks at the oracle o, in one run of the
           committer and n sessions: ALL leaves of ALL trees of all tables and all runs; one
           Fiat-Shamir query for each round of each run; EVERY FURTHER TRY OF EVERY SEARCH, UP TO
           ITS CAP, a letter; g, the request tree's leaf and its nodes for each run.
           A search's try number j + 2 is counted at the name fbw t j, an oracle name of the
           analysis that no algorithm of the scheme asks (OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean):
           two tries of one search differ in the nonce, so they never meet.
         e o (eW)  how many queries without a secret the honest side asks at o: the seeds' two
           queries for each of the M + 2 tables, at the seeds' Fiat-Shamir oracle. (eW also writes
           the number of the inner nodes of all trees, at the oracle of inner nodes. THAT NUMBER
           ENTERS NO TERM: m is 0 there, and that oracle is not among os.)
         ℓ o (bitsW)  the secret bits: at a leaf THE FREE BITS OF ITS SALT ALONE, not the salt's
           length; at a Fiat-Shamir query min(the first salt's length, the digests' length); else
           the digests' length. THE NUMBER ℓr of free bits of the string behind a slot's value
           (CoinNums) STANDS IN NO TERM: at the request tree's leaf the secret that is counted is
           the slot's value, a digest.
         os (osW)  the oracle names at which m can be other than 0.

What ζ does not have. No term for a search that runs out: that is a value of the key or of a proof,
which the simulator is built to make with the real law. No term for the law of a seed beyond SEEDS.
No term for a query of the adversary before the key is out: the experiment has none.

Main names (namespace OnBytes.WholeKey): runLeaves, roundHasTest, nLater, maxCap; allLeaves, mW, eW,
bitsW, laterNames, osW; zetaW.

Limits. A bound that is 1 or more makes a statement of index privacy trivially true: a bar on ζ at
named letters is owed by whoever uses it. ζ is void near n = (M + 1) · s1. The counts are upper
bounds by a reading of the programs' texts; that the programs keep them is part of what a proof of
the statement owes.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Premises
import Rom.SpecHopCost
import Prob.Tail

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

variable {I X : Type} {lam : ℕ}

/-! ## Counts of one compiled run -/

section Run
variable {K : ℕ}

/-- The leaves of all trees of a run. -/
def runLeaves : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) =>
      (w.depth0.map fun d => 2 ^ d).sum + (w.depthJ.map fun d => 2 ^ d).sum + runLeaves s A W

/-- Has the round's Fiat-Shamir query a test? -/
def roundHasTest {r : Round} (a : RAnn r) (w : WireRB lam K r a) : Bool :=
  match a.kind with
  | .lo => w.grJ.isSome
  | .sh => w.gr0.isSome

/-- The rounds whose search may make a try number j + 2. i: the number of the first of the rounds s.
-/
def nLater : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | [], _, _, _, _, _ => 0
  | _ :: s, (a, A), (w, W), cap, i, j =>
      (if roundHasTest a w = true ∧ j + 1 ≤ cap i then 1 else 0) + nLater s A W cap (i + 1) j

/-- The largest cap of a round with a test. -/
def maxCap : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → ℕ
  | [], _, _, _, _ => 0
  | _ :: s, (a, A), (w, W), cap, i =>
      max (if roundHasTest a w = true then cap i else 0) (maxCap s A W cap (i + 1))

end Run

/-! ## Counts of the committer's run and n sessions -/

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (p : Params)
  (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) (u : NumsW)

/-- All leaves: of the M + 2 tables, of the proof on the first table, of the M + 1 link proofs, of n
sessions. -/
def allLeaves (n : ℕ) : ℕ :=
  (a.M + 2) * 2 ^ W.depth + runLeaves L.offline.shape aT (wTC W).sh +
    (a.M + 1) * runLeaves L.link.shape aL (wLC W).sh +
    n * runLeaves L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh

/-- The honest side's queries that hold a secret string, oracle by oracle. -/
def mW (n : ℕ) : ON₂ → ℕ
  | .leaf => allLeaves W a n
  | .fb .test => L.offline.shape.length
  | .fb .link => (a.M + 1) * L.link.shape.length
  | .fb .onl => n * L.onlineBatch.loc.shape.length
  | .fbw .test j => nLater L.offline.shape aT (wTC W).sh a.capT 0 j
  | .fbw .link j => (a.M + 1) * nLater L.link.shape aL (wLC W).sh a.capL 0 j
  | .fbw .onl j => n * nLater L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh a.capB 0 j
  | .g .test => 1
  | .g .link => a.M + 1
  | .g .onl => n
  | .rleaf => 1 + (a.M + 1) + n
  | .rnode => W.depthReqT + (a.M + 1) * W.depthReqL + n * W.depthReq
  | _ => 0

/-- The honest side's queries without a secret, oracle by oracle: the seeds' two queries for each
table; the inner nodes of all trees (fewer than there are leaves). -/
def eW (n : ℕ) : ON₂ → ℕ
  | .node => allLeaves W a n
  | .fb t => if t = S.t then 2 * (a.M + 2) else 0
  | _ => 0

/-- The secret bits of a query, oracle by oracle. -/
def bitsW : ON₂ → ℕ
  | .leaf => c.ℓ
  | .fb _ => min p.sFS lam
  | .fbw _ _ => min p.sFS lam
  | _ => lam

/-- The names of the tries number 2, .., k + 1 of the searches of the protocol with the tag t. -/
def laterNames (t : Tag) (k : ℕ) : Finset ON₂ :=
  (Finset.range k).image fun j => TypedOracleCompiler.Compile.Batch.OracleName.fbw t j

/-- The oracle names at which the honest side asks a query that holds a secret string. -/
def osW : Finset ON₂ :=
  ({.leaf, .rleaf, .rnode, .g .test, .g .link, .g .onl, .fb .test, .fb .link, .fb .onl} :
      Finset ON₂) ∪
    laterNames .test (maxCap L.offline.shape aT (wTC W).sh a.capT 0) ∪
    laterNames .link (maxCap L.link.shape aL (wLC W).sh a.capL 0) ∪
    laterNames .onl (maxCap L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh a.capB 0)

/-- **THE ERROR.** -/
def zetaW : ℕ → ℕ → ℝ≥0∞ := fun t n =>
  Prob.pOver (a.M + 1) u.s1 n +
    (u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
    (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
    ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ +
    Rom.costTotal (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (eW W S a n) (mW W a n)
      (bitsW (lam := lam) p c) (osW W a) t

end OnBytes.WholeKey
