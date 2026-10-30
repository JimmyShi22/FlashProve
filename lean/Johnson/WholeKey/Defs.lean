-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Defs.lean: A SCHEME (COMMITTER, PROVER, VERIFIER) OVER THE TYPED ORACLES WHOSE
PUBLISHED KEY HOLDS ALL THAT IS MADE ONCE, around the compiled verifier at the key (root,
out-of-domain sample) (verifyAtKeyRoot, Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean), which is called as it stands.
AT LETTERS: any object with out-of-domain samples, any wires, any strategies, any number of copies.
DEFINITIONS ALONE.

This file is a general definition. It states no goal of the release, and it proves nothing.

Words. "Out-of-domain (OOD) sample" is what other files of the library call a record: a seed, which
is read off an oracle's answers to two nested queries, the first of which holds the root of the tree
over an encoded index; and the answers at that seed.
"Table": an encoded index with its tree and its OOD sample. "First table": the one whose root the
key begins with. "Copy": a further table over the same index, tied to the first by a link proof.

Why. A typed proof for verifyAtKeyRoot (OfflineLinkOnlineProof, Johnson/TypedOracleCompiler/RecCompile/FrontRoot.lean) bears four things: the
proof on the first table (the key's test), one copy with its link proof, the copy's number, and the
session's proof. The first two read the first table. A prover without a state that made them anew
for each request would read the first table again each time, and the number of positions of one
table that may be read before it stops hiding the index is bounded. So here they are made ONCE, by
the committer. And they are PUBLISHED: they are part of the verifier's key. In the experiment of
index privacy (ZKCP/Gen.lean) the adversary's view then holds them from its first step, and a
simulator has to make them before any session.

THE FORM. A scheme of ZKCP/Gen.lean (ZKCP.Gen.Arg: typed oracles, batches), like the scheme of
Johnson/Top/InnerCompiledVerifier.lean. There the strong form of index privacy, in which the environment sees
the adversary's whole view, is ZKCP.Gen.HasIndexPrivacyWith. The steps that lead on from it are
general in the types of keys and proofs: to one hash function (privacy_overOne, Rom/ExitPriv.lean),
to the form of ZKCP/Defs.lean (strongPrivacy_of_gen, ZKCP/SpecialAny.lean), to other keys and proofs
made from these (PrivacyFor.wrap, ZKCP/PrivacyWrap.lean).

THE TYPES.
  verifier's key   FullKey (Johnson/TypedOracleCompiler/RecCompile/Cms.lean), the library's own type of the whole key:
                   the first table's root, its OOD sample, the proof on it, and the list of copies,
                   each as (root, OOD sample, link proof).
  proof            RequestProof (same file): the place of a copy in the key's list, the copy's number, the
                   session's proof.
  prover's key     Isk: the index; each copy as the honest side keeps it (TabK: the encoding's
                   randomness, the tree with its leaves' inputs and ALL ITS LEVELS, the seed).
                   THE FIRST TABLE IS NOT IN IT: that the prover never proves on the first table
                   holds by type.
A STOP OF THE HONEST SIDE IS A VALUE of the key or of the proof: "none" in the place of that proof
string, to which the verifier says no. There are two kinds of stop (shown). A search for a nonce has
run out. Or the verifier messages of the run lie in the set at which the honest side withholds its
messages (stopT, stopL, stopB): honest-verifier zero knowledge of an interactive prover
(Honest.output, Honest.HVZK, Iop/InteractiveOracleProof.lean) speaks of an output that is "none" there, and says
nothing on what the strategy's messages at such verifier messages show. The compiled prover of one
slot does not make that test; it hands back the transcript as it was hashed, so the test is made
here, behind it, before anything is handed out.

THE COINS, each named.
  the committer draws (DrawC)  the first table's encoding randomness and salts; the coins of the
      interactive strategy of the key's test, and those of its compiled run; for each copy
      (DrawCopy) its encoding randomness and salts, the coins of the link's strategy, and those of
      its compiled run.
  the prover draws (DrawP)  the place of a copy, uniform among the h.M + 1 copies; the coins of the
      session's strategy; those of its compiled run. NOTHING ELSE: no coin for what is made once.
Each kind of coin has its own enumeration, and each draw is a draw of its own: that the copies'
coins are independent of each other and of the first table's is so by the text, not by a premise.
THE ONE TIE BETWEEN A STRATEGY's COINS AND ITS COMPILED RUN's COINS IS A WRITTEN FUNCTION (dress).
Where bytes are reached, the typed salt of a leaf in a compiled run begins with a public string, the
"run value" of the hash chain that sent the leaf's tree, and the strategy sends the same run values
in plain parts. So the coins that are DRAWN for a compiled run hold the free bits alone, and the run
is HANDED these coins with the public starts laid in front: a start is made from the run values
(read off the strategy's coins: rvT, rvL, rvB), the round's number, the component and the run's
first salt. The strategy's coins and the run's coins stay two draws: that the free bits are
independent of the strategy's coins is so by the text.
ONLY WHAT IS READ IS HANDED ON. The salts of a table and the leaf salts of a compiled run are drawn
as functions on all natural numbers. A table is handed its salts at the places of its tree's leaves
alone (cutS), a compiled run the free bits within a window of rounds, trees and leaves alone
(dress): so what the honest side does and keeps is, by the text, a function of finitely many drawn
strings. The three strategies have three types of coins (Plays): that the session's strategy does
not read the coins of the key's test is so by type. The session's strategy has ONE type of coins for
all numbers of a copy; the number is an argument of the strategy and of its test for a stop.

WHEN THE SEEDS ARE ASKED. The committer builds ALL trees and asks ALL seeds first, and only then
runs the proof on the first table and the link proofs: so all that these runs are about (encoded
indices, roots, seeds) stands before the first of them begins. All tables are the committer's work,
so the two queries of every table's seed are asked before the key is out. In the experiment of index
privacy the adversary gets the key first and asks afterwards: that no query of the adversary comes
before a seed's is so by the form of the experiment. Each table has fresh encoding randomness and
one seed.

THE PARTS are the compiled prover of one slot at its three sets of letters (proveTA, proveLA,
proveBA, Johnson/Prover/YesOfProve.lean), the tree as a prover keeps it (committerTreeKeptByProver,
Johnson/Prover/CommitterTreeKeptByProver.lean) and the seed's two queries (seedsO, Johnson/Prover/All/Defs.lean), each
called with the arguments with which the prover of a whole request calls it (allY, same file) at the
strategies Plays.joint and at the draw that the committer's and the prover's coins make up
(drawOf). What differs from allY: who runs which part, and when; each tree is built once; the other
copies' runs stand in between; the tests for a stop; "none" where allY's caller lays a fixed proof.

WHERE THINGS SIT.
  The number of copies is h.M + 1, a letter of the honest side. It is NOT read off the verifier's
  parameters p (Params, Compile/Star.lean, has a field M of that meaning): the compiled verifier
  reads of p the two lengths of salts alone, and an input that is written for the verifier may hold
  any number there.
  A copy's number, which the session's strategy is handed and which the verifier tests on the
  session's plain parts (OutOfDomainSampleQueryLayout.num), is nm j at the place j of the key's list: a public letter.
  The 256-bit commitment ID is no field here: over typed oracles there is no oracle for it. It is
  the one hash function's answer at a code of (root, OOD sample), so it is a function of this key
  and the hash function; it is laid beside the key behind the step to one hash function
  (Johnson/WholeKey/AtInput.lean).

Main names (namespace OnBytes.WholeKey).
  Plays, Plays.joint   the three strategies, each with its own coins and its test for a stop; the
    strategies as one family.
  shown   what is handed out of a compiled run's outcome.
  HonestSide   the honest side's letters: strategies, caps of the searches, enumerations of coins,
    the public starts of salts.
  dress, HonestSide.dressT | dressL | dressB, cutS   the coins that a compiled run is handed, and
    the salts that a table is handed, out of those that are drawn.
  TabK, Isk    a table as it is kept; the prover's key.
  DrawCopy, DrawC, DrawP, drawOf   the coins.
  tabO, tabsO, linkO, linksO, commitAt   the committer behind its coins.
  coinsCopy, coinsCopies, coinsC, commitW   its coins; the committer.
  proveAt, coinsP, proveW   the prover behind its coins; its coins; the prover.
  lowKey, lowPrf, verifyW   from (key, proof) to verifyAtKeyRoot's key and verifyAtKeyRoot's proof; the verifier: verifyAtKeyRoot at
    these.
  argW   THE SCHEME.
  argLow   the same honest side at verifyAtKeyRoot's own types: the key is (root, OOD sample), and the prover
    copies what was made once into each proof.

Limits. Definitions alone. No law is asked here of an enumeration, a strategy or a cap: at idle
letters the scheme is a scheme that proves nothing. The salts and the compiled runs' coins are of
infinite types, of which no finite enumeration lists every member: laws on them that can be met are
in Johnson/WholeKey/CoinLaws.lean. One request a proof: a batch of two or more gets
fixed proofs that the verifier refuses. The prover has no state: it does not count how often a copy
was used. One run of the committer. Tied to no program.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Defs

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ}

/-! ## The letters of the honest side -/

/-- The three interactive strategies, as families in what the honest side knows and in the seeds,
EACH WITH COINS OF ITS OWN TYPE, and for each the test "at these verifier messages the honest side
withholds its messages". The session's are also handed the instance and the copy's number. The tests
read no coin of a strategy. -/
structure Plays (L : HolographicProtocol I X) (KT KL KB : Type) where
  /-- the key's test, on the first table -/
  T : I → L.EncodingRandomness → L.OutOfDomainSeed → KT → Strat L.offline.shape Unit
  /-- a link, from the first table to a copy -/
  Lk : I → L.EncodingRandomness × L.OutOfDomainSeed → L.EncodingRandomness × L.OutOfDomainSeed → KL → Strat L.link.shape Unit
  /-- a session, on a copy -/
  B : I → L.EncodingRandomness → L.OutOfDomainSeed → X → ℕ → KB → Strat L.onlineBatch.loc.shape Unit
  /-- the key's test: are the messages withheld at these verifier messages? -/
  stopT : I → L.EncodingRandomness → L.OutOfDomainSeed → Rho L.offline.shape → Bool
  /-- the same for a link -/
  stopL : I → L.EncodingRandomness × L.OutOfDomainSeed → L.EncodingRandomness × L.OutOfDomainSeed → Rho L.link.shape → Bool
  /-- the same for a session -/
  stopB : I → L.EncodingRandomness → L.OutOfDomainSeed → X → ℕ → Rho L.onlineBatch.loc.shape → Bool

/-- What is handed out of the outcome of a compiled run: the proof string, if the run has returned
one and the verifier messages of its transcript are not such that the messages are withheld. -/
def shown {P : Type} {s : Shape} (stop : Rho s → Bool) : Res (P × Tr s) → Option P
  | .ok a => if stop a.2.rho then none else some a.1
  | .noFormat => none
  | .ranOut _ => none

/-- The three strategies as one family in the triple of their coins: the form in which the prover of
a whole request takes them (Strats, Johnson/Prover/All/Defs.lean). -/
def Plays.joint {L : HolographicProtocol I X} {KT KL KB : Type} (st : Plays L KT KL KB) :
    Strats L (KT × KL × KB) where
  T := fun i r e κ => st.T i r e κ.1
  Lk := fun i a b κ => st.Lk i a b κ.2.1
  B := fun i r e x n κ => st.B i r e x n κ.2.2

/-- **The honest side's letters.** The verifier reads none of them. -/
structure HonestSide (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) where
  /-- the coins of the strategy of the key's test -/
  KT : Type
  /-- the coins of a link's strategy -/
  KL : Type
  /-- the coins of a session's strategy -/
  KB : Type
  /-- the three strategies -/
  st : Plays L KT KL KB
  /-- the body of a table's leaf beyond the word's length -/
  b₀ : Bd
  /-- the key's test: in round number i the search for a nonce may try capT i + 1 nonces -/
  capT : ℕ → ℕ
  /-- the same for a link -/
  capL : ℕ → ℕ
  /-- the same for a session -/
  capB : ℕ → ℕ
  /-- the number of copies is M + 1 -/
  M : ℕ
  /-- the number of the copy that stands at place j of the key's list: public -/
  nm : ℕ → ℕ
  /-- what of a strategy's coins the starts of a compiled run's leaf salts are made of ("run
  values"): strings that the strategy also sends in plain parts, so public once a string is out -/
  RV : Type
  rvT : KT → RV
  rvL : KL → RV
  rvB : KB → RV
  /-- the public start of a leaf's salt in a compiled run of the key's test: from the run values,
  the round's number, whether the tree is over the slot's own component, and the run's first salt -/
  startT : RV → ℕ → Bool → Bits → Bits
  /-- the same for a link -/
  startL : RV → ℕ → Bool → Bits → Bits
  /-- the same for a session -/
  startB : RV → ℕ → Bool → Bits → Bits
  /-- how the run values are read off the plain parts of a run of the key's test. The honest side
  does not use it: a simulator, which has no strategy's coins, does -/
  pvT : Plains L.offline.shape → RV
  /-- the same for a link -/
  pvL : Plains L.link.shape → RV
  /-- the same for a session -/
  pvB : Plains L.onlineBatch.loc.shape → RV
  /-- the public word behind the free bits of the string that stands behind a slot's value: from
  the slot -/
  rtail : ℕ → Bits
  /-- the window of a compiled run's leaf salts: rounds, trees a component, leaves a tree. Of the
  coins that are drawn a run is handed the free bits within the window alone -/
  nR : ℕ
  nK : ℕ
  nJ : ℕ
  /-- what stands for a leaf's free bits outside the window: a fixed public string -/
  fill : Bits
  /-- a table's encoding randomness -/
  ri : Enum L.EncodingRandomness
  /-- a table's salts, one for each leaf -/
  sl : Enum (ℕ → Bits)
  kT : Enum KT
  kL : Enum KL
  kB : Enum KB
  /-- the coins of the compiled run of the key's test: salts, paddings, its place in a request tree
  (Coins, OnBytes/Prover/Defs.lean) -/
  coT : Enum (Coins lam (typedOracleCarrier L Bd aT aL))
  /-- the same for a link -/
  coL : Enum (Coins lam (typedOracleCarrier L Bd aT aL))
  /-- the same for a session -/
  coB : Enum (Coins lam (typedOracleCarrier L Bd aT aL))

/-- **The coins that a compiled run is handed**, out of the coins that are drawn: in front of each
leaf's free bits its public start; behind the free bits of the string behind the slot's value a
public word. Outside the window (rounds below nR, trees below nK, leaves below nJ) a fixed string
stands for the free bits: so what is handed on is a function of the drawn coins WITHIN THE WINDOW.
-/
def dress {I' X' : Type} {L' : BatchProtocolWithLeafBody I' X'} (start : ℕ → Bool → Bits → Bits) (rtail : ℕ → Bits)
    (nR nK nJ : ℕ) (fill : Bits) (co : Coins lam L') : Coins lam L' :=
  { co with
    leaf := fun i b k j =>
      start i b co.salt ++ if i < nR ∧ k < nK ∧ j < nJ then co.leaf i b k j else fill
    rsalt := co.rsalt ++ rtail co.slot }

/-- A table's salts as they are handed on: those that were drawn at the places of the tree's m
leaves, nothing beyond. -/
def cutS (m : ℕ) (s : ℕ → Bits) : ℕ → Bits := fun j => if j < m then s j else []

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} in
/-- The coins that a compiled run of the key's test is handed, at the run values v. -/
def HonestSide.dressT (h : HonestSide lam L Bd aT aL) (v : h.RV)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) : Coins lam (typedOracleCarrier L Bd aT aL) :=
  dress (h.startT v) h.rtail h.nR h.nK h.nJ h.fill co

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} in
/-- The same for a link. -/
def HonestSide.dressL (h : HonestSide lam L Bd aT aL) (v : h.RV)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) : Coins lam (typedOracleCarrier L Bd aT aL) :=
  dress (h.startL v) h.rtail h.nR h.nK h.nJ h.fill co

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} in
/-- The same for a session. -/
def HonestSide.dressB (h : HonestSide lam L Bd aT aL) (v : h.RV)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) : Coins lam (typedOracleCarrier L Bd aT aL) :=
  dress (h.startB v) h.rtail h.nR h.nK h.nJ h.fill co

/-! ## What is kept -/

/-- A table as the honest side keeps it: the encoding's randomness; the tree over the encoded index,
with the inputs of its leaves (so the salts) and all its levels; the seed of its OOD sample. -/
structure TabK (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) where
  r : L.EncodingRandomness
  tree : TreeK lam (typedOracleCarrier L Bd aT aL)
  seed : L.OutOfDomainSeed

/-- **The prover's key**: the index and the copies, in the order of the key's list. The first table
is not in it. -/
structure Isk (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) where
  i : I
  copies : List (TabK lam L Bd aT aL)

/-! ## The coins -/

/-- What the committer draws for one copy. -/
structure DrawCopy (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (KL : Type) where
  /-- the copy's encoding randomness -/
  r : L.EncodingRandomness
  /-- its salts -/
  s : ℕ → Bits
  /-- the coins of the link's strategy -/
  κ : KL
  /-- the coins of the link's compiled run -/
  co : Coins lam (typedOracleCarrier L Bd aT aL)

/-- **What the committer draws.** -/
structure DrawC (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (KT KL : Type) where
  /-- the first table's encoding randomness -/
  r : L.EncodingRandomness
  /-- its salts -/
  s : ℕ → Bits
  /-- the coins of the strategy of the key's test -/
  κ : KT
  /-- the coins of its compiled run -/
  co : Coins lam (typedOracleCarrier L Bd aT aL)
  /-- one entry for each copy -/
  copies : List (DrawCopy lam L Bd aT aL KL)

/-- **What the prover draws for a request.** -/
structure DrawP (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (KB : Type) where
  /-- the place of a copy in the key's list -/
  j : ℕ
  /-- the coins of the session's strategy -/
  κ : KB
  /-- the coins of the session's compiled run -/
  co : Coins lam (typedOracleCarrier L Bd aT aL)

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- The draw of the prover of a whole request (Draw, Johnson/Prover/All/Defs.lean) that the
committer's coins, its coins for one copy, and the prover's coins make up: a function of coins
alone. The copy's salts and the three compiled runs' coins stand in it as they are handed on. -/
def drawOf (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (h : HonestSide lam L Bd aT aL)
    (c : DrawC lam L Bd aT aL h.KT h.KL) (e : DrawCopy lam L Bd aT aL h.KL)
    (d : DrawP lam L Bd aT aL h.KB) : Draw lam L Bd aT aL (h.KT × h.KL × h.KB) :=
  ⟨e.r, cutS (2 ^ W.depth) e.s, h.nm d.j, (c.κ, e.κ, d.κ), h.dressT (h.rvT c.κ) c.co,
    h.dressL (h.rvL e.κ) e.co, h.dressB (h.rvB d.κ) d.co⟩

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (h : HonestSide lam L Bd aT aL)

/-! ## The committer -/

/-- One table: the tree over the encoded index, kept whole; the seed's two queries at its root.
These are the queries of the library's committer behind its coins (committerAtFixedCoins,
Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean), in its order. -/
def tabO (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (TabK lam L Bd aT aL) :=
  (committerTreeKeptByProver W b₀ (L.encodeIndex i r) s).bind fun T =>
    (seedsO W S T.root).bind fun e => .pure ⟨r, T, e⟩

/-- The copies' tables, one after the other: for each its tree, then its seed's two queries. -/
def tabsO (i : I) : List (DrawCopy lam L Bd aT aL h.KL) →
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (List (TabK lam L Bd aT aL))
  | [] => .pure []
  | d :: ds => (tabO W S h.b₀ i d.r (cutS (2 ^ W.depth) d.s)).bind fun t =>
      (tabsO i ds).bind fun ts => .pure (t :: ts)

/-- One copy's entry in the key's list, behind its coins: the link proof from the first table to the
copy's table; then (root, OOD sample, link proof). -/
def linkO (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (d : DrawCopy lam L Bd aT aL h.KL) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) :=
  (proveLA W cA (fun k => if k = 0 then t₁.tree else t₂.tree)
    (h.dressL (h.rvL d.κ) d.co) h.capL t₁.tree.root t₂.tree.root
    (L.recOf i t₁.r t₁.seed) (L.recOf i t₂.r t₂.seed)
    (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r)
    (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) d.κ)).bind fun b =>
  .pure (t₂.tree.root, L.recOf i t₂.r t₂.seed,
    shown (h.st.stopL i (t₁.r, t₁.seed) (t₂.r, t₂.seed)) b)

/-- The entries of the key's list, one after the other. -/
def linksO (i : I) (t₁ : TabK lam L Bd aT aL) :
    List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL) →
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))))
  | [] => .pure []
  | a :: l => (linkO W cA h i t₁ a.2 a.1).bind fun e =>
      (linksO i t₁ l).bind fun es => .pure (e :: es)

/-- **The committer behind its coins.** FIRST ALL TABLES: the first table's tree and seed, then each
copy's. THEN THE PROOFS THAT ARE MADE ONCE: the proof on the first table, then the link proofs. A
program without coins. -/
def commitAt (i : I) (d : DrawC lam L Bd aT aL h.KT h.KL) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (FullKey lam L aT aL × Isk lam L Bd aT aL) :=
  (tabO W S h.b₀ i d.r (cutS (2 ^ W.depth) d.s)).bind fun t₁ =>
    (tabsO W S h i d.copies).bind fun ts =>
    (proveTA W cA (fun _ => t₁.tree) (h.dressT (h.rvT d.κ) d.co) h.capT
      t₁.tree.root (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
      (h.st.T i t₁.r t₁.seed d.κ)).bind fun a =>
    (linksO W cA h i t₁ (d.copies.zip ts)).bind fun ls =>
    .pure (⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, shown (h.st.stopT i t₁.r t₁.seed) a, ls⟩,
      ⟨i, ts⟩)

/-- The coins for one copy: four draws. It asks no oracle. -/
def coinsCopy : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (DrawCopy lam L Bd aT aL h.KL) :=
  .sample h.ri.n fun a => .sample h.sl.n fun b => .sample h.kL.n fun c => .sample h.coL.n fun e =>
    .pure ⟨h.ri.e a, h.sl.e b, h.kL.e c, h.coL.e e⟩

/-- The coins for n copies. -/
def coinsCopies : ℕ → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (List (DrawCopy lam L Bd aT aL h.KL))
  | 0 => .pure []
  | n + 1 => (coinsCopy W h).bind fun d => (coinsCopies n).bind fun ds => .pure (d :: ds)

/-- The committer's coins: the first table's randomness and salts first, as the library's committer
draws them (committerOverTypedOracles); then those of the key's test; then those of the h.M + 1 copies. -/
def coinsC : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (DrawC lam L Bd aT aL h.KT h.KL) :=
  .sample h.ri.n fun a => .sample h.sl.n fun b => .sample h.kT.n fun c => .sample h.coT.n fun e =>
    (coinsCopies W h (h.M + 1)).bind fun ds =>
      .pure ⟨h.ri.e a, h.sl.e b, h.kT.e c, h.coT.e e, ds⟩

/-- **The committer.** -/
def commitW (i : I) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (FullKey lam L aT aL × Isk lam L Bd aT aL) :=
  (coinsC W h).bind fun d => commitAt W S cA h i d

/-! ## The prover -/

/-- **The prover of one request behind its coins**: the session's compiled run on the copy at the
drawn place, out of what is kept. It builds no tree, asks for no seed, and reads nothing of the
first table. A program without coins. -/
def proveAt (isk : Isk lam L Bd aT aL) (x : X) (d : DrawP lam L Bd aT aL h.KB) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (RequestProof lam L) :=
  match isk.copies[d.j]? with
  | none => .pure ⟨d.j, h.nm d.j, none⟩
  | some t =>
    (proveBA W cA r₀ (fun _ => t.tree) (h.dressB (h.rvB d.κ) d.co) h.capB
      t.tree.root x (L.recOf isk.i t.r t.seed) (L.encodeIndex isk.i t.r)
      (h.st.B isk.i t.r t.seed x (h.nm d.j) d.κ)).bind fun c =>
    .pure ⟨d.j, h.nm d.j, shown (h.st.stopB isk.i t.r t.seed x (h.nm d.j)) c⟩

/-- The prover's coins: a place among the h.M + 1 copies, the strategy's coins, the compiled run's.
It asks no oracle. -/
def coinsP : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (DrawP lam L Bd aT aL h.KB) :=
  .sample h.M fun j => .sample h.kB.n fun c => .sample h.coB.n fun e =>
    .pure ⟨j.val, h.kB.e c, h.coB.e e⟩

/-- **The prover**: one request a proof. It has no state. -/
def proveW (isk : Isk lam L Bd aT aL) : (b : List (X × Unit)) →
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (ZKCP.Gen.Slots (RequestProof lam L) b)
  | [] => .pure ⟨[], rfl⟩
  | [(x, _)] => (coinsP W h).bind fun d =>
      (proveAt W cA r₀ h isk x d).bind fun π => .pure ⟨[π], rfl⟩
  | u :: v :: l => .pure ⟨(u :: v :: l).map fun _ => ⟨0, 0, none⟩, by simp⟩

/-! ## The verifier -/

/-- The key that the compiled verifier verifyAtKeyRoot takes, out of the whole key: (root, OOD sample). -/
def lowKey (k : FullKey lam L aT aL) : KeyRoot lam L := ⟨k.cm, k.rcd⟩

/-- The typed proof that verifyAtKeyRoot takes, out of the whole key and a proof: the proof's number of the
copy, the key's proof on the first table, the key's entry at the proof's place, the session's proof.
Where the key's list has no such place: an entry without a link proof, which verifyAtKeyRoot refuses. -/
def lowPrf (k : FullKey lam L aT aL) (π : RequestProof lam L) : OfflineLinkOnlineProof lam L aT aL :=
  ⟨π.copy, k.piT, (k.links[π.leaf]?).getD (k.cm, k.rcd, none), π.piB⟩

/-- **The verifier**: the compiled verifier verifyAtKeyRoot, as it stands, at what is re-packed. -/
def verifyW (k : FullKey lam L aT aL) (x : X) (π : RequestProof lam L) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyAtKeyRoot W S cA r₀ p (lowKey k) x (lowPrf k π)

/-! ## The scheme -/

/-- **THE SCHEME with the whole key published.** -/
def argW : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL)
    (Isk lam L Bd aT aL) (RequestProof lam L) :=
  ⟨commitW W S cA h, proveW W cA r₀ h, verifyW W S cA r₀ p⟩

/-! ## The same honest side at the compiled verifier's own types -/

/-- The scheme at verifyAtKeyRoot's own types, with the same honest side: the committer publishes (root, OOD
sample) alone and keeps the whole key; the prover copies what was made once into each proof and
draws no coin for it. Here what was made once reaches the adversary's view only with the first
proof. -/
def argLow : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot lam L)
    (FullKey lam L aT aL × Isk lam L Bd aT aL) (OfflineLinkOnlineProof lam L aT aL) :=
  ⟨fun i => (commitW W S cA h i).bind fun a => .pure (lowKey a.1, a),
   fun isk b => (proveW W cA r₀ h isk.2 b).bind fun πs =>
     .pure ⟨πs.val.map (lowPrf isk.1), by rw [List.length_map]; exact πs.property⟩,
   verifyAtKeyRoot W S cA r₀ p⟩

end OnBytes.WholeKey
