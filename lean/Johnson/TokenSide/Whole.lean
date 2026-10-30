-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/Whole.lean: THE HONEST SIDE OF THE SCHEME WITH THE WHOLE KEY PUBLISHED
(Johnson/WholeKey/Defs.lean) AS TOKEN PROGRAMS, and the challenger whose steps they are. DEFINITIONS
ALONE.

A device of one step of a proof of index privacy (the head of Johnson/TokenSide/Split.lean). The
scheme is not defined by these programs.

Each program is laid, bind by bind, on the scheme's own term of the like name:
  tabT, tabsT, linkT, linksT, commitAtT   on tabO, tabsO, linkO, linksO, commitAt
  coinsCopyT, coinsCopiesT, coinsCT, commitT   on coinsCopy, coinsCopies, coinsC, commitW
  proveAtT, coinsPT, proveWT   on proveAt, coinsP, proveW
What differs. (1) The scheme draws a table's salts and the coins of a compiled run at the start,
from enumerations. Here the secret strings among them are tokens, drawn where they are first used,
with the lengths of TokLen; the draws from the enumerations sl, coT, coL, coB are not made. The
other coins (a table's encoding randomness, the three strategies' coins, the place of a copy) are
drawn as in the scheme, from the same enumerations, in the same order. (2) The test for a stop
stands inside the compiled run's twin, before its reveals (proveC,
Johnson/TokenRules/Chunks.lean). (3) What is kept of a table holds tokens in the place of salts
(TabT, IskT).

A TABLE's SEED IS ASKED BY TWO ORDINARY QUERIES, at the root, which is a value: the queries of the
scheme's committer and of the verifier (seedQ0, seedQ1, Johnson/TypedOracleCompiler/RecCompile/Seeds.lean). seedPts
is the set of these points: the letter sd of the rules (rulesT, Johnson/TokenSide/Split.lean).

THE CHALLENGER (challT) has the calls and replies of the real experiment as a challenger (realW,
Compile/Batch/SpecGlue.lean). Its state is the prover's key with tokens. TOKENS KEEP THEIR NUMBERS
FOR THE WHOLE EXPERIMENT: a session's program is run as it stands, on the numbers that the key
holds, with no renumbering. WHAT IS NOT SHOWN IS NOT MADE: a batch whose one request is not the
adversary's own runs no program; the real experiment runs the prover there and drops the proof.

Main names (namespace OnBytes.TokenSide).
  TokLen   the lengths, starts and fixed values of the secret strings.
  TabT, IskT, TabT.toK   a table and the prover's key, with tokens.
  seedPts, seedsT   the seeds' points; the two queries.
  DrawCopyD, DrawCD, DrawPD   the coins that are drawn from enumerations.
  challT   THE CHALLENGER.

Limits. Definitions alone: that these programs erase to the scheme's terms under a law on the
scheme's coins, that they keep the rules, and how many evaluations they make, is not shown here. One
request a proof, as in the scheme. One run of the committer: a second call "setup" is answered by an
empty list.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenRules.Chunks
import Johnson.WholeKey.Defs
import Compile.Batch.SpecGlue

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey
open _root_.Compile.GlueB (GCall ownPf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ}

/-! ## The letters -/

/-- The lengths, the starts and the fixed values of the honest side's secret strings. The start of a
leaf's salt in a compiled run may hang on the strategy's coins, the round's number, the component
and the run's first salt. -/
structure TokLen (lam : ℕ) {I' X' : Type} (L' : BatchProtocolWithLeafBody I' X') (KT KL KB : Type) where
  /-- a table's salts: the public start, the number of free bits -/
  preE : Bits
  frE : ℕ
  /-- the three compiled runs -/
  T : RunLen lam L'
  Lk : RunLen lam L'
  B : RunLen lam L'
  stT : KT → ℕ → Bool → Bits → Bits
  stL : KL → ℕ → Bool → Bits → Bits
  stB : KB → ℕ → Bool → Bits → Bits

/-! ## What is kept -/

/-- A table as it is kept, with tokens: the twin of TabK. -/
structure TabT (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) where
  r : L.EncodingRandomness
  tree : TreeT lam (typedOracleCarrier L Bd aT aL)
  seed : L.OutOfDomainSeed

/-- The prover's key with tokens: the twin of Isk. -/
structure IskT (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) where
  i : I
  copies : List (TabT lam L Bd aT aL)

/-- What the committer draws from enumerations for one copy. -/
structure DrawCopyD (L : HolographicProtocol I X) (KL : Type) where
  r : L.EncodingRandomness
  κ : KL

/-- What the committer draws from enumerations. -/
structure DrawCD (L : HolographicProtocol I X) (KT KL : Type) where
  r : L.EncodingRandomness
  κ : KT
  copies : List (DrawCopyD L KL)

/-- What the prover draws from enumerations for a request. -/
structure DrawPD (KB : Type) where
  j : ℕ
  κ : KB

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- the table as the scheme keeps it, at values of the tokens -/
def TabT.toK (val : Tok → Bits) (pre : Bits) (t : TabT lam L Bd aT aL) : TabK lam L Bd aT aL :=
  ⟨t.r, t.tree.toK val pre, t.seed⟩

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
  (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)

/-! ## The committer -/

/-- The points of the seeds' queries: the ordinary queries that the rules allow at a Fiat-Shamir
oracle. -/
def seedPts (t : Tag) (q : FbIn lam (typedOracleCarrier L Bd aT aL) t) : Prop :=
  (∃ cm, (⟨t, q⟩ : Σ t, FbIn lam (typedOracleCarrier L Bd aT aL) t) = ⟨S.t, seedQ0 W S cm⟩) ∨
    ∃ v, (⟨t, q⟩ : Σ t, FbIn lam (typedOracleCarrier L Bd aT aL) t) = ⟨S.t, seedQ1 W S v⟩

/-- The seed's two queries at a root, as ordinary queries: the twin of seedsO. -/
def seedsT (cm : Dig lam) : StT lam W.K (typedOracleCarrier L Bd aT aL) L.OutOfDomainSeed :=
  Step.plain (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t) (seedQ0 W S cm) fun a0 =>
    Step.plain (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
      (seedQ1 W S (TypedOracleCompiler.Compile.Batch.link
        (show TypedOracleCompiler.Compile.Batch.FsAns lam W.K from a0))) fun a1 =>
      Step.pure (S.seed (show TypedOracleCompiler.Compile.Batch.FsAns lam W.K from a1).1)

/-- One table: the twin of tabO. The bodies of the leaves are the committer's (committerLeafInput). -/
def tabT (b₀ : Bd) (i : I) (r : L.EncodingRandomness) :
    StT lam W.K (typedOracleCarrier L Bd aT aL) (TabT lam L Bd aT aL) :=
  (treeT (K := W.K) tl.frE [] (fun _ => tl.preE) W.depth
    fun j => (committerLeafInput W b₀ (L.encodeIndex i r) (fun _ => []) j).body).bind fun T =>
    (seedsT W S T.root).bind fun e => .pure ⟨r, T, e⟩

/-- The copies' tables: the twin of tabsO. -/
def tabsT (i : I) : List (DrawCopyD L h.KL) →
    StT lam W.K (typedOracleCarrier L Bd aT aL) (List (TabT lam L Bd aT aL))
  | [] => .pure []
  | d :: ds => (tabT W S h tl h.b₀ i d.r).bind fun t =>
      (tabsT i ds).bind fun ts => .pure (t :: ts)

/-- One copy's entry in the key's list: the twin of linkO. -/
def linkT (i : I) (t₁ t₂ : TabT lam L Bd aT aL) (d : DrawCopyD L h.KL) :
    StT lam W.K (typedOracleCarrier L Bd aT aL) (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) :=
  (proveC Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
    (cmsLA cA t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed).2 (L.recOf i t₂.r t₂.seed).2)
    (L.recOf i t₁.r t₁.seed, L.recOf i t₂.r t₂.seed) (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r)
    (fun k => if k = 0 then t₁.tree else t₂.tree) tl.preE
    (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) d.κ) tl.Lk (tl.stL d.κ) h.capL
    (h.st.stopL i (t₁.r, t₁.seed) (t₂.r, t₂.seed))).bind fun b =>
  .pure (t₂.tree.root, L.recOf i t₂.r t₂.seed, b)

/-- The entries of the key's list: the twin of linksO. -/
def linksT (i : I) (t₁ : TabT lam L Bd aT aL) :
    List (DrawCopyD L h.KL × TabT lam L Bd aT aL) →
    StT lam W.K (typedOracleCarrier L Bd aT aL) (List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))))
  | [] => .pure []
  | a :: l => (linkT W cA h tl i t₁ a.2 a.1).bind fun e =>
      (linksT i t₁ l).bind fun es => .pure (e :: es)

/-- The committer behind the coins that are drawn from enumerations: the twin of commitAt. -/
def commitAtT (i : I) (d : DrawCD L h.KT h.KL) :
    StT lam W.K (typedOracleCarrier L Bd aT aL) (FullKey lam L aT aL × IskT lam L Bd aT aL) :=
  (tabT W S h tl h.b₀ i d.r).bind fun t₁ =>
    (tabsT W S h tl i d.copies).bind fun ts =>
    (proveC Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
      (cmsTA cA t₁.tree.root (L.recOf i t₁.r t₁.seed).2) (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
      (fun _ => t₁.tree) tl.preE (h.st.T i t₁.r t₁.seed d.κ) tl.T (tl.stT d.κ) h.capT
      (h.st.stopT i t₁.r t₁.seed)).bind fun a =>
    (linksT W cA h tl i t₁ (d.copies.zip ts)).bind fun ls =>
    .pure (⟨t₁.tree.root, L.recOf i t₁.r t₁.seed, a, ls⟩, ⟨i, ts⟩)

/-- The twin of coinsCopy, without the draws of salts and of a run's coins. -/
def coinsCopyT : StT lam W.K (typedOracleCarrier L Bd aT aL) (DrawCopyD L h.KL) :=
  .sample h.ri.n fun a => .sample h.kL.n fun c => .pure ⟨h.ri.e a, h.kL.e c⟩

def coinsCopiesT : ℕ → StT lam W.K (typedOracleCarrier L Bd aT aL) (List (DrawCopyD L h.KL))
  | 0 => .pure []
  | n + 1 => (coinsCopyT W h).bind fun d => (coinsCopiesT n).bind fun ds => .pure (d :: ds)

/-- The twin of coinsC. -/
def coinsCT : StT lam W.K (typedOracleCarrier L Bd aT aL) (DrawCD L h.KT h.KL) :=
  .sample h.ri.n fun a => .sample h.kT.n fun c =>
    (coinsCopiesT W h (h.M + 1)).bind fun ds => .pure ⟨h.ri.e a, h.kT.e c, ds⟩

/-- **The committer as a token program**: the twin of commitW. -/
def commitT (i : I) :
    StT lam W.K (typedOracleCarrier L Bd aT aL) (FullKey lam L aT aL × IskT lam L Bd aT aL) :=
  (coinsCT W h).bind fun d => commitAtT W S cA h tl i d

/-! ## The prover -/

/-- The prover of one request behind the coins that are drawn from enumerations: the twin of
proveAt. -/
def proveAtT (isk : IskT lam L Bd aT aL) (x : X) (d : DrawPD h.KB) :
    StT lam W.K (typedOracleCarrier L Bd aT aL) (RequestProof lam L) :=
  match isk.copies[d.j]? with
  | none => .pure ⟨d.j, h.nm d.j, none⟩
  | some t =>
    (proveC Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀)
      (cmsBA cA t.tree.root (L.recOf isk.i t.r t.seed).2) (x, L.recOf isk.i t.r t.seed)
      (L.encodeIndex isk.i t.r) (fun _ => t.tree) tl.preE (h.st.B isk.i t.r t.seed x (h.nm d.j) d.κ) tl.B
      (tl.stB d.κ) h.capB (h.st.stopB isk.i t.r t.seed x (h.nm d.j))).bind fun c =>
    .pure ⟨d.j, h.nm d.j, c⟩

/-- The twin of coinsP. -/
def coinsPT : StT lam W.K (typedOracleCarrier L Bd aT aL) (DrawPD h.KB) :=
  .sample h.M fun j => .sample h.kB.n fun c => .pure ⟨j.val, h.kB.e c⟩

/-- **The prover as a token program**, on a batch as the environment names it: one proof for each
slot. A batch of one request that is the adversary's own: a session. Any other batch: the fixed
proofs of proveW, and no program is run: of a batch of one request that is not the adversary's own
nothing is shown. -/
def proveWT (isk : IskT lam L Bd aT aL) : ZKCP.Gen.Batch X Unit →
    StT lam W.K (typedOracleCarrier L Bd aT aL) (List (RequestProof lam L))
  | [(x, _, true)] => (coinsPT W h).bind fun d =>
      (proveAtT W cA r₀ h tl isk x d).bind fun π => .pure [π]
  | b => .pure (b.map fun _ => ⟨0, 0, none⟩)

/-! ## The challenger -/

/-- **The challenger** whose steps are the token programs. -/
def challT (i : I) : Chall (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
    (splitT lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
    (_root_.Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L)) where
  τ := Option (IskT lam L Bd aT aL)
  step := fun s c => match c, s with
    | .setup, none => (commitT W S cA h tl i).bind fun o => Step.pure (.inl o.1, some o.2)
    | .setup, some k => Step.pure (.inr [], some k)
    | .batch _, none => Step.pure (.inr [], none)
    | .batch b, some k =>
        (proveWT W cA r₀ h tl k b).bind fun πs => Step.pure (.inr (ownPf b πs), some k)

end OnBytes.TokenSide
