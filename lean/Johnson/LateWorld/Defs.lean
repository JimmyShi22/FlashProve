-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Defs.lean: THE HONEST SIDE OF THE SCHEME WITH THE WHOLE KEY PUBLISHED (argW,
Johnson/WholeKey/Defs.lean), ON AN INDEX i, AS A CHALLENGER THAT LAYS ITS HASH QUERIES LATE.
DEFINITIONS ALONE.

General definitions. This file states no goal of the release and proves nothing. The challenger is a
device of the proof of index privacy: a world between the real experiment and the reduction around
the game (wrapW, Johnson/WholeKey/Wrap.lean). It stands in no statement on the scheme.

What it is. The real challenger (realW, Compile/Batch/SpecGlue.lean) runs the committer's and the
prover's programs under lazy sampling from one table. This one runs THE SAME PROGRAMS, at the same
coins, honest strategies and index, with the same calls, replies and state. It differs in how their
queries are answered:
  the making of a table (tabO, tabsO): its leaves get fresh answers without a look at the table and
      are not written (OComp.runDefer at mkTab); inner nodes and the seed's two queries are asked of
      the table. What is pending of a table is what the prover's key holds of it: each leaf's input
      and its digest.
  a compiled run (the prover's chain, chainX): leaves, Fiat-Shamir queries, g and the request tree
      get fresh answers and are logged (runDefer at mkRun); inner nodes are asked of the table. Then
      what is handed out (handOut, Johnson/WholeKey/Sim.lean): if the chain has come to its end and
      the honest side does not withhold its messages at the run's verifier messages, the string, and
      these are written where the table has no entry: the log's entries that are no leaves, the
      run's own leaves at the positions read, the tables' leaves at the positions read. Else
      nothing is handed out and nothing late is written.

Main names (namespace OnBytes.LateWorld).
  goOf        is a string handed out: the chain has ended and the messages are not withheld.
  lateProof     one compiled run, laid late, at letters.
  lateTA, lateLA, lateBA   at the three sets of letters of proveTA, proveLA, proveBA
              (Johnson/Prover/YesOfProve.lean).
  lateLinks, lateCommit, lateAt, lateBatch   the committer and the prover, step for step as linksO,
              commitW, proveAt, proveW.
  lateW       THE CHALLENGER.

It follows the pattern of the scheme's own text: linkO, linksO, commitAt, commitW, proveAt, proveW
(Johnson/WholeKey/Defs.lean), step for step, at the letters of proveTA, proveLA, proveBA
(Johnson/Prover/YesOfProve.lean); the world's form is that of realW (Compile/Batch/SpecGlue.lean).

Limits. Definitions alone. A batch that is not one request of the adversary's own gets a fixed reply
and no program is run: no proof for a batch without an own slot; the fixed proofs of proveW for two
slots or more. So for a batch of one slot that is not the adversary's own this challenger does NOT
run the session that the real prover runs.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Sim
import Compile.Batch.SpecGlue

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Compile.GlueB (GCall GIn ownPf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## One compiled run, laid late -/

section Generic
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- Is a string handed out: the chain has come to its end, and the honest side does not withhold its
messages at the run's verifier messages. -/
def goOf {s : Shape} (stop : Rho s → Bool) : Res (OutP lam L s) → Bool
  | .ok z => !stop z.1
  | _ => false

variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L) (cap : ℕ → ℕ)

/-- **One compiled run, laid late**, against the table T: the proof string, or none; the table after
it. -/
def lateProof (stop : Rho Q.loc.shape → Bool) (σ : Strat Q.loc.shape Unit) (co : Coins lam L)
    (T : Table (typedOracleFamily lam K L)) : PMF (Option (OneProtocolProof lam Q) × Table (typedOracleFamily lam K L)) :=
  ((chainX t Q wq embS embP xin cms x cap σ co).runDefer mkRun T []).map fun o =>
    handOut Q wq x y xt (goOf stop o.1) co (o.1, ⟨o.2.1, o.2.2, [], false⟩)

end Generic

/-! ## At an object with out-of-domain samples -/

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

/-- lateProof at the letters of the key's test (proveTA). -/
def lateTA (xt : ℕ → TreeK lam (typedOracleCarrier L Bd aT aL)) (co : Coins lam (typedOracleCarrier L Bd aT aL))
    (cap : ℕ → ℕ) (cm : Dig lam) (rec : L.Rec) (y : (oneExternalString L.wordLength L.Symbol).Str)
    (stop : Rho L.offline.shape → Bool) (σ : Strat L.offline.shape Unit) (T : Tb W) :
    PMF (Option (OneProtocolProof lam (batTC L aT)) × Tb W) :=
  lateProof Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) (cmsTA cA cm rec.2) rec y xt cap
    stop σ co T

/-- At the letters of the link (proveLA). -/
def lateLA (xt : ℕ → TreeK lam (typedOracleCarrier L Bd aT aL)) (co : Coins lam (typedOracleCarrier L Bd aT aL))
    (cap : ℕ → ℕ) (cm cm' : Dig lam) (rec rec' : L.Rec) (y : (twoExternalStrings L.wordLength L.Symbol).Str)
    (stop : Rho L.link.shape → Bool) (σ : Strat L.link.shape Unit) (T : Tb W) :
    PMF (Option (OneProtocolProof lam (batLC L aL)) × Tb W) :=
  lateProof Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) (cmsLA cA cm cm' rec.2 rec'.2)
    (rec, rec') y xt cap stop σ co T

/-- At the letters of the session (proveBA). -/
def lateBA (xt : ℕ → TreeK lam (typedOracleCarrier L Bd aT aL)) (co : Coins lam (typedOracleCarrier L Bd aT aL))
    (cap : ℕ → ℕ) (cm : Dig lam) (x : X) (rec : L.Rec) (y : (oneExternalString L.wordLength L.Symbol).Str)
    (stop : Rho L.onlineBatch.loc.shape → Bool) (σ : Strat L.onlineBatch.loc.shape Unit) (T : Tb W) :
    PMF (Option (OneProtocolProof lam L.onlineBatch) × Tb W) :=
  lateProof Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA cm rec.2) (x, rec) y xt cap stop σ
    co T

/-- The entries of the key's list, one after the other (linksO, linkO). -/
def lateLinks (i : I) (t₁ : TabK lam L Bd aT aL) :
    List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL) → Tb W →
    PMF (List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) × Tb W)
  | [], T => PMF.pure ([], T)
  | a :: l, T =>
      (lateLA W cA (fun k => if k = 0 then t₁.tree else a.2.tree) (h.dressL (h.rvL a.1.κ) a.1.co)
        h.capL t₁.tree.root a.2.tree.root (L.recOf i t₁.r t₁.seed) (L.recOf i a.2.r a.2.seed)
        (L.encodeIndex i t₁.r, L.encodeIndex i a.2.r) (h.st.stopL i (t₁.r, t₁.seed) (a.2.r, a.2.seed))
        (h.st.Lk i (t₁.r, t₁.seed) (a.2.r, a.2.seed) a.1.κ) T).bind fun o =>
      (lateLinks i t₁ l o.2).bind fun o' =>
      PMF.pure ((a.2.tree.root, L.recOf i a.2.r a.2.seed, o.1) :: o'.1, o'.2)

/-- The committer (commitW): its coins; all tables, their leaves late; then the proofs that are made
once, laid late. -/
def lateCommit (i : I) (T : Tb W) : PMF ((FullKey lam L aT aL × Isk lam L Bd aT aL) × Tb W) :=
  ((coinsC W h).runLazy T).bind fun o₀ =>
  ((tabO W S h.b₀ i o₀.1.r (cutS (2 ^ W.depth) o₀.1.s)).runDefer mkTab o₀.2 []).bind fun o₁ =>
  ((tabsO W S h i o₀.1.copies).runDefer mkTab o₁.2.1 []).bind fun o₂ =>
  (lateTA W cA (fun _ => o₁.1.tree) (h.dressT (h.rvT o₀.1.κ) o₀.1.co) h.capT o₁.1.tree.root
    (L.recOf i o₁.1.r o₁.1.seed) (L.encodeIndex i o₁.1.r) (h.st.stopT i o₁.1.r o₁.1.seed)
    (h.st.T i o₁.1.r o₁.1.seed o₀.1.κ) o₂.2.1).bind fun o₃ =>
  (lateLinks W cA h i o₁.1 (o₀.1.copies.zip o₂.1) o₃.2).bind fun o₄ =>
  PMF.pure ((⟨o₁.1.tree.root, L.recOf i o₁.1.r o₁.1.seed, o₃.1, o₄.1⟩, ⟨i, o₂.1⟩), o₄.2)

/-- The prover of one request behind its coins (proveAt). -/
def lateAt (isk : Isk lam L Bd aT aL) (x : X) (d : DrawP lam L Bd aT aL h.KB) (T : Tb W) :
    PMF (RequestProof lam L × Tb W) :=
  match isk.copies[d.j]? with
  | none => PMF.pure (⟨d.j, h.nm d.j, none⟩, T)
  | some t =>
    (lateBA W cA r₀ (fun _ => t.tree) (h.dressB (h.rvB d.κ) d.co) h.capB t.tree.root x
      (L.recOf isk.i t.r t.seed) (L.encodeIndex isk.i t.r) (h.st.stopB isk.i t.r t.seed x (h.nm d.j))
      (h.st.B isk.i t.r t.seed x (h.nm d.j) d.κ) T).map fun o => (⟨d.j, h.nm d.j, o.1⟩, o.2)

/-- A batch. One request of the adversary's own: the prover's coins, then the session. Else a fixed
reply: the proofs of the adversary's own slots among the fixed proofs that proveW gives. -/
def lateBatch (isk : Isk lam L Bd aT aL) (T : Tb W) : ZKCP.Gen.Batch X Unit →
    PMF (List (RequestProof lam L) × Tb W)
  | [(x, _, true)] => ((coinsP W h).runLazy T).bind fun o =>
      (lateAt W cA r₀ h isk x o.1 o.2).map fun a => ([a.1], a.2)
  | b => PMF.pure (b.ownX.map fun _ => ⟨0, 0, none⟩, T)

/-- **THE CHALLENGER THAT LAYS LATE**, on the index i. Its state: the prover's key, once the setup
has been made; the table. It starts from (none, the empty table). -/
def lateW (i : I) : World (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
    (GIn (FullKey lam L aT aL) (RequestProof lam L)) where
  σ := Option (Isk lam L Bd aT aL) × Tb W
  answer := fun s o q => (lazyAnswer s.2 o q).map fun a => (a.1, (s.1, a.2))
  reply := fun s c =>
    match c, s.1 with
    | .setup, _ => (lateCommit W S cA h i s.2).map fun o => (.inl o.1.1, (some o.1.2, o.2))
    | .batch _, none => PMF.pure (.inr [], s)
    | .batch b, some k => (lateBatch W cA r₀ h k s.2 b).map fun o => (.inr o.1, (some k, o.2))

end OnBytes.LateWorld
