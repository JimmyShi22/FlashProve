-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SpecWrap.lean: THE HONEST SIDE THAT LAYS LATE (lateW, Johnson/LateWorld/Defs.lean)
AGAINST THE REDUCTION AROUND THE GAME's REAL SIDE (wrapW, Johnson/WholeKey/Wrap.lean; gameReal,
Hiop/Seeded/Game.lean). DEFINITIONS AND THE STATEMENT. The proof is in
Johnson/LateWorld/Whole.lean.

This file states no goal of the release: the statement is one step of the proof of index privacy for
the scheme with the whole key published.

The two challengers do the same, but for two things that the game does and the honest side does not:
  the game serves at most s1 sessions on a copy, and refuses beyond; the prover has no state and
      draws its copy at random;
  the game refuses a table whose seed lies outside the public set Gs.
The game's honest sides are recsG a (Johnson/WrapLaws/Recs.lean), off the three honest sides: the
test's and the link's at every number; the session's on the table number e is that for the number of
the copy at the place e - 1 of the key's list.
So they are not equal but close:
  Prob.pOver (M + 1) s1 n   some copy is drawn more than s1 times in n sessions (Prob/Tail.lean);
  (M + 2) · δ               one of the M + 2 tables has its seed outside Gs.

Main names (namespace OnBytes.LateWorld).
  PremLate   the premises. ok: a set of indices, a letter; one clause is asked at its members alone.
  Spec.lateToWrap   THE STATEMENT, for adversaries whose first move is the setup, which then send
             batches of at most one slot.

Why "whose first move is the setup". The experiment of the definition hands out the key before the
adversary's first query. From a table that already has entries the chance that a seed lies outside
Gs is not at most δ state by state.

Limits. δ and s1 are letters: whether the bound is small at given letters is not said. The statement
speaks of adversaries whose first move is the setup alone. lateW is a device of the proof and stands
in no statement on the scheme: the step counts only as a part of the proof of index privacy. The
term (M + 2) · δ has been put to no test at a member: at both small members of the premises that are
typed (Johnson/WholeKey/Member.lean, Member2.lean) Gs is all seeds and δ = 0, so the game refuses no
table there.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Defs
import Johnson.WholeKey.Wrap
import Johnson.WholeKey.Premises
import Johnson.WrapLaws.Recs
import Prob.Tail

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.WrapLaws
open _root_.Compile.GlueB (GCall GIn GAdm asW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **The premises.** -/
structure PremLate (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (a : AtRecs lam L Bd aT aL) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop)
    (δ : ℝ≥0∞) : Prop where
  /-- the honest sides speak of the encodings -/
  ext : ExtEnc a.Hs
  /-- the run values stand in the plain parts, at the indices of ok -/
  runVals : RunVals a ok
  /-- the positions read do not hang on nonces -/
  freeT : ReadsFree (batTC L aT) (wTC W).sh
  freeL : ReadsFree (batLC L aL) (wLC W).sh
  freeB : ReadsFree L.onlineBatch (wBC W).sh
  /-- the wires' laws -/
  wires : OKA W cA
  /-- the enumerations of the encoding's randomness and of the strategies' coins list each member
  once -/
  ri : a.ri.OK
  kT : a.kT.OK
  kL : a.kL.OK
  kB : a.kB.OK
  /-- the coins of a compiled run hold as many sibling digests as its request tree is deep -/
  pathT : ∀ n, (a.coT.e n).path.length = W.depthReqT
  pathL : ∀ n, (a.coL.e n).path.length = W.depthReqL
  pathB : ∀ n, (a.coB.e n).path.length = W.depthReq
  /-- a seed made from uniform digests lies outside Gs with probability at most δ -/
  seeds : pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ

/-- **THE STATEMENT.** -/
def Spec.lateToWrap : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (a : AtRecs lam L Bd aT aL) (ok : I → Prop)
    (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞) (s1 : ℕ) (i : I),
    PremLate W S cA a ok Gs δ → ok i →
    ∀ (α : Type) (okb : ZKCP.Gen.Batch X Unit → Prop)
      (k : GIn (FullKey lam L aT aL) (RequestProof lam L) →
        Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
          (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ),
      (∀ b, okb b → b.length ≤ 1) → GAdm okb (.call .setup k) false n →
      tv ((interact (lateW W S cA r₀ a.side i) (.call .setup k) (none, Table.empty _)).map Prod.fst)
          ((interact (asW Unit ((wrapW W S cA r₀ a.side).world
              (Hiop.Seeded.gameReal L (kitW W r₀ a.side) (recsG a) i (boundsW a.side s1) Gs _)))
            (.call .setup k) ((Table.empty _, none), (none, Table.empty _))).map Prod.fst) ≤
        Prob.pOver (a.M + 1) s1 n + ((a.M + 2 : ℕ) : ℝ≥0∞) * δ

end OnBytes.LateWorld
