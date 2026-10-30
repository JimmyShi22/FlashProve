-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/WorkOf.lean: THE WRITTEN BOUNDS ON THE HONEST SIDE's WORK
(Johnson/WholeKey/Work.lean) UNDER THE PREMISES OF THE STATEMENT OF INDEX PRIVACY (PremW,
Johnson/WholeKey/Premises.lean).

General theorems with their proofs. This file states no goal of the release.

Johnson/WholeKey/Work.lean bounds the typed queries of the committer and of the prover under one
premise, PathsFit: the coins that are listed for a compiled run hold as many sibling digests as its
request tree is deep. That premise follows from the laws on the coins, which are among the premises
of the statement of index privacy.

  pathsFit_of_coins, pathsFit_of_prem   PathsFit at the honest side made of the three honest sides
                    of the interactive protocols.
  work_commitW      under PremW the committer asks at most commitN typed queries on every path:
                    (M + 2) tables, the run on the first table, M + 1 link runs: a formula in the
                    number of copies.
  work_proveW       under PremW the prover asks at most proveN typed queries on every path: one
                    session's run.
Limits. Those of Johnson/WholeKey/Work.lean: upper bounds, no number evaluated. TYPED QUERIES, NOT
CALLS OF ONE HASH FUNCTION: a typed query may cost several calls, and the committer's and the
prover's counts in calls of the hash function are typed nowhere.
THESE COUNTS ARE NOT THOSE OF THE WRITTEN ERROR (eW, mW, Johnson/WholeKey/Zeta.lean). What follows
in this paragraph is a reading of the two texts; none of it is shown in Lean. Neither set bounds the
other at all letters. The written error counts the query to g, the request tree's leaf and its nodes
once for each RUN, also for a run without rounds; commitN and proveN count them in every ROUND, with
a Fiat-Shamir query for both components. So the sum of eW + mW over all names is at most commitN + n
· proveN only where each of the three protocols has a round, and the reverse fails as soon as one
has two. The bound on the honest side's work is commitN and proveN.

-/
import Johnson.WholeKey.Work
import Johnson.LateWorld.PremOf

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-- The listed coins of the three kinds of run hold as many sibling digests as the request trees are
deep: from the laws on the coins. -/
theorem pathsFit_of_coins {p : Params} {a : AtRecs lam L Bd aT aL} {c : CoinNums Bd}
    (hc : CoinsFit W p a c) : PathsFit W a.side where
  T := hc.coT.path_length
  Lk := hc.coL.path_length
  B := hc.coB.path_length

variable {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {p : Params}
  {a : AtRecs lam L Bd aT aL} {Sm : Sims L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop}
  {Ryes : I → X → Prop} {c : CoinNums Bd} {u : NumsW}

theorem pathsFit_of_prem (hP : PremW W S cA p a Sm ok Gs Ryes c u) : PathsFit W a.side :=
  pathsFit_of_coins hP.coins

/-- **Under the premises of the statement the committer asks at most commitN typed queries.** -/
theorem work_commitW (hP : PremW W S cA p a Sm ok Gs Ryes c u) (i : I) :
    (commitW W S cA a.side i).QueryBound (commitN W a.side) :=
  queryBound_commitW W S cA a.side (pathsFit_of_prem hP) i

/-- **Under the premises of the statement the prover asks at most proveN typed queries.** -/
theorem work_proveW (hP : PremW W S cA p a Sm ok Gs Ryes c u) (r₀ : L.Rec)
    (isk : Isk lam L Bd aT aL) (b : List (X × Unit)) :
    (proveW W cA r₀ a.side isk b).QueryBound (proveN W a.side) :=
  queryBound_proveW W cA r₀ a.side (pathsFit_of_prem hP) isk b

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.pathsFit_of_prem
#print axioms OnBytes.WholeKey.work_commitW
#print axioms OnBytes.WholeKey.work_proveW
