-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsOne.lean: the entry's arm with the answers alone in the first query,
against every maker over one hash function.

`arm_pr` (LinkAnsPr.lean) is over the typed oracles. Here all typed oracles are read out of one
random function on bit strings, through a coding m of the typed queries (`Rom.OracleCoding`,
Rom/Family.lean). The maker is any algorithm that asks that one function. The verifier's arm draws
no coin, so its run is a function of the oracle functions: it is run at `readBlocks m g`, the typed
oracle functions that m reads out of g.

  `runA`         the run of an arm (`IsArm`) at typed oracle functions: its verdict and its log
  `logOne`       the typed log of maker and verifier: each string that the maker asked, as the typed
                 query that it codes with that query's whole answer; then the verifier's log
  `arm_pr_one`   the bound, the same as `arm_pr`'s: one query of the maker to the hash function
                 counts as one typed query. At `armS`: the arm with the strict Link; at `armL`:
                 with the lax one

How: an algorithm over the hash function is an algorithm over the typed oracles with as many queries
(`down`, Rom/ExitDown.lean), and a random function on strings is a random family (`lintegral_glue`).

Limits: soundness alone.
  * No coding m is given. A coding (`Rom.OracleCoding`) is one to one and onto all bit strings, with places
    for every typed oracle whose answers hold a block, those that no verifier asks among them. That
    one exists is not shown in this folder (Johnson/Flat/EntryCoding.lean [not in this library; so
    here read: not proved in this library]
    shows it where the instances are countable, by choice); that the programs' strings are its codes
    is shown nowhere.
  * m, the wires W and S (`S.cfg` with it), the code cA and the arm are fixed before the function is
    drawn.
  * The maker puts out typed values (digests, records, a typed proof string), not bytes.
  * The typed log holds, for each string that the maker asked, the whole answer of the typed query
    that the string codes, though the maker may have asked one block of it. The words under the
    roots read entries at the leaf and node oracles alone.
  * In this file the arm is run at `readBlocks m g`: it is no algorithm over the function
    (LinkAnsMore.lean: `arm_overOne`, `arm_pr_hash` make it one). Its calls to the function are
    counted neither in t nor, as calls to the function, in n (n counts its typed queries).
  * The bullets under "Limits" in the head of LinkAnsPr.lean hold of this file too.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPr
import Rom.ExitDown

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
  (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
  (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)

/-- The run of an arm at typed oracle functions: its verdict and its log. -/
def runA (G : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (z : OutLA lam L aL) : Bool × Tc W :=
  (V z).withTrace.det G

/-- The typed log of a maker over the hash function and of an arm. -/
def logOne (G : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (o : OutLA lam L aL × Trace (rom lam)) :
    Tc W :=
  upTr m G o.2 ++ (runA W V G o.1).2

/-- The typed experiment at the maker brought down, under F: the maker's run under the hash function
that holds all of F, with the arm's run laid behind it. -/
theorem joinedA_down (hV : ∀ z, (V z).NoCoin) (A : OComp (rom lam) (OutLA lam L aL))
    (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (joinedA W V (down m A)).withTrace.runEager F =
      (A.withTrace.runEager (glue m F)).map fun o =>
        ((o.1, (runA W V F o.1).1), logOne W V m F o) := by
  unfold joinedA
  rw [Rom.withTrace_bind, OComp.runEager_bind, withTrace_down, PMF.bind_map,
    ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun o => ?_)
  have hnc : ((V o.1).bind fun b =>
      (OComp.pure (o.1, b) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL × Bool))).NoCoin :=
    OComp.NoCoin.bind (hV o.1) fun _ => trivial
  show ((((V o.1).bind fun b =>
      (OComp.pure (o.1, b) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL)
        (OutLA lam L aL × Bool))).withTrace.bind fun out' =>
      OComp.pure (out'.1, upTr m F o.2 ++ out'.2)).runEager F) = PMF.pure _
  rw [runEager_bind_pure, runEager_withTrace_det F _ hnc, PMF.pure_map, Rom.withTrace_bind,
    OComp.det_bind, OComp.det_bind]
  show PMF.pure ((o.1, (runA W V F o.1).1), upTr m F o.2 ++ ((runA W V F o.1).2 ++ [])) = _
  rw [List.append_nil]
  rfl

variable {W V}

/-- An arm (`IsArm`) is sound against every maker over one hash function: the arm, run at the typed
oracle functions that m reads out of the hash function, accepts, and what it promises fails on the
typed log of the maker and the arm, with probability at most n εs + 2 (n + 1)² / 2^lam, where
n = 5 (t + tVL) and t bounds the maker's queries to the hash function (hq). The premises are those
of `arm_pr` (LinkAnsPr.lean); m is any coding. -/
theorem arm_pr_one {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (A : OComp (rom lam) (OutLA lam L aL)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr A.withTrace
        (fun g => {o | (runA W V (readBlocks m g) o.1).1 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have key : ∀ F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)),
      PrCoins (glue m F) A.withTrace
          {o | (runA W V (readBlocks m (glue m F)) o.1).1 = true ∧
            ¬ LinkHolds W (logOne W V m (readBlocks m (glue m F)) o) o.1.1 o.1.2.1 o.1.2.2.1
              o.1.2.2.2.1} =
        PrCoins F (joinedA W V (down m A)).withTrace
          {o | o.1.2 = true ∧ ¬ LinkHolds W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1} := by
    intro F
    unfold PrCoins
    rw [joinedA_down W V m fun z => noCoin_of_detBound (hV.det z), pr_map, readBlocks_glue]
    rfl
  refine le_trans (le_of_eq ?_)
    (arm_pr hsL hlL hcL hW hA hSd hbL hV (down m A) t (queryBound_down m A t hq))
  unfold Rom.Pr
  rw [lintegral_glue m (fun g => PrCoins g A.withTrace
      {o | (runA W V (readBlocks m g) o.1).1 = true ∧
        ¬ LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1})]
  · simp only [key]
  · simp only [key]
    exact measurable_PrCoins _ _

end TypedOracleCompiler.Compile.Batch.Cms
