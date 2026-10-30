-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecOneCall.lean: under `Std m` and `Test0 W` a failed proof-of-work attempt that is
not the last costs one hash query (`Spec.failCostsOne`): the rule, the relation, the counts.
Definitions and statements. Nothing is proved here. (Words of this library: lean/GLOSSARY.md.)

In a round with proof-of-work bits the honest prover queries the Fiat-Shamir oracle once for each
nonce (an attempt), until all these bits of the verifier message are 0; if none passes it goes on
with the last (Compile/Batch/Prover.lean: `fbG`). The final attempt is the one whose challenge the
proof uses. In the step to one hash function f that asks only for marked blocks (Rom/OverOneN.lean)
every attempt is counted with all hash blocks that a final attempt needs. Here: the same step with
an adaptive rule (Rom/SpecOverOneA.lean) under which a failed attempt that is not the last costs one
query to f (`Spec.failCostsOne`: under `Std m` and `Test0 W`).

  `tryInfo`, `tryInfoT`   what a Fiat-Shamir query says of its attempt, read off its plain part:
                          none if that component of its round has no proof-of-work bits; else the
                          check as a function of the K hash blocks of the answer, and whether the
                          nonce denotes the last number that the honest prover uses (or a later one)
  `agF`   the relation on typed answers: at a Fiat-Shamir oracle `fb` (or a ghost name `fbw` of it):
          both answers are failed attempts that are not the last (`failsAt`). Nothing is asked of
          their other hash blocks or of their chaining values. At every other oracle: no two answers
          are related
  `ruleT`   the rule: at a query to `fb t` with proof-of-work bits: `Rom.ndTest` (block 0 first; the
            rest only if it passes or the attempt is the last; then the non-adaptive choice
            `needOf nb m`). Everywhere else: `needOf nb m`
  `cSlotA`, `cSharedA`, `cProve1A`, `cPUA`, `cCBA`
      the counts: those of Compile/Batch/NeedCostP.lean (its counts are not in this library) with,
      for round i, g its `grJ` or `gr0`, moreOf g + (nb i + 1) in place of triesOf g · (nb i + 1):
      one for each attempt but the one with which the search ends
  `Spec.facF`   a condition on a scheme A: after answers related by `agF W`, C and P of A continue
                alike. Only for the schemes whose isk holds (i, seed), for `argPL` also the cache,
                and no store: `argP`, `argPL`, `prunedK` of them. The one statement here is
                `Spec.facF_PL`, for `prunedK` of `argPL`. For `argB` .. `argBKE` it is not claimed,
                and by this argument (no Lean fact) it fails: their committer returns its whole
                store in isk (Compile/Batch/Star.lean: `Ctok`), the chaining values of failed
                attempts too, so its output differs after two failed attempts with different
                chaining values

A statement that the three algorithms so meet what the step asks, C and P under the rule, V under
`needOf`, is not in this library. Statements that on every path the blocks that the rule asks for
add up to at most `cPUA` and `cCBA` are not in this library. Compile/Batch/OneCallCostS.lean proves
`costV_PU`, `costV_C` for every weight that meets `TryW` of Compile/Batch/OneCallCostW.lean; the
rule's own weight does, if the encoding splits an answer as Compile/Batch/ImplOf.lean does (`Std m`)
and under `Test0 W` (the check depends on block 0 alone): `tryW_numA`. `costV_PU` and `costV_C`
assume `W.OKG` and `NbPos W nb` (in a round with proof-of-work bits nb marks a block). Without
`NbPos` the counts at the rule's own weight would be too small by one: the rule asks for block 0 in
any case, and a final attempt would cost 1 (block 0) + 1 (the chaining value) = 2 against nb + 1 =
1.

Notation: `K`: `W.K`: an answer of `fb t` has K hash blocks (Compile/Batch/Oracles.lean); `m`: an
`OracleCoding (spec lam K L) lam` (Rom/Family.lean); `nb`: of type `Tag → ℕ → ℕ`: in `needOf`
(Compile/Batch/NeedTable.lean): "the blocks below nb t (round)"; `nbf`: of type `ℕ → ℕ`: `nb .test`,
`nb .link` or `nb .onl`; `moreOf`: "at most this many attempts after the first: 0 without
proof-of-work bits"; `triesOf`: "at most this many attempts for one Fiat-Shamir query: 1 without
proof-of-work bits" (both: Compile/Batch/Counts.lean); `tr d`: "the leaves and the inner nodes of a
tree of depth d" (Compile/Batch/NeedCostTree.lean); `costJ`, `cost0`: `tr w.depthJ`, `tr w.depth0`;
`PhK` (`.first`, `.loc`, `.shr`, `afterLo`): "where the chains are, without tokens" (both entries:
Compile/Batch/NeedCostP.lean); `p.M`: "the number of copies is M + 1" (`Params`, Compile/Star.lean).

Limits. The sums for the committers of `argP` and `argPL` and for the lazy prover of `argPL` are in
Compile/Batch/SpecOneCallL.lean, not here. Nothing about the mean. V is charged as before. Whether a
given wire record meets `Test0` is not said.
-/
import Compile.Batch.NeedO
import Compile.Batch.NeedL
import Compile.Batch.NeedCostP
import Rom.TestFirst

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.Need (needOf PhK costJ cost0 tr Std)

/-! ## 1. What a query says of its attempt -/

/-- The proof-of-work check, and whether the attempt is the last, read off the plain part of a
Fiat-Shamir query. -/
def tryInfo {lam K : ℕ} :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PlainPart s A → Option ((Blk lam K → Bool) × Bool)
  | [], _, _, z => z.elim
  | _ :: _, (_, _), (w, _), .inl (.inl α) => w.gr0.map fun g => (fun bl => g.ok (w.chal bl), decide (g.more ≤ g.get α))
  | _ :: _, (_, _), (w, _), .inl (.inr α) => w.grJ.map fun g => (fun bl => g.ok (w.chal bl), decide (g.more ≤ g.get α))
  | _ :: s, (_, A), (_, W), .inr z => tryInfo s A W z

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

def tryInfoT (W : QueryLayout lam L) :
    (t : Tag) → PlainPart (shapeOf L t) (annOf L t) → Option ((Blk lam W.K → Bool) × Bool)
  | .test => tryInfo _ _ W.T.sh
  | .link => tryInfo _ _ W.Lk.sh
  | .onl => tryInfo _ _ W.B.sh

/-- A failed attempt that is not the last. -/
def failsAt (W : QueryLayout lam L) (t : Tag) (q : FbIn lam L t) (bl : Blk lam W.K) : Bool :=
  match tryInfoT W t q.plain with
  | some x => !x.1 bl && !x.2
  | none => false

/-- The relation on typed answers. -/
def agF (W : QueryLayout lam L) : (o : OracleName) → domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop
  | .fb t, q, r, r' => failsAt W t q r.1 = true ∧ failsAt W t q r'.1 = true
  | .fbw t _, q, r, r' => failsAt W t q r.1 = true ∧ failsAt W t q r'.1 = true
  | _, _, _, _ => False

/-- The proof-of-work check depends on block 0 alone. -/
def Test0 (W : QueryLayout lam L) : Prop :=
  ∀ t z x, tryInfoT W t z = some x →
    0 < W.K ∧ ∀ bl bl' : Blk lam W.K, (∀ h : 0 < W.K, bl ⟨0, h⟩ = bl' ⟨0, h⟩) → x.1 bl = x.1 bl'

/-! ## 2. The rule -/

/-- The adaptive rule. -/
def ruleT (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) (m : OracleCoding (spec lam W.K L) lam) :
    NeedA (spec lam W.K L) lam := fun o q j acc =>
  match o, q with
  | .fb t, q =>
      match tryInfoT W t (q : FbIn lam L t).plain with
      | some x =>
        ndTest (fun b0 => x.1 fun _ => b0) x.2
          (fun j' => NeedA.ofNeed (needOf nb m) (.fb t) q j' acc) j acc
      | none => NeedA.ofNeed (needOf nb m) (.fb t) q j acc
  | o, q => NeedA.ofNeed (needOf nb m) o q j acc

/-! ## 3. The counts -/

section Counts
variable {K : ℕ}

/-- one slot with a request, from round i on -/
def cSlotA (nbf : ℕ → ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → PhK → ℕ
  | [], _, _, _, _ => 0
  | _ :: s, (a, A), (w, W), i, ph =>
      match a.kind, ph with
      | .lo, ph => (costJ w + (moreOf w.grJ + (nbf i + 1))) + cSlotA nbf s A W (i + 1) ph.afterLo
      | .sh, .loc => (costJ w + 1 + 1) + cSlotA nbf s A W (i + 1) .shr
      | .sh, ph => cSlotA nbf s A W (i + 1) ph

/-- the shared part -/
def cSharedA (nbf : ℕ → ℕ) (Ns : ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → PhK → ℕ
  | [], _, _, _, _ => 0
  | _ :: s, (a, A), (w, W), i, ph =>
      match a.kind, ph with
      | .lo, ph => cSharedA nbf Ns s A W (i + 1) ph.afterLo
      | .sh, .loc => ((Ns - 1) + cost0 w + (moreOf w.gr0 + (nbf i + 1))) + cSharedA nbf Ns s A W (i + 1) .shr
      | .sh, .shr => (cost0 w + (moreOf w.gr0 + (nbf i + 1))) + cSharedA nbf Ns s A W (i + 1) .shr
      | .sh, ph => cSharedA nbf Ns s A W (i + 1) ph

/-- In a round with proof-of-work bits nbf is at least 1 (block 0, which the rule asks for in any
case, is then one of the marked blocks). -/
def NbPosSh (nbf : ℕ → ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), i =>
    ((w.grJ.isSome = true ∨ w.gr0.isSome = true) → 1 ≤ nbf i) ∧ NbPosSh nbf s A W (i + 1)

def cProve1A (nbf : ℕ → ℕ) {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) :
    ℕ :=
  cSharedA nbf 1 Q.loc.shape Q.ann wq.sh 0 .first + cSlotA nbf Q.loc.shape Q.ann wq.sh 0 .first

end Counts

/-- `NbPosSh` for the three protocols -/
def NbPos (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) : Prop :=
  NbPosSh (nb .test) _ _ W.T.sh 0 ∧
  NbPosSh (nb .link) _ _ W.Lk.sh 0 ∧
  NbPosSh (nb .onl) _ _ W.B.sh 0

/-- the prover without queries for empty slots, a batch with n requests -/
def cPUA (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) (n : ℕ) : ℕ :=
  cSharedA (nb .onl) L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first +
    n * cSlotA (nb .onl) L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first

/-- the count for the committer -/
def cCBA (W : QueryLayout lam L) (p : Params) (nb : Tag → ℕ → ℕ) : ℕ :=
  tr W.depth + cProve1A (nb .test) W.T + (p.M + 1) * (tr W.depth + cProve1A (nb .link) W.Lk)

/-! ## 4. The statements -/

namespace Spec

/-- Under `Std m` and `Test0 W`: under the rule a failed attempt that is not the last costs exactly
one query to f. -/
def failCostsOne : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L)
      (nb : Tag → ℕ → ℕ) (m : OracleCoding (spec lam W.K L) lam),
    Std m → Test0 W →
    ∀ (t : Tag) (q : FbIn lam L t) (r : rngOf lam W.K (.fb t)),
      failsAt W t q r.1 = true → numA m (ruleT W nb m) (.fb t) q r = 1

/-- A condition on a scheme A: C and P continue alike after answers related by `agF W`.

A condition with parameters, which other statements and theorems use; it is not itself a claim. -/
def facF {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) {IVK ISK Pf : Type}
    (A : Gen.Arg (spec lam W.K L) I X Unit IVK ISK Pf) : Prop :=
  (∀ i, (A.C i).FactorsBy (agF W)) ∧ ∀ k b, (A.P k b).FactorsBy (agF W)


/-- `facF` for the scheme with the lazy prover and pruned Merkle paths, under `W.OKG`, σ.o =
`OracleName.other`. (That there is a slot comes from W.OKG.) -/
def facF_PL : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (ℓ : ℕ),
    W.OKG → σ.o = OracleName.other → facF W (prunedK W p (Seed.argPL W WP p bk σ ℓ Seed.noK))



end Spec

end Compile.Batch
