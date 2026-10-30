-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsFoldTestCore.lean: the field `keyArm` of `CoreArmsD` (Johnson/Top/OnFilesArmsD.lean:
the bound on the input's check of the key file, among the named hypotheses of `verify_sound_arms_D`,
whose promises read a public reading's value), from a bound on the key's check that asks for its
public digests itself. That bound is a hypothesis here.

What this file states. `keyArm_of_test`: at every b whose type of digests, reading and word are D,
"Pub at every key" and `wordAt m`: the field `keyArm`. `wordAt m`: the word under a root, read at d
off a log of strings: through the coding at d. `ZKCP.Gen.ArmBoundD.weakenLe`: a bound holds for
every promise that follows from its own, and for every larger ε; for arbitrary parameters; over any
family of oracles. `CoreArmsD b` requires `ArmBoundD b.rd (liftK r) (KeyHoldsD b) b.εK`. The promise
there is "the record's seed is a collision seed of the word, or word and record decode to
something". The bound of Johnson/Top/ArmsFoldTest.lean has the stronger promise `holdsTestOf`: "no
collision seed, and they decode to something". A bound for a stronger promise is one for a weaker.
The step from `armTestOf` to `liftK r` is `armBoundD_liftK` (Johnson/Top/ArmsFoldTestJoin.lean).

Under which hypotheses. b: a bound `ArmBoundD` of `armTestOf V m Pub` at an error ε; hε: ε is at
most b.εK; h: r's field `armK` is `armKOf V m Pub`.

What it does not show. The field is that of the record of hypotheses whose key holds a root and a
record alone (`CoreArmsD`); the field of the record with the public data in the key (`CoreArmsCD`)
is in Johnson/Top/ArmsFoldGuard.lean. In the passage to the weaker promise the half "no collision
seed" is dropped; the entry's check's promise in that record requires it again. One field of five:
nothing on `entryArm`, `proofArm`, `reading`, `noCoin`. The three promises of `CoreArmsD` read one
word, through `b.wordOf`: here that is the key's check's coding; that the two other checks' bounds
can be had at the same word is not shown. r and b are parameters, and that r's field `armK` is
`armKOf V m Pub` is a hypothesis. All that the heads of Johnson/Top/ArmsFoldTest.lean and
ArmsFoldTestJoin.lean do not claim.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsFoldTestJoin
import Johnson.Top.OnFilesArmsD

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec)

variable {S : OSpec} {X IVK Pf D : Type}

/-- A bound stands for every promise that follows from its own, and for every larger ε. -/
theorem ArmBoundD.weakenLe {rd : IVK → Rom.OComp S D} {v : IVK → X → Pf → Rom.OComp S Bool}
    {H H' : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε ε' : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBoundD rd v H ε) (hH : ∀ d k trC x π trP, H d k trC x π trP → H' d k trC x π trP)
    (hε : ∀ tC tP, ε tC tP ≤ ε' tC tP) : ArmBoundD rd v H' ε' := by
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_ ((h tC tP St Ct Pt hC hP).trans (hε tC tP))
  unfold Rom.Pr Rom.PrCoins
  refine MeasureTheory.lintegral_mono fun f => Prob.pr_mono _ ?_
  rintro o ⟨hb, hn⟩
  exact ⟨hb, fun hh => hn (hH _ _ _ _ _ _ hh)⟩

end ZKCP.Gen

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles

variable {r : InputArms} {Bd D : Type} {W : QueryLayout 256 (typedOracleCarrier r.L Bd r.aT r.aL)}

/-- The word under a root, read at d off a log of strings: what its one-block entries, under the
coding at d, determine. -/
def wordAt (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) (d : D)
    (tr : Trace (rom 256)) (cm : Dig 256) : Fin r.L.wordLength → r.L.Symbol :=
  extEnc W (singleTr (m d) tr) cm

/-- The field `keyArm` of `CoreArmsD`, at the data that a `BesideArmsD r` holds beside D, the
reading and the word. -/
theorem keyArm_of_test
    (V : D → OutTA 256 r.L r.aT → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool)
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) (Pub : OComp (rom 256) D)
    (h : r.armK = armKOf V m Pub) (q₀ : ℕ) (Wn : Type) (Rno : r.I → r.X → Wn → Prop)
    (εK εE εP : ℕ → ℕ → ℝ≥0∞) (x₀ : r.X) {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ => Pub) (armTestOf (X' := r.X) V m Pub)
      (holdsTestOf (W := W) m) ε) (hε : ∀ tC tP, ε tC tP ≤ εK tC tP) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftK r)
      (KeyHoldsD (r := r) ⟨D, fun _ => Pub, q₀, wordAt m, Wn, Rno, εK, εE, εP, x₀⟩) εK :=
  (armBoundD_liftK r V m Pub h b).weakenLe (fun _ _ _ _ _ _ hh => Or.inr hh.2) hε

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms ZKCP.Gen.ArmBoundD.weakenLe
#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyArm_of_test
