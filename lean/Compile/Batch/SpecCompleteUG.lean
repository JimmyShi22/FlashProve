-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecCompleteUG.lean: towards completeness of the compiled scheme whose prover makes no
query for an empty slot, for wire records that may have proof-of-work bits. Statements only. (Words
of this library: lean/GLOSSARY.md.)

  `Spec.acceptsHonestBUG`   with runAllBUX (Compile/Batch/StarUX.lean): on every output of the
                            honest run with its further output, V accepts the proof of every request
                            that has a slot, unless Test, Link for the sampled copy or the slot is
                            bad (`Ref.badAt`: `none`, or a failed search)
  `Spec.lawTUG`, `Spec.lawLUG`, `Spec.lawBUG`
      with the oracle functions fixed: each of the three events of that run has, over the coins, the
      distribution of a small experiment without tokens: `RT`, `RL` (the committer is that of
      Compile/Batch/Star.lean) and `RBU` (Compile/Batch/CompleteURefDefs.lean)
  `Spec.unifBUG`   under lazily sampled oracles `RBU` returns "bad" with probability at most pO +
                   `cFail` (`RT`, `RL`: Compile/Batch/SpecCompleteG.lean)
  `Spec.completeOfUG`   these, with `Spec.unifTG` and `Spec.unifLG`
                        (Compile/Batch/SpecCompleteG.lean), together give `Spec.completeBatchUGr`
                        (Compile/Batch/SpecUGr.lean)

The hypotheses differ from statement to statement; `Spec.lawTUG` and `Spec.lawLUG` have none.
-/
import Compile.Batch.StarUX
import Compile.Batch.SpecCompleteG
import Compile.Batch.CompleteURefDefs
import Compile.Batch.SpecUGr

noncomputable section

namespace Compile.Batch
open Iop Rom Prob Ref RefU
open scoped ENNReal

/-- Under the hypotheses below, with the oracle functions fixed: on an honest key, V accepts the
proof of every request that has a slot, in an honest batch of requests in the relation made by
`PUX`, unless Test, Link for the sampled copy or the slot is bad. -/
def Spec.acceptsHonestBUG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Prop) (M : LH.Nums),
    L.PropsNoAcc Ryes Rno M → W.OKG → GrFitB W Ryes → L.onlineBatch.ann.Fmt →
    ∀ (f : Fam (spec lam W.K L)) (i : I) (b : List (X × Unit)), (∀ xw ∈ b, Ryes i xw.1) →
      ∀ z ∈ ((runAllBUX W WP p i b).runEager f).support, ∀ (a : Fin L.maxBatchSize) (x : X) (π : Prf lam L),
        (b.map Prod.fst)[a.val]? = some x → z.1.2[a.val]? = some π → z.2.badT WP = false →
        z.2.badL WP = false → z.2.badB WP a x = false → (V W p z.1.1 x π).runEager f = PMF.pure true

def Spec.lawTUG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (f : Fam (spec lam W.K L)) (i : I) (b : List (X × Unit)),
    ((runAllBUX W WP p i b).runEager f).map (fun z => z.2.badT WP) = (Ref.RT W WP p i).runEager f

def Spec.lawLUG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (f : Fam (spec lam W.K L)) (i : I) (b : List (X × Unit)),
    ((runAllBUX W WP p i b).runEager f).map (fun z => z.2.badL WP) = (Ref.RL W WP p i).runEager f

def Spec.lawBUG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params), W.OKG →
    L.onlineBatch.ann.Fmt →
    ∀ (f : Fam (spec lam W.K L)) (i : I) (b : List (X × Unit)) (a : Fin L.maxBatchSize) (x : X),
      (b.map Prod.fst)[a.val]? = some x →
      ((runAllBUX W WP p i b).runEager f).map (fun z => z.2.badB WP a x) =
        (RBU W WP p i (b.map Prod.fst) a x).runEager f

def Spec.unifBUG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Prop) (M : LH.Nums),
    L.PropsNoAcc Ryes Rno M → W.OKG → GrFitB W Ryes → WP.OK → L.onlineBatch.ann.Fmt →
    ∀ (i : I) (xs : List X) (a : Fin L.maxBatchSize) (x : X), xs[a.val]? = some x → Ryes i x →
      pr (RBU W WP p i xs a x).law {b | b = true} ≤ M.pO + cFail L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh

def Spec.completeOfUG : Prop :=
  Spec.acceptsHonestBUG → Spec.lawTUG → Spec.lawLUG → Spec.lawBUG → Spec.unifTG → Spec.unifLG →
  Spec.unifBUG → Spec.completeBatchUGr

end Compile.Batch
