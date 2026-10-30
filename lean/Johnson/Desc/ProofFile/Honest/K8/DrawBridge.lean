-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/DrawBridge.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: FROM
A YES OF THE KIND's OWN BLOCK, AND FROM THE ARRAY OF DIGITS AS IT IS MADE, TO THE PREMISES OF
Honest/K8/SmallLaw.lean; AND SO TO THE LIBRARY's TWO SENTENCES BEHIND THE DRAW, BY THEIR OWN NAMES.
STATEMENTS ALONE: definitions of type Prop. NO THEOREM HERE: the proofs are
Honest/K8/DrawBridgeProofs.lean's. LEMMAS ON THE HONEST PROVER's SIDE; NONE OF THE LIBRARY's
GOALS.

What a yes of the block of the draw means at the verifier's state is the library's
`MeansAtS p s r s'` (Johnson/Desc/First/K8/HearMeans.lean; `decide_atS_iff`: the decision says yes
just there).

  `Spec.same_of_yes`      behind a yes the state of the test has the place's numbers, and holds the
                          round's entries as the drawn matrix
  `Spec.drawLaid_of_yes`  behind a yes on a round that the frame's test on a challenge passes, at a
                          place with a matrix: `DrawLaid`: BUT FOR THE LIBRARY's TEST ON THE DIGITS'
                          COLUMNS, WHICH STAYS A PREMISE
  `Spec.inARow_of_tabs`   a list with the shapes that a place's numbers make is laid in a row
  `Spec.inARow_of_yes`    so behind a yes the closed list is
  `Spec.zzBy_of_zzOf`     a table that has `zzOf` (Honest/K8/Digits.lean), carried into the
                          extension field, in the array of digits has `ZzBy`
  **`Spec.small_at_yes`** BEHIND A YES OF THE DRAW, WHERE NO COMBINATION LEAVES ITS WINDOW, AT A
                          TABLE MADE OF THE CELLS: the library's `SmallAt` and `DigitsAt`
                          (Johnson/Desc/First/K8/LawItems.lean), under its own `Extra`
  **`Spec.small_at_silence`**   the same with "the part's second stop is silent behind its round"
                          (Honest/K8/Part.lean: `smallHid`) in the place of the window's premise
Limits. One place. THE LIBRARY's TEST ON THE DIGITS' COLUMNS AND `Extra` ARE PREMISES. That the
table of which a table of joints' items speak is made of the cells (`TieBy`, `ZzBy`) is a premise.
No frame, no message, no coin.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SmallLaw
import Johnson.Desc.K8.Honest.SameNumbers
import Johnson.Desc.First.K8.HearMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par MeansAtS tabs SmallAt DigitsAt Extra)
open VerifiableInference.Desc.First.K8.Honest

namespace Spec

/-- States: behind a yes the state of the test has the place's numbers, and holds the round's
entries as the drawn matrix. -/
def same_of_yes : Prop :=
  ∀ (p : Par) (s s' : S) (r : Fmt.RoundView) (tl' : HTailF2), MeansAtS p s r s' → s'.tl? = some tl' →
    SameNumbers (parOfTail tl') p ∧ tl'.cfF = r.drawn.trits.toArray

/-- States: behind a yes, on a round that the frame's test on a challenge passes, at a place with a
matrix, the draw is laid; the library's test on the digits' columns stays a premise. -/
def drawLaid_of_yes : Prop :=
  ∀ (p : Par) (s s' : S) (r : Fmt.RoundView) (tl' : HTailF2), MeansAtS p s r s' →
    drawFit (VerifiableInference.Desc.First.K8.round p) r.drawn = true → p.ks ≠ [] →
    s'.tl? = some tl' → DgP.colsTest tl' = true → DrawLaid tl'

/-- States: a list with the shapes that a place's numbers make is laid in a row from entry 0 on, at
every numbers that are alike in the matrices' columns and rows. (Of `SameNumbers` the number of
combinations is not spent.) -/
def inARow_of_tabs : Prop :=
  ∀ (p q : Par) (fs : List HFun), SameNumbers q p →
    (fs.map fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p → inARow q 0 fs = true

/-- States: behind a yes the closed list is laid in a row. -/
def inARow_of_yes : Prop :=
  ∀ (p : Par) (s s' : S) (r : Fmt.RoundView) (tl' : HTailF2), MeansAtS p s r s' → s'.tl? = some tl' →
    inARow (parOfTail tl') 0 tl'.funs.toList = true

/-- States: a table that has `zzOf`, carried into the extension field, in the array of digits. -/
def zzBy_of_zzOf : Prop :=
  ∀ (tl : HTailF2) (A : TableE) (mats : List (ℕ × String × ℕ)) (C : Cells) (trits : List ℤ),
    tl.cfF = trits.toArray →
    (∀ u, u < tl.tau → ∀ col, col < 2 * tl.mz →
      A tl.ix.ZZ u col = algebraMap Cb.Gl.F Cb.Gl.E (zzOf tl mats C trits u col)) →
    ZzBy tl A (cellsAtOf C mats)

/-- **States: behind a yes of the draw, where no combination leaves its window, at a table made of
the cells, the library's two sentences hold.** -/
def small_at_yes : Prop :=
  ∀ (W : Type) (A : W → TableE) (w : W) (p : Par) (s s' : S) (r : Fmt.RoundView) (tl' : HTailF2)
    (a : CellsAt), MeansAtS p s r s' →
    drawFit (VerifiableInference.Desc.First.K8.round p) r.drawn = true → p.ks ≠ [] →
    s'.tl? = some tl' → DgP.colsTest tl' = true → Extra s' →
    TieBy tl' (A w) a → ZzBy tl' (A w) a → leaves p a r.drawn.trits.toArray = none →
    SmallAt A s' w ∧ DigitsAt A s' w

/-- **States: the same where the part's second stop, asked behind its round, is silent**: at the
cells that the part is handed. -/
def small_at_silence : Prop :=
  ∀ (W : Type) (A : W → TableE) (w : W) (p : Par) (s s' : S) (r : Fmt.RoundView) (tl' : HTailF2)
    (v : SmallAsk) (front : List Fmt.Drawn), MeansAtS p s r s' →
    drawFit (VerifiableInference.Desc.First.K8.round p) r.drawn = true → p.ks ≠ [] →
    s'.tl? = some tl' → DgP.colsTest tl' = true → Extra s' →
    TieBy tl' (A w) v.cell → ZzBy tl' (A w) v.cell → smallHid p v front [r.drawn] = none →
    SmallAt A s' w ∧ DigitsAt A s' w

end Spec

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.Spec.same_of_yes
#print axioms ProofFile.Honest.K8.Spec.drawLaid_of_yes
#print axioms ProofFile.Honest.K8.Spec.inARow_of_tabs
#print axioms ProofFile.Honest.K8.Spec.inARow_of_yes
#print axioms ProofFile.Honest.K8.Spec.zzBy_of_zzOf
#print axioms ProofFile.Honest.K8.Spec.small_at_yes
#print axioms ProofFile.Honest.K8.Spec.small_at_silence
