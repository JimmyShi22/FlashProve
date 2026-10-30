-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerSumMain.lean: "fold, then code switch" and the tower of two stages, with no hypothesis
but the blocks' own.

In standard terms: one recursion step of a proximity test beyond unique decoding (a sumcheck that
folds the word, then a switch to a new code), and a test of two such steps and a base case.
Cb/Ld/LdTowerSum.lean and Cb/Ld/LdTowerTwo.lean take the fold's bundle as a hypothesis (`SumGood`).
Here it is put in: Cb/Ld/LdSumMain.lean: `ld_sum_good`, with the fold's own backward extractor
`Y.ext d` (`SumPar.ext`, Cb/Ld/LdSumKnow.lean).

Definitions, statements (a `Prop` in `Cb.Spec` each, but for `sumGood_of_hyp`) and proofs (each
applies one theorem of another file). The sets of long positions are not empty (`[Nonempty P]`) in
all statements.

Main names:
  `SumPar.Hyp` (written `Y.Hyp d e t Lst mC mS mW`): the fold's own hypotheses
    (Cb/Ld/LdSumMain.lean): the three codes have their laws and, under their transformations, a
    distance d above the radius e; Lst, mC, mS, mW bound the lists and the exceptional values of the
    k + 1 stages of the fold (`SumPar.stage`, Cb/Ld/LdSum.lean: the three tables after j rounds) at
    e (exactly: `SumPar.ErrOK`, Cb/Ld/LdSum.lean); challenges are distinct field elements; degree at
    least 2; the law of the packing and the degrees of its weights; the encoding of the fresh mask
    table hides t long positions.
  `Spec.ldTower_stage_full`: under `Y.Hyp` at t = the switch's number of positions and the switch's
    hypotheses (Cb/Ld/LdTower.lean: `LdSw.Hyp`), of the stage "fold, then code switch", in the order
    of the statement's four conjuncts:
    (1) the stage is a piece of a chain from (main table and carried mask, rows on the cubes; a pair
    of forms; radius e) to (the new code; the batched form; radius e'): the bundle `IOR.GoodT` with
    the extractor "cut the new message, then the fold's";
    (2) k + 3 rounds;
    (3) the errors in a row;
    (4) nothing is withheld, in this sense: `pBad` = 0, with `PieceTr.noHid` (Cb/Ld/LdTowerKit.lean;
    it lies inside (1)): completeness is perfect;
    and, inside (1): honest-verifier exact zero knowledge (`Honest.Exact`, Ior/Honest.lean): what
    follows may read t' long positions of the new word; the simulator is given as many long
    positions of the input as the switch draws in this sense:
    `(ldStageSum G e (G.Y.ext d) Lst mC mS mW e' L t').OK G.ts t'` (`LdBlock.OK`,
    Cb/Ld/LdTower.lean; that this is on what the simulator is given: by the definition `IOR.need`,
    Ior/Bears.lean).
  `Spec.ldTower_two_full`: the tower of two stages and the base case (Cb/Ld/LdTowerTwo.lean), from
    the five blocks' own hypotheses: it is OK, so it has all that `Spec.ldTower_end` says.

Limits: what the heads of Cb/Ld/LdTower.lean, Cb/Ld/LdTowerSum.lean, Cb/Ld/LdSumMain.lean,
Cb/Ld/LdSwitch.lean and Cb/Ld/LdBase.lean list as not said is not said here either. `SumGood`, a
hypothesis in Cb/Ld/LdTowerSum.lean, is proved here from `SumPar.Hyp` (`sumGood_of_hyp`).
e, e' may lie beyond half the distances: e has to be below the distance d of the stage's three codes
as they are read (`LdCode.Dist`, Cb/Ld/LdRel.lean); e' is any number (the next block says what it
asks of it).
This file does not say that the hypotheses can be met together. Toys for the stage are in other
files; this library has no instance of `TwoPar`.
The bounds Lst, mC, mS, mW, L, bad, L2 on lists and agreement are hypotheses: no bound on a list or
on agreement is proved here for any code.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerTwo
import Cb.Ld.LdSumMain
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-- The fold's own hypotheses. -/
structure SumPar.Hyp {E P : Type} [Field E] [Fintype E] [Fintype P] (Y : SumPar E P)
    (d e t : ℕ) (Lst mC mS mW : ℕ → ℕ) : Prop where
  codes : Spec.CodesOK E P Y.C Y.Z Y.Zw d e
  errs  : Y.ErrOK e Lst mC mS mW
  inj   : Function.Injective Y.val
  deg   : 2 ≤ Y.n
  pack  : Y.PackOK
  qw    : Y.QwDeg
  zk    : Y.Cw.Zk t

/-- the fold's bundle, from its own hypotheses (P not empty) -/
theorem sumGood_of_hyp {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P)
    (d e t : ℕ) (Lst mC mS mW : ℕ → ℕ) (h : Y.Hyp d e t Lst mC mS mW) :
    SumGood Y e (Y.ext d) t Lst mC mS mW :=
  ld_sum_good E P Y d e t Lst mC mS mW h.codes h.errs h.inj h.deg h.pack h.qw h.zk

namespace Spec

/-- Fold, then code switch: from the two blocks' own hypotheses. -/
def ldTower_stage_full : Prop :=
  ∀ (E P P' : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (G : SumSw E P P') (d e : ℕ) (Lst mC mS mW : ℕ → ℕ) (e' L t' : ℕ),
    G.Y.Hyp d e G.ts Lst mC mS mW → (G.D e).Hyp e' L t' →
    (ldStageSum G e (G.Y.ext d) Lst mC mS mW e' L t').OK G.ts t' ∧
    (ldStageSum G e (G.Y.ext d) Lst mC mS mW e' L t').R.shape.length = G.Y.k + 3 ∧
    (ldStageSum G e (G.Y.ext d) Lst mC mS mW e' L t').N.err =
      Err.app (t := (G.D e).sh) (G.Y.err Lst mC mS mW)
        ((G.D e).W.err1 L, ((G.D e).W.err2 e L, ())) ∧
    (ldStageSum G e (G.Y.ext d) Lst mC mS mW e' L t').N.pBad = 0

end Spec

theorem ldTower_stage_full :
    Spec.ldTower_stage_full := fun E P P' _ _ _ _ _ _ G d e Lst mC mS mW e' L t' hY hD =>
  ldTower_stage_sum E P P' G e (G.Y.ext d) Lst mC mS mW e' L t'
    (sumGood_of_hyp G.Y d e G.ts Lst mC mS mW hY) hD

/-- the numbers of a tower of two stages, with the folds' own extractors at the thresholds d₁, d₂ -/
def TwoPar.nums {E P₁ P₂ P₃ : Type} [Field E] [Fintype E] [Fintype P₁] [Nonempty P₁]
    [Fintype P₂] [Nonempty P₂] [Fintype P₃] [Nonempty P₃] (V : TwoPar E P₁ P₂ P₃) (d₁ d₂ : ℕ)
    (Lst₁ mC₁ mS₁ mW₁ Lst₂ mC₂ mS₂ mW₂ : ℕ → ℕ) (L₁ L₂ d bad L2 : ℕ) : TwoNums V :=
  ⟨V.Y₁.ext d₁, V.Y₂'.ext d₂, Lst₁, mC₁, mS₁, mW₁, Lst₂, mC₂, mS₂, mW₂, L₁, L₂, d, bad, L2⟩

/-- The tower of two stages: from the five blocks' own hypotheses. -/
def Spec.ldTower_two_full : Prop :=
  ∀ (E P₁ P₂ P₃ : Type) [Field E] [Fintype E] [Fintype P₁] [Nonempty P₁] [Fintype P₂] [Nonempty P₂]
      [Fintype P₃] [Nonempty P₃] (V : TwoPar E P₁ P₂ P₃) (d₁ d₂ : ℕ)
      (Lst₁ mC₁ mS₁ mW₁ Lst₂ mC₂ mS₂ mW₂ : ℕ → ℕ) (L₁ L₂ d bad L2 : ℕ),
    V.Y₁.Hyp d₁ V.e₁ V.ts₁ Lst₁ mC₁ mS₁ mW₁ → V.D₁.Hyp V.e₂ L₁ V.ts₂ →
    V.Y₂'.Hyp d₂ V.e₂ V.ts₂ Lst₂ mC₂ mS₂ mW₂ → V.D₂.Hyp V.e₃ L₂ V.t₃ →
    (V.D₂.jOut V.e₃).BaseHyp d bad L2 →
    (twoTower V (V.nums d₁ d₂ Lst₁ mC₁ mS₁ mW₁ Lst₂ mC₂ mS₂ mW₂ L₁ L₂ d bad L2)).OK ∧
    (twoTower V (V.nums d₁ d₂ Lst₁ mC₁ mS₁ mW₁ Lst₂ mC₂ mS₂ mW₂ L₁ L₂ d bad L2)).q = V.ts₁ ∧
    (twoTower V
        (V.nums d₁ d₂ Lst₁ mC₁ mS₁ mW₁ Lst₂ mC₂ mS₂ mW₂ L₁ L₂ d bad L2)).toEnd.R.shape.length =
      (V.Y₁.k + 3) + (V.Y₂.k + 3) + 2

theorem ldTower_two_full : Spec.ldTower_two_full := fun E P₁ P₂ P₃ _ _ _ _ _ _ _ _ V d₁ d₂ Lst₁ mC₁ mS₁ mW₁ Lst₂ mC₂ mS₂ mW₂ L₁ L₂ d bad L2 h1 h2 h3 h4 h5 =>
  ldTower_two E P₁ P₂ P₃ V (V.nums d₁ d₂ Lst₁ mC₁ mS₁ mW₁ Lst₂ mC₂ mS₂ mW₂ L₁ L₂ d bad L2)
    ⟨sumGood_of_hyp V.Y₁ d₁ V.e₁ V.ts₁ Lst₁ mC₁ mS₁ mW₁ h1, h2,
      sumGood_of_hyp V.Y₂' d₂ V.e₂ V.ts₂ Lst₂ mC₂ mS₂ mW₂ h3, h4, h5⟩

end Cb
