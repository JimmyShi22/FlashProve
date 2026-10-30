-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumKnow.lean: round-by-round knowledge soundness of the zero-knowledge sumcheck that folds
(the block `Y.ior` of Cb/Ld/LdSum.lean).

The extractor and the statement; the proof is in Cb/Ld/LdSumKnowProofs.lean.

The relations are the existential relaxations of Cb/Ld/LdRel.lean (`ConL`) at one radius e, before
and after the block: "some (message, randomness) has an encoding within e long positions of the
oracles, and its message meets the linear claim". Nothing is decoded from errors.

Main names:
  `Y.ext d`, the extractor, named, from a witness w' of the output statement, the input oracles y
  and the transcript:
    w' is read as a witness of the last stage (`LdCode.stg`, Cb/Ld/LdSumStepStage.lean: tables with
    one row);
    the rounds of the sumcheck are undone from the last to the first (`HChain.backAll` of
    Cb/Ld/LdSumStepChain.lean): in each, the word before the round is computed from y, the fresh
    mask oracle and the challenges; the set of long positions on which its fold agrees with the
    encoding of the witness so far is taken; the erasures of both halves are corrected on that set,
    and the two results are joined;
    at the end the part of the fresh mask is dropped.
    d is a number at or below the distances of the codes (Limits, (a)); it is the threshold of the
    corrector.
  `Spec.ld_sum_know`: let the three codes have their laws and the distance d > e, let the numbers
    Lst, mC, mS, mW bound lists and exceptional values as `Y.ErrOK` says, let the map from
    challenges to E be injective, 2 ≤ n, and let the public weights of the hiding polynomial have
    the degrees of `Y.QwDeg`. Then `Y.ior` is round-by-round knowledge sound with this extractor and
    the errors `Y.err`: round of the coefficient: the list of the complex with the fresh mask; round
    j: the agreement counts of the tables after the round (the masks' only while they are halved) +
    the list of the complex before the round times n.
    Round-by-round knowledge soundness (`Know`), at a list of errors, asks: on every input statement
    of a given set the prover has lost from the start towards this property: whenever the verifier
    outputs a statement, the given extractor turns each witness of it in the output relation into a
    witness of the input statement in the input relation. Here it is the conclusion of
    `Spec.ld_sum_know`, at the set of all statements (`fun _ => True`).
    A list of errors (`Err`) holds one number for each round, a count, not a probability: how many
    values of that round's verifier message may let a prover that has lost (`Doomed`) escape.

Limits:
Declared differences (two narrowings).
 (a) One number d lies below the distances of ALL THREE codes as they are read, also when the masks
     have no variable (h = 0); the paper that this protocol builds on (lean/CREDITS.md) asks nothing
     of the fresh mask's reading in that case.
 (b) "Distance" is `LdCode.Dist`: what is read of an encoding determines (message, randomness). So
     the extractor needs no further correction of the two halves (the head of Cb/Ld/LdSumStep.lean,
     Limits).
The law of the packing (`Y.PackOK`) is not asked: a cheating prover's fresh mask is any word, and
the claim speaks of any table.
No bound on lists or agreement is proved or assumed here: such bounds are hypotheses of
`Spec.ld_sum_know` (`Y.ErrOK`). This file says nothing on running time. It says nothing on
completeness and zero knowledge: Cb/Ld/LdSumAcc.lean, Cb/Ld/LdSumZk.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumClaimY
import Cb.Ld.LdSumStepClosed
import Cb.Ld.LdSumStepCoeff
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop LdCode

namespace SumPar
variable {E P : Type} [Field E] (Y : SumPar E P)

/-- a stage of this block -/
abbrev sg (k h : ℕ) : LdCode E P := stg Y.C Y.Z Y.Zw k h

/-- a point of the chain of rounds, from the challenges -/
def chPt : (k h : ℕ) → HPt (sVars E Y.n k) → (stgChain Y.C Y.Z Y.Zw k h).Pt
  | 0, _, _ => ()
  | k + 1, h, γ => (γ.1, chPt k (h - 1) γ.2)

/-- the word after the round of the coefficient: the input oracles and the fresh mask -/
def word0 (y : Y.Cin.Word) (z : Y.Cw.Word) : (Y.sg Y.k Y.h).Word :=
  mkW (C₁ := Y.C.il (Fin Y.k → Bool))
    (C₂ := (Y.Z.il (Fin Y.h → Bool)).pair (Y.Zw.il (Fin Y.h → Bool))) (fstW y)
    (mkW (C₁ := Y.Z.il (Fin Y.h → Bool)) (C₂ := Y.Zw.il (Fin Y.h → Bool)) (sndW y) z)

/-- the renaming from the last stage's code to the code of the output statement (`Y.Cout`) -/
def lastN : Rename (Y.sg 0 (endH Y.k Y.h)) Y.Cout :=
  Rename.last Y.C Y.Z Y.Zw (ldh_endH Y.k Y.h (Nat.le_add_right Y.h Y.g))

variable [Fintype E] [Fintype P]

/-- The extractor. -/
def ext (d : ℕ) (a : Y.Xi × Y.Cin.Word) (τ : Tr Y.ior.shape) (w' : Y.Cout.N.Wit) :
    Y.Cin.N.Wit :=
  dropM (D₁ := Y.C.il (Fin Y.k → Bool))
    (D₂ := Y.Z.il (Fin Y.h → Bool)) (W := Y.Zw.il (Fin Y.h → Bool))
    ((stgChain Y.C Y.Z Y.Zw Y.k Y.h).backAll
      d (Y.chPt Y.k Y.h (Y.gam τ.rho)) (Y.word0 a.2 τ.1.1) (Y.lastN.mrInv w'))

end SumPar

/-- Round-by-round knowledge soundness of the block. -/
def Spec.ld_sum_know (E P : Type) [Field E] [Fintype E] [Fintype P] : Prop :=
  ∀ (Y : SumPar E P) (d e : ℕ) (Lst mC mS mW : ℕ → ℕ), Spec.CodesOK E P Y.C Y.Z Y.Zw d e →
    Y.ErrOK e Lst mC mS mW → Function.Injective Y.val → 2 ≤ Y.n → Y.QwDeg →
    Y.ior.red.Know (fun _ => True) (ConL Y.Cin.N e Y.slIn.Holds) (ConL Y.Cout.N e Y.slOut.Holds)
      (Y.ext d) (Y.err Lst mC mS mW)

end Cb
