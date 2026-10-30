-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/AtBaseFilling.lean: kind K13, the members' batching, at the filling from which the
honest prover for a request is made, before it is read through the object's randomness: the filling
`onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest`
(E2E/TheHonestProver.lean: `onlineFilling` is that filling read through). Under the library's head h
(`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), where `onlineProverFromPublicFiles` (Johnson/Desc/ProofFile/Honest/AtPure.lean)
returns at that filling and the head's files. One statement with its proof; no definition.

  `k13_at_base_filling`   what is returned has the head's public part and description; among the
     returned prover's sides of the first chain, in their order, those at a place of the kind K13
     are just the sides of the kind's rows (`k13BaseRows`,
     Johnson/Desc/ProofFile/Honest/K13/AtBase.lean) at the filling's own reader of the index and
     filler of the pile; that is one side, the kind's (`proverSideOfClaimCombination`); the shared and the second chain
     have none; each of these rows is seated at
     the sub-protocol number 355, and every side at which it is seated meets `Good`
     (Johnson/Desc/ProofFile/Honest/Side.lean) at the returned book of coins and order of places

Limits.
  * The head h, and that `onlineProverFromPublicFiles` returns, are hypotheses.
  * That what `onlineMaker` returns is this return read through is not shown here.
  * A and B are False in the term of `Good`: `plays` and `acc` hold vacuously; `fits` and `exact`
    say something. `fresh` in that term says next to nothing: the kind's two parts own no coin
    (Johnson/Desc/ProofFile/Honest/K13/Fields.lean). All Limits of
    Johnson/Desc/ProofFile/Honest/K13/GoodRows.lean hold here: above all, that the block which the
    kind borrows is still uniform when it is spent is the condition `fresh` at its owner, and is not
    shown.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K13.AtBase
import Johnson.Desc.ProofFile.Honest.K13.GoodRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open VerifiableInference.Desc (Chain Place)
open ProofFile.Honest.K13
open P5J (TS)

variable {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The kind K13 at the filling from which the honest prover for a request is made.** -/
theorem k13_at_base_filling (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) =
        .ok A) :
    A.Z = Zp ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧
      A.H.first.filter atK13 =
        (k13BaseRows matrixInput.weights openHonest.pile Zp A.G).map (·.half) ∧
      (k13BaseRows (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) matrixInput.weights openHonest.pile Zp
          A.G).map (·.half) =
        [proverSideOfClaimCombination (matrixInput.weights Zp) (openHonest.pile Zp A.G)
          (VerifiableInference.Desc.K13.whereOf Zp)] ∧
      A.H.shared.filter atK13 = [] ∧ A.H.second.filter atK13 = [] ∧
      ∀ (fs : List (Fall TS)) (pre : List (Nat × Nat × List Fmt.DeclaredRound)),
        ∀ r ∈ k13BaseRows (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) matrixInput.weights
            openHonest.pile Zp A.G,
          (∃ σ, Side.seated cF.blocksInOrder r.place r.row fs = some σ ∧ cF.blocksInOrder[355]? = some σ.block) ∧
            ∀ σ, Side.seated cF.blocksInOrder r.place r.row fs = some σ →
              Good pre .own σ A.B (orderOf A.F) 0 0 (fun _ _ _ _ => False)
                (fun _ _ _ _ => False) r.On r.bud := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (hF.symm.trans h.laid.value)
  have e1 := k13_at_base hA
  rw [eZ] at e1
  exact ⟨eZ, eF, e1, k13SLot_halves _ _ Zp A.G, (k13_none_elsewhere h hA).1,
    (k13_none_elsewhere h hA).2, fun fs pre =>
    k13_good_rows_atPure h hA _ _ A.G pre .own _ 0 0 fs⟩

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.k13_at_base_filling
