-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerToyStage.lean: a guard against emptiness: a small stage "fold, then code switch" with a
real fold, at a radius not below half the distance, that meets all hypotheses of
`Spec.ldTower_stage_full` (Cb/Ld/LdTowerSumMain.lean) together (the two hypotheses themselves are
proved: `LdToy.toyStage_fold`, `LdToy.toyStage_switch`), nothing assumed beyond the hypotheses of
these two and of `Spec.ldTower_toy_stage`, with every error below the number of values of its
verifier message.

In standard terms: a small example instance of one recursion step of a proximity test (a sumcheck
that folds the word, then a switch to a new code), over the field with 101 elements.

Definitions, statement and proof.

The codes are the toy of Cb/Ld/LdRelToy.lean: Reed-Solomon of length 5 and dimension 2 over the
field with 101 elements (one message symbol, one symbol of randomness a row), distance 4, at the
radius 2 on both sides: 2 · 2 is not below 4, a word may have two codewords within the radius.
The stage (`toyStage h g R ..`), for every h and g (k = h + g variables), every finite set R of
further rows of the main table, and any two forms.
  The fold: the parameters of Cb/Ld/LdSumPackToy.lean (`toySum`): round polynomials of degree at
  most 2, challenges from the whole field, the packing into 2^h rows.
  The switch: from the three folded words side by side to one row for each coordinate of the new
  message (the three old messages, the three old encoding randomnesses, one pad entry); the standard
  maps of Cb/Ld/LdTowerToyKit.lean; one drawn position.

Main names:
  `Spec.ldTower_toy_stage`:
    the stage is a piece of a chain (the bundle `IOR.GoodT`: perfect completeness, round-by-round
    knowledge soundness with the named backward extractor, honest-verifier exact zero knowledge
    (`GoodT.exact`: `Honest.Exact`, Ior/Honest.lean); one long position of the input is needed if
    what follows needs one of the new word);
    k + 3 rounds;
    nothing is withheld, in this sense: `N.pBad = 0` (`StageFacts.pBad`,
    Cb/Ld/LdTowerToyKit.lean), with `PieceTr.noHid` (Cb/Ld/LdTowerKit.lean);
    the errors in a row, each below its number of values:
      the fold's coefficient: 2 of 101;
      round j of the sumcheck: 16 + 32 + 2 · 2 = 52 of 101 while the masks are halved,
      16 + 2 · 2 = 20 after;
      the seed of the sample: 100 times the count is at most the number of seeds;
      a position and the batching: below the number of values (the fraction 2/5 + 2/101).

Notation: `N`: in `N.pBad`: the field `N` (`IOR.Nums`) of the block `ldStageSum (toyStage ..) ..`
(`LdBlock`, Cb/Ld/LdTower.lean; `ldStageSum`, Cb/Ld/LdTowerSum.lean); the literals of
`StageFacts (toyStage ..) 4 2 2 2 1 ..`, by its binders (Cb/Ld/LdTowerToyKit.lean): d = 4, e = 2,
e' = 2, L = 2, t' = 1; `fun _ => 2`: Lst; the three `fun _ => 16`: mC, mS, mW.

Limits: no security: these are the numbers of a toy.
This file does not say that the bounds are attained.
It does not say that some word has two codewords within the radius.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerToyKit
import Cb.Ld.LdSumPackToy
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Blocks Cb.Ood

namespace LdToy
variable (h g : ℕ) (R : Type) [Fintype R] [DecidableEq R] (St StS : Type)
  (sl : Slf K St ((Fin (h + g) → Bool) × (toyLd R).J))
  (slS : Slf K StS ((Fin h → Bool) × (toyLd (PCol h g 1)).J))

instance neP5 : Nonempty P5 := inferInstanceAs (Nonempty (Fin 5))

/-- the instances that the stage asks of the fold's output code, by name -/
instance finAaS : Fintype (toySum h g R St StS sl slS).Cout.Aa :=
  inferInstanceAs (Fintype ((toyLd R).Aa ⊕ ((toyLd (PCol h g 1)).Aa ⊕ (toyLd (PCol h g 1)).Aa)))
instance decAaS : DecidableEq (toySum h g R St StS sl slS).Cout.Aa :=
  Classical.decEq _
instance neJS :
    Nonempty ((toySum h g R St StS sl slS).Cout.J ⊕ (toySum h g R St StS sl slS).Cout.Q) :=
  ⟨Sum.inl (Sum.inr (Sum.inl (plc5 h g (Sum.inr (Sum.inr ())))))⟩

/-- the coordinates of the new message = the rows of the new word -/
abbrev NwS : Type :=
  ((toySum h g R St StS sl slS).Cout.J ⊕ (toySum h g R St StS sl slS).Cout.Q) ⊕ Unit

/-- The small stage. -/
def toyStage : SumSw K P5 P5 :=
  stdStage (toySum h g R St StS sl slS) (toyLd (NwS h g R St StS sl slS))
    (toyPlace (NwS h g R St StS sl slS)) 1

end LdToy

open LdToy in
/-- All hypotheses together; every error below the number of values. (the hypotheses:
`LdToy.toyStage_fold`, `LdToy.toyStage_switch`) -/
def Spec.ldTower_toy_stage : Prop :=
  ∀ (h g : ℕ) (R : Type) [Fintype R] [DecidableEq R] (St StS : Type)
      (sl : Slf K St ((Fin (h + g) → Bool) × (toyLd R).J))
      (slS : Slf K StS ((Fin h → Bool) × (toyLd (PCol h g 1)).J)),
    StageFacts (toyStage h g R St StS sl slS) 4 2 2 2 1 (fun _ => 2) (fun _ => 16)
      (fun _ => 16) (fun _ => 16) ∧
    ¬ 2 * 2 < 4 ∧
    (toyStage h g R St StS sl slS).ts = 1 ∧
    (toyStage h g R St StS sl slS).Y.k = h + g ∧
    Fintype.card K - 1 = 100 ∧
    Nat.choose 2 2 = 1 ∧
    (toyStage h g R St StS sl slS).Y.err (fun _ => 2) (fun _ => 16) (fun _ => 16) (fun _ => 16) =
      (2, sErr (toyStage h g R St StS sl slS).Y.n (toyStage h g R St StS sl slS).Y.k
          fun i => 16 + (if i + 1 ≤ h then 16 + 16 else 0) + 2 * 2) ∧
    2 < Fintype.card K ∧
    ∀ i : ℕ, 16 + (if i + 1 ≤ h then 16 + 16 else 0) + 2 * 2 < Fintype.card K

namespace LdToy
variable (h g : ℕ) (R : Type) [Fintype R] [DecidableEq R] (St StS : Type)
  (sl : Slf K St ((Fin (h + g) → Bool) × (toyLd R).J))
  (slS : Slf K StS ((Fin h → Bool) × (toyLd (PCol h g 1)).J))

/-- the fold's own hypotheses at the toy -/
theorem toyStage_fold :
    (toyStage h g R St StS sl slS).Y.Hyp 4 2 (toyStage h g R St StS sl slS).ts (fun _ => 2)
      (fun _ => 16) (fun _ => 16) (fun _ => 16) := by
  obtain ⟨hn, hP, hQ, hC, -, hE, hv, hZk⟩ := ld_pack_toy h g R St StS sl slS
  exact ⟨hC, hE, hv, hn, hP, hQ, hZk⟩

/-- the switch's hypotheses at the toy -/
theorem toyStage_switch : ((toyStage h g R St StS sl slS).D 2).Hyp 2 2 1 := by
  obtain ⟨-, -, -, hC, -, -, -, -⟩ := ld_pack_toy h g R St StS sl slS
  obtain ⟨hL, -, -, hl, -, -, hz, -, -⟩ := ld_toy (NwS h g R St StS sl slS)
  exact std_stage_hyp (toySum h g R St StS sl slS) (toyLd (NwS h g R St StS sl slS))
    (toyPlace (NwS h g R St StS sl slS)) 1 2 2 2 1
    (ld_laws_pair K P5 _ _ hC.1.1 (ld_laws_pair K P5 _ _ hC.1.2.1 hC.1.2.2)) hL.loc hl hz

end LdToy

open LdToy in
theorem ldTower_toy_stage : Spec.ldTower_toy_stage := by
  intro h g R _ _ St StS sl slS
  obtain ⟨hn, hP, hQ, hC, -, hE, hv, hZk⟩ := ld_pack_toy h g R St StS sl slS
  obtain ⟨hL, -, -, hl, -, -, hz, -, -⟩ := ld_toy (NwS h g R St StS sl slS)
  have hK : Fintype.card K = 101 := ZMod.card 101
  have hnum : (Fintype.card P5 - 2 - 1) ^ 1 * Fintype.card K + Fintype.card P5 ^ 1 * 2 <
      Fintype.card P5 ^ 1 * Fintype.card K := by
    rw [card5, hK]
    norm_num
  refine ⟨std_stage_facts (toySum h g R St StS sl slS) (toyLd (NwS h g R St StS sl slS))
      (toyPlace (NwS h g R St StS sl slS)) 1 4 2 2 2 1 _ _ _ _
      ⟨hC, hE, hv, hn, hP, hQ, hZk⟩ hL.loc hl hz hnum,
    by norm_num, rfl, rfl, ?_, Nat.choose_self 2, rfl, ?_, fun i => ?_⟩
  · rw [hK]
  · rw [hK]
    norm_num
  · rw [hK]
    split_ifs <;> norm_num

end Cb
