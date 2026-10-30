-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumPackToy.lean: a small example: parameters at which all hypotheses of the statement
`Spec.ld_sum_good` (stated and proved in Cb/Ld/LdSumMain.lean) on the zero-knowledge sumcheck that
folds (Cb/Ld/LdSum.lean) hold together, nothing assumed beyond the hypotheses of `Spec.ld_pack_toy`,
at a radius not below half the distance.

Definitions, statements and proofs.

The parameters are `toySum h g R ..`, for every h and g (k = h + g variables), every finite set R
and any two forms `sl`, `slS` (`Slf`, Cb/Ld/LdRel.lean).
   The field `K` has 101 elements, and all of it is the set of challenges.
   The degree n is 2: round polynomials have degree at most 2.
   The codes are the toy of Cb/Ld/LdRelToy.lean. It is a Reed-Solomon code of length 5 and
   dimension 2, with distance 4, read as it stands (`Reading.one`, Cb/Gen/CodeRep.lean).
   The main table's code `C` has the rows R, as further rows of the main table.
   The masks' code `Z` has one row for each column of the packing,
   so that the message of the mask code has exactly k · n + 1 - h coordinates.
   The fresh mask is read as the carried one (`AaW`, `TW`, `srcW`).
   The packing is the packing into 2^h rows of Cb/Ld/LdSumPack.lean.
   The radius is 2. With distance 4 that is not below half the distance.

Main names:
  `Spec.ld_pack_toy`: at these parameters all of these hold: 2 ≤ n; the law of the packing; the
    degrees of the weights (`SumPar.QwDeg`, Cb/Ld/LdSumClaimY.lean); the laws and the distance 4 > 2
    of the three codes; the numbers of `SumPar.ErrOK`: lists of at most 2 members at every stage
    (`SumPar.stage`, Cb/Ld/LdSum.lean; the Johnson bound), at most 16 exceptional values for every
    table; the challenges are different elements of the field; the encoding of the fresh mask's
    table hides 1 long position.
  These errors come out: the round of the coefficient has the error 2, of 101 values of the
  coefficient. A round of the sumcheck has the error 16 + 32 + 2·2 = 52, of 101, while the masks are
  halved (the first h rounds), and 16 + 2·2 = 20 after.
  `Spec.ld_pack_toy_err` states of these numbers only that each round's is at most 52 and that 52
  and 2 are below the number of field elements.
  `Spec.ld_pack_toy_hon`: so the block is perfectly complete and honest-verifier exactly zero
    knowledge (`Honest.Exact`, Ior/Honest.lean; `SumPar.bud 1`, Cb/Ld/LdSum.lean) at these
    parameters (Cb/Ld/LdSumAcc.lean, Cb/Ld/LdSumZk.lean).
  `Spec.ld_pack_toy_good`: and the whole record `IOR.GoodT` (Ior/KnowCollGood.lean), in which
    `Spec.ld_sum_good` (Cb/Ld/LdSumMain.lean) ends, holds at them, with no hypothesis left beyond
    those of `Spec.ld_pack_toy_good`: round-by-round knowledge soundness at the radius 2 with the
    named backward extractor and these errors, perfect completeness, honest-verifier exact zero
    knowledge (`GoodT.exact`: `Honest.Exact`, Ior/Honest.lean).

Notation: `AaW`, `TW`, `srcW`: the transformation under which the fresh mask is read; `Zw`: the code
of the masks, under the transformation of the fresh mask: the same encoder; `Cw`: the code of the
oracle that the prover sends (`SumPar`, Cb/Ld/LdSum.lean). The literals, by the binders of the
declarations (d, e, t, Lst, mC, mS, mW: also the binders of `Spec.ld_sum_good`,
Cb/Ld/LdSumMain.lean): in `CodesOK .. 4 2`: d = 4, e = 2; in `ErrOK 2 ..` and `rels .. 2 ..`: e = 2;
in `ext 4`: d = 4; in `nums 1 ..`, `bud 1` and `Cw.Zk 1`: t = 1; `fun _ => 2`: Lst; the three
`fun _ => 16`: mC, mS, mW; in `PCol h g 1`, `pkC h g 1`, `QwC h g 1`: m = 1, where n = m + 1
(`CodesOK`: Cb/Ld/LdSumStepStage.lean; `ErrOK`, `nums`, `bud`: Cb/Ld/LdSum.lean; `ext`:
Cb/Ld/LdSumKnow.lean; `rels`, `Zk`: Cb/Ld/LdRel.lean; `PCol`, `pkC`, `QwC`: Cb/Ld/LdSumPack.lean).

Limits: this file is a guard against empty theorems; it has no parameter of a real protocol. 52 of
101 is no security.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumPackProofs
import Cb.Ld.LdSumMain
import Cb.Ld.LdRelToy
import Cb.Ld.LdRelJohnsonProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
namespace LdToy
open Iop Prob Hiop

/-- the long positions of the toy -/
abbrev P5 : Type := (Reading.one C5).P

/-- each column of the packing in its own coordinate of the mask code's message -/
def plc5 (h g : ℕ) : PCol h g 1 → (toyLd (PCol h g 1)).J := fun c =>
  ⟨(), (c, (⟨0, by decide⟩ : Fin C5.msg))⟩

/-- The parameters. -/
def toySum (h g : ℕ) (R : Type) [Fintype R] [DecidableEq R] (St StS : Type)
    (sl : Slf K St ((Fin (h + g) → Bool) × (toyLd R).J))
    (slS : Slf K StS ((Fin h → Bool) × (toyLd (PCol h g 1)).J)) : SumPar K P5 where
  h := h
  g := g
  n := 2
  Ch := K
  val := id
  C := toyLd R
  Z := toyLd (PCol h g 1)
  AaW := (toyLd (PCol h g 1)).Aa
  TW := (toyLd (PCol h g 1)).T
  srcW := (toyLd (PCol h g 1)).src
  St := St
  StS := StS
  sl := sl
  slS := slS
  pk := pkAt (plc5 h g) (pkC h g 1)
  Qw := QwAt (plc5 h g) (QwC h g 1)

end LdToy

namespace Spec
open LdToy

def ld_pack_toy : Prop :=
  ∀ (h g : ℕ) (R : Type) [Fintype R] [DecidableEq R] (St StS : Type)
      (sl : Slf K St ((Fin (h + g) → Bool) × (toyLd R).J))
      (slS : Slf K StS ((Fin h → Bool) × (toyLd (PCol h g 1)).J)),
    2 ≤ (toySum h g R St StS sl slS).n ∧
    (toySum h g R St StS sl slS).PackOK ∧
    (toySum h g R St StS sl slS).QwDeg ∧
    CodesOK K P5 (toySum h g R St StS sl slS).C (toySum h g R St StS sl slS).Z
      (toySum h g R St StS sl slS).Zw 4 2 ∧
    ¬ 2 * 2 < 4 ∧
    (toySum h g R St StS sl slS).ErrOK 2 (fun _ => 2) (fun _ => 16) (fun _ => 16) (fun _ => 16) ∧
    Function.Injective (toySum h g R St StS sl slS).val ∧
    (toySum h g R St StS sl slS).Cw.Zk 1

/-- The numbers that stand in the errors of the rounds. (What it states of them: the head.) -/
def ld_pack_toy_err : Prop :=
  ∀ i h : ℕ,
    (16 + (if i + 1 ≤ h then 16 + 16 else 0) + 2 * 2 ≤ 52) ∧
    52 < Fintype.card K ∧
    2 < Fintype.card K

def ld_pack_toy_hon : Prop :=
  ∀ (h g : ℕ) (R : Type) [Fintype R] [DecidableEq R] (St StS : Type)
      (sl : Slf K St ((Fin (h + g) → Bool) × (toyLd R).J))
      (slS : Slf K StS ((Fin h → Bool) × (toyLd (PCol h g 1)).J)),
    (toySum h g R St StS sl slS).hon.Acc
      (Con (toySum h g R St StS sl slS).Cin.N (toySum h g R St StS sl slS).slIn.Holds)
      (Con (toySum h g R St StS sl slS).Cout.N (toySum h g R St StS sl slS).slOut.Holds) ∧
    (toySum h g R St StS sl slS).hon.Exact
      (Con (toySum h g R St StS sl slS).Cin.N (toySum h g R St StS sl slS).slIn.Holds)
      ((toySum h g R St StS sl slS).bud 1)

def ld_pack_toy_good : Prop :=
  ∀ (h g : ℕ) (R : Type) [Fintype R] [DecidableEq R] (St StS : Type)
      (sl : Slf K St ((Fin (h + g) → Bool) × (toyLd R).J))
      (slS : Slf K StS ((Fin h → Bool) × (toyLd (PCol h g 1)).J)),
    Iop.IOR.GoodT (toySum h g R St StS sl slS).ior (toySum h g R St StS sl slS).hon
      ((toySum h g R St StS sl slS).Cin.rels (toySum h g R St StS sl slS).slIn 2 fun _ => ())
      ((toySum h g R St StS sl slS).Cout.rels (toySum h g R St StS sl slS).slOut 2 fun _ => ())
      ((toySum h g R St StS sl slS).ext 4)
      ((toySum h g R St StS sl slS).nums 1 (fun _ => 2) (fun _ => 16) (fun _ => 16) (fun _ => 16))

end Spec

namespace LdToy

theorem plc5_inj (h g : ℕ) : Function.Injective (plc5 h g) := fun c c' hc => by
  have h1 := congrArg (fun a : (toyLd (PCol h g 1)).J => a.2.1) hc
  exact h1

theorem card5 : Fintype.card P5 = 5 := Fintype.card_fin 5

theorem list5 (D : LdCode K P5) (hL : D.Laws) (hD : D.Dist 4) : D.ListAt 2 2 := by
  have hJ : InJohnson (Fintype.card P5) 4 2 := by
    rw [card5]
    unfold InJohnson
    norm_num
  have hl : listMax (Fintype.card P5) 4 2 = 2 := by
    rw [card5]
    unfold listMax
    norm_num
  have h := ld_list_johnson K P5 D 4 2 hL hD hJ
  rwa [hl] at h

theorem mca5 (D : LdCode K P5) (hL : D.Laws) : D.MCAat 2 16 :=
  ld_mca_mono K _ _ 2 _ 16 (le_of_eq cnt_sets) (ld_mca_sets K P5 D hL 2)

end LdToy

open LdToy in
theorem ld_pack_toy : Spec.ld_pack_toy := by
  intro h g R _ _ St StS sl slS
  obtain ⟨hCL, hCD, -, -, -, -, -, -, -⟩ := ld_toy R
  obtain ⟨hZL, hZD, -, -, -, -, hZk, -, -⟩ := ld_toy (PCol h g 1)
  have hWL : (toySum h g R St StS sl slS).Zw.Laws := hZL
  have hWD : (toySum h g R St StS sl slS).Zw.Dist 4 := hZD
  refine ⟨le_refl 2, ?_, ?_, ⟨⟨hCL, hZL, hWL⟩, ⟨hCD, hZD, hWD⟩, by norm_num⟩,
    by norm_num, ?_, fun _ _ h => h, ?_⟩
  · exact (ld_pack_ok_iff K P5 _).2
      (ld_pack_place K h g 2 _ _ (plc5 h g) _ _ (plc5_inj h g) (ld_pack_law K h g 1))
  · exact ld_pack_deg_place K _ _ _ (plc5 h g) (QwC h g 1) _ (ld_pack_deg K h g 1)
  · exact
      { list := fun j _ =>
          list5 _ (ld_laws_pair K P5 _ _ (ld_laws_il K P5 _ _ hCL)
              (ld_laws_pair K P5 _ _ (ld_laws_il K P5 _ _ hZL) (ld_laws_il K P5 _ _ hWL)))
          (ld_dist_pair K P5 _ _ 4 (ld_dist_il K P5 _ _ 4 hCD)
            (ld_dist_pair K P5 _ _ 4 (ld_dist_il K P5 _ _ 4 hZD) (ld_dist_il K P5 _ _ 4 hWD)))
        mcaC := fun j _ _ => mca5 _ (ld_laws_il K P5 _ _ hCL)
        mcaS := fun j _ _ => mca5 _ (ld_laws_il K P5 _ _ hZL)
        mcaW := fun j _ _ => mca5 _ (ld_laws_il K P5 _ _ hWL) }
  · exact ld_zk_il K P5 _ _ 1 hZk

open LdToy in
theorem ld_pack_toy_err : Spec.ld_pack_toy_err := by
  intro i h
  refine ⟨by split_ifs <;> norm_num, ?_, ?_⟩ <;>
  · rw [ZMod.card]
    norm_num

open LdToy in
theorem ld_pack_toy_hon : Spec.ld_pack_toy_hon := by
  intro h g R _ _ St StS sl slS
  obtain ⟨hn, hP, -, ⟨⟨hC, hZ, hW⟩, -, -⟩, -, -, -, hZk⟩ := ld_pack_toy h g R St StS sl slS
  exact ⟨ld_sum_acc K P5 _ hn hP hC hZ hW, ld_sum_exact K P5 _ 1 hn hZk⟩

open LdToy in
theorem ld_pack_toy_good : Spec.ld_pack_toy_good := by
  intro h g R _ _ St StS sl slS
  obtain ⟨hn, hP, hQ, hC, -, hE, hv, hZk⟩ := ld_pack_toy h g R St StS sl slS
  exact ld_sum_good K P5 _ 4 2 1 _ _ _ _ hC hE hv hn hP hQ hZk

end Cb
