-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerToyKit.lean: for toys: a stage "fold, then code switch" with standard maps, for
variable codes and an abstract field, and its counts.

In standard terms: one recursion step of a proximity test (a sumcheck that folds the word, then a
switch to a new code) in which the two seeded maps of the switch, the sample and the batching, are
fixed once (`stdZo`; `Evader.indep`). For any finite field and any codes, `std_stage_facts` gives,
under its hypotheses, `StageFacts` of the step (see its row).

Definitions, statements and proofs. A tool for guards against empty theorems; no parameter of a
protocol.

Why a file of its own: over a concrete field Lean must never compare numbers by unfolding
(cardinalities of function spaces). So everything that a toy needs of the switch's two maps is
stated and proved here, for an abstract finite field and variable codes; a toy only instantiates.

Main names (q: the number of elements of E):
  `stdZo E J₀`: the sample map: one row of independent coefficients on the entries J₀, made private
    by an onto block over one pad entry (Cb/Ld/LdSwitchPriv.lean: `boot`). Not reducible, on
    purpose.
  `stdZo_ok`, `stdZo_sim`, `stdZo_le`: it has the property of a sample map; it is private with a
    simulator, error 0; (q - 1) times its number (`err`) is at most the number of its seeds, if J₀
    is not empty.
  `stdStage Y Cnew place ts`: the stage (Cb/Ld/LdTowerSum.lean: `SumSw`): the fold Y; the switch to
    the code Cnew with one pad entry, the sample `stdZo`, ts drawn positions, independent
    coefficients for the batching.
  `StageFacts G ..`: what a guard shows of a stage G: it is a piece of a chain; k + 3 rounds; the
    errors in a row; nothing is withheld, in this sense: `N.pBad = 0`, with `PieceTr.noHid`
    (Cb/Ld/LdTowerKit.lean); the switch's first error times (q - 1) is at most (L choose 2) times
    the number of seeds; its second error is below the number of values of the verifier's message.
  `std_stage_hyp`: the switch's hypotheses (Cb/Ld/LdTower.lean: `LdSw.Hyp`) at the standard maps,
    from those on the two codes.
  `std_stage_facts`: `StageFacts` of `stdStage`, from: the fold's own hypotheses
    (Cb/Ld/LdTowerSumMain.lean: `SumPar.Hyp`, at t = ts); Cnew reads what it declares
    (`Cnew.Reads`), has lists of at most L at e' (`Cnew.ListAt e' L`), hides t' long positions
    (`Cnew.Zk t'`); and one inequality between numbers:
    (|P| - e - 1)^ts · q + |P|^ts · L < |P|^ts · q;
    P, P' and the coordinates `Y.Cout.J ⊕ Y.Cout.Q` of the fold's output code are not empty.
  `toyPlace R`: for the small Reed-Solomon code of Cb/Ld/LdRelToy.lean with rows R: each row holds
    one message symbol, so R names the coordinates of a message.

Notation:
  `G`: a stage (`SumSw`, Cb/Ld/LdTowerSum.lean);
  `d`, `e`, `e'`, `L`, `t'`: natural numbers; `Lst`, `mC`, `mS`, `mW`: functions ℕ → ℕ: the nine
    further arguments of `StageFacts`;
  in `std_stage_facts`: they stand in `Y.Hyp d e ts Lst mC mS mW` (`SumPar.Hyp`,
    Cb/Ld/LdTowerSumMain.lean: its head tells these letters), `Cnew.ListAt e' L` and `Cnew.Zk t'`
    (Cb/Ld/LdRel.lean);
  `N`: in `N.pBad`: the field `N` (`IOR.Nums`) of the block `ldStageSum G ..` (`LdBlock`,
    Cb/Ld/LdTower.lean; `ldStageSum`, Cb/Ld/LdTowerSum.lean).

Limits: the standard maps are no proposal for a protocol (the seeds of `stdZo` are as long as the
message).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerSumMain
import Cb.Ld.LdSwitchPrivProofs
import Cb.Gen.BatEvaderProofs
import Cb.Ld.LdRelProofsCode
import Cb.Ld.LdRelToy
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Blocks Cb.Ood

/-! ## The sample -/

section Std
variable (E J₀ : Type) [Field E] [Fintype E] [Fintype J₀] [DecidableEq J₀]

instance ontoUnit : Nonempty (OntoMx E Unit Unit) := (ldPriv_nonempty E Unit Unit).2 le_rfl

/-- One row of independent coefficients, made private by an onto block over one pad entry. -/
def stdZo : Sample E (J₀ ⊕ Unit) := (Sample.one (Evader.indep E J₀)).boot Unit

theorem stdZo_ok : (stdZo E J₀).OK :=
  ldPriv_ok_boot E J₀ Unit (Sample.one (Evader.indep E J₀)) (ood_ok_one E J₀ _ (ok_indep E J₀))

theorem stdZo_sim : (stdZo E J₀).PrivateSim E :=
  ldPriv_sim_boot E J₀ Unit (Sample.one (Evader.indep E J₀))

theorem stdZo_card :
    Fintype.card (stdZo E J₀).D =
      Fintype.card E ^ Fintype.card J₀ * Fintype.card (OntoMx E Unit Unit) := by
  show Fintype.card ((J₀ → E) × OntoMx E Unit Unit) = _
  rw [Fintype.card_prod, Fintype.card_fun]

theorem stdZo_le [Nonempty J₀] :
    (stdZo E J₀).err * (Fintype.card E - 1) ≤ Fintype.card (stdZo E J₀).D := by
  have hJ : 1 ≤ Fintype.card J₀ := Fintype.card_pos
  have hf : (stdZo E J₀).err * (Fintype.card E ^ Fintype.card Unit - 1) ≤
      max (Fintype.card E ^ (Fintype.card J₀ - 1) * (Fintype.card E ^ Fintype.card Unit - 1))
          (Fintype.card (J₀ → E)) *
        Fintype.card (OntoMx E Unit Unit) :=
    ldPriv_frac_boot E J₀ Unit (Sample.one (Evader.indep E J₀))
  rw [Fintype.card_unit, pow_one, Fintype.card_fun] at hf
  rw [stdZo_card]
  refine hf.trans (Nat.mul_le_mul_right _ (max_le ?_ le_rfl))
  calc
    Fintype.card E ^ (Fintype.card J₀ - 1) * (Fintype.card E - 1) ≤
        Fintype.card E ^ (Fintype.card J₀ - 1) * Fintype.card E :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = Fintype.card E ^ (Fintype.card J₀ - 1 + 1) := (pow_succ _ _).symm
    _ = Fintype.card E ^ Fintype.card J₀ := by rw [Nat.sub_add_cancel hJ]

instance stdZo_decS : DecidableEq (stdZo E J₀).S := inferInstanceAs (DecidableEq Unit)

end Std

/-! ## The stage -/

section Stage
variable {E P P' : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P]

/-- The stage with standard maps. -/
def stdStage (Y : SumPar E P) [Fintype Y.Cout.Aa] [DecidableEq Y.Cout.Aa]
    (Cnew : LdCode E P') (place : (Y.Cout.J ⊕ Y.Cout.Q) ⊕ Unit ≃ Cnew.J) (ts : ℕ) :
    SumSw E P P' where
  Y := Y
  Cnew := Cnew
  Qo := Unit
  place := place
  Zo := stdZo E (Y.Cout.J ⊕ Y.Cout.Q)
  ts := ts
  Zb := Evader.indep E (LdRow (stdZo E (Y.Cout.J ⊕ Y.Cout.Q)).S ts Y.Cout.Aa)

variable [Fintype P'] [Nonempty P']

/-- What a guard shows of a stage. -/
structure StageFacts (G : SumSw E P P') (d e e' L t' : ℕ) (Lst mC mS mW : ℕ → ℕ) : Prop where
  ok     : (ldStageSum G e (G.Y.ext d) Lst mC mS mW e' L t').OK G.ts t'
  rounds : (ldStageSum G e (G.Y.ext d) Lst mC mS mW e' L t').R.shape.length = G.Y.k + 3
  err    : (ldStageSum G e (G.Y.ext d) Lst mC mS mW e' L t').N.err =
    Err.app (t := (G.D e).sh) (G.Y.err Lst mC mS mW) ((G.D e).W.err1 L, ((G.D e).W.err2 e L, ()))
  pBad   : (ldStageSum G e (G.Y.ext d) Lst mC mS mW e' L t').N.pBad = 0
  small1 : (G.D e).W.err1 L * (Fintype.card E - 1) ≤ L.choose 2 * Fintype.card (G.D e).Zo.D
  small2 : (G.D e).W.err2 e L < Fintype.card (G.D e).W.Ch2

/-- a count: the two terms of the switch's second error against the number of values -/
theorem std_count (a N L q r : ℕ) (hr : 1 ≤ r) (hq : 0 < q) (h : a * q + N * L < N * q) :
    a * q ^ r + N * (L * q ^ (r - 1)) < N * q ^ r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  calc a * (q ^ s * q) + N * (L * q ^ s) = (a * q + N * L) * q ^ s := by ring
    _ < (N * q) * q ^ s := (Nat.mul_lt_mul_right (pow_pos hq s)).2 h
    _ = N * (q ^ s * q) := by ring

omit [Nonempty P'] in
/-- the switch's hypotheses at the standard maps -/
theorem std_stage_hyp (Y : SumPar E P) [Fintype Y.Cout.Aa] [DecidableEq Y.Cout.Aa]
    (Cnew : LdCode E P') (place : (Y.Cout.J ⊕ Y.Cout.Q) ⊕ Unit ≃ Cnew.J) (ts e e' L t' : ℕ)
    (hCL : Y.Cout.Laws) (hR : Cnew.Reads) (hl : Cnew.ListAt e' L) (hz : Cnew.Zk t') :
    ((stdStage Y Cnew place ts).D e).Hyp e' L t' :=
  ⟨hCL, hR, hl, stdZo_ok E (Y.Cout.J ⊕ Y.Cout.Q),
    ok_indep E (LdRow (stdZo E (Y.Cout.J ⊕ Y.Cout.Q)).S ts Y.Cout.Aa),
    stdZo_sim E (Y.Cout.J ⊕ Y.Cout.Q), hz⟩

theorem std_stage_facts (Y : SumPar E P) [Fintype Y.Cout.Aa] [DecidableEq Y.Cout.Aa]
    [Nonempty (Y.Cout.J ⊕ Y.Cout.Q)] (Cnew : LdCode E P')
    (place : (Y.Cout.J ⊕ Y.Cout.Q) ⊕ Unit ≃ Cnew.J) (ts : ℕ) (d e e' L t' : ℕ)
    (Lst mC mS mW : ℕ → ℕ) (hY : Y.Hyp d e ts Lst mC mS mW) (hR : Cnew.Reads)
    (hl : Cnew.ListAt e' L) (hz : Cnew.Zk t')
    (hn : (Fintype.card P - e - 1) ^ ts * Fintype.card E + Fintype.card P ^ ts * L <
      Fintype.card P ^ ts * Fintype.card E) :
    StageFacts (stdStage Y Cnew place ts) d e e' L t' Lst mC mS mW := by
  have hCL : Y.Cout.Laws :=
    ld_laws_pair E P _ _ hY.codes.1.1 (ld_laws_pair E P _ _ hY.codes.1.2.1 hY.codes.1.2.2)
  have hD : ((stdStage Y Cnew place ts).D e).Hyp e' L t' :=
    std_stage_hyp Y Cnew place ts e e' L t' hCL hR hl hz
  obtain ⟨h1, h2, h3, h4⟩ :=
    ldTower_stage_full E P P' (stdStage Y Cnew place ts) d e Lst mC mS mW e' L t' hY hD
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · show L.choose 2 * (stdZo E (Y.Cout.J ⊕ Y.Cout.Q)).err * (Fintype.card E - 1) ≤
      L.choose 2 * Fintype.card (stdZo E (Y.Cout.J ⊕ Y.Cout.Q)).D
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (stdZo_le E _)
  · show (Fintype.card P - e - 1) ^ ts *
          Fintype.card (LdRow (stdZo E (Y.Cout.J ⊕ Y.Cout.Q)).S ts Y.Cout.Aa → E) +
        Fintype.card P ^ ts *
          (L * Fintype.card
              E ^ (Fintype.card (LdRow (stdZo E (Y.Cout.J ⊕ Y.Cout.Q)).S ts Y.Cout.Aa) - 1)) <
      Fintype.card ((Fin ts → P) × (LdRow (stdZo E (Y.Cout.J ⊕ Y.Cout.Q)).S ts Y.Cout.Aa → E))
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
    exact std_count _ _ L _ _ (Fintype.card_pos_iff.2 ⟨Sum.inl ()⟩) Fintype.card_pos hn

end Stage

/-! ## The small Reed-Solomon code: the names of the coordinates of a message -/

namespace LdToy

theorem msg5 : C5.msg = 1 := rfl

/-- each row holds one message symbol -/
def toyPlace (R : Type) [Fintype R] [DecidableEq R] : R ≃ (toyLd R).J where
  toFun r := ⟨(), (r, ⟨0, by rw [msg5]; exact Nat.one_pos⟩)⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, r, i⟩
    have hi : i.val = 0 := by
      have h : i.val < 1 := i.2
      omega
    exact congrArg (fun j => (⟨(), (r, j)⟩ : (toyLd R).J)) (Fin.ext hi.symm)

end LdToy
end Cb
