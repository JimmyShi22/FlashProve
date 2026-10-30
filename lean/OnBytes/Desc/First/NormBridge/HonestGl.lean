--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/NormBridge/HonestGl.lean: floorB_not_empty
(OnBytes/Desc/First/NormBridge/HonestRun.lean) at the reading that the library uses for the
program's field: Reading.gl, into the cubic extension Cb.Gl.E of the Goldilocks field, at the
program's own inverse of 2 (Model.Head.half), and at data made of integer streams and the library's
honest ledger (OnBytes/Desc/First/NormBridge/BridgeHonest.lean). Statements and proofs.

The three premises of floorB_not_empty that speak of the reading and the field are paid here:
  liftGl, liftGl_val: Reading.gl is onto. card_gl: the field has more than two elements.
  half_gl: 1 - h = h at the reading of the program's inverse of 2.
  floorB_not_empty_gl: at all sizes lt, lPd, NI, lNI with d <= 2^lPd and NI <= 2^lNI, at all streams
    and constants that meet the library's HonHyp at every norm and position, at any masks and any
    draws P, gam, rho, om: there are a run and a world that meet all seven premises of bridge_world.

Lemmas taken: OnBytes/Slice/Field.lean toE_ofE; OnBytes/Slice/ProgField.lean readE_inv;
OnBytes/Tie/Pv/Lookup/Ends/FoNatVal.lean ofNat_val; Cb/Gl/GlField.lean gl_card;
Cb/Pv/Head/NormGl.lean gl_two_ne_zero; Cb/Pv/Head/SquaresSum.lean one_sub_half.

Limits. Those of HonestRun.lean's head (the caller's forms are constant forms; the sumchecks' own
draws are chosen). That a given model's constants and streams meet HonHyp is not shown.
Not claimed: anything on soundness or hiding; that the prover's program sends what is written here.

-/
import OnBytes.Desc.First.NormBridge.HonestRun
import OnBytes.Desc.First.NormBridge.BridgeHonest
import OnBytes.Slice.ProgField
import OnBytes.Model.HeadHeard
import Cb.Pv.Head.NormGl

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D6.Bridge
open OnBytes OnBytes.Model
open Inst.Model (NormPar)
open Inst.Model.Ledger (HonHyp)

/-- The element whose words below the prime are read as k. -/
def liftGl (k : Cb.Gl.E) : E := E.ofTriple (Slice.ofE k)

theorem liftGl_val (k : Cb.Gl.E) : Reading.gl.val (liftGl k) = k := Slice.toE_ofE k

theorem card_gl : 2 < Fintype.card Cb.Gl.E := by
  rw [Cb.Gl.gl_card.2.1]
  exact lt_trans (by norm_num) Cb.Gl.gl_card.2.2.1

theorem half_gl : 1 - Reading.gl.val Head.half = Reading.gl.val Head.half := by
  unfold Head.half
  have hinv : Reading.gl.val (invE (ofNat 2)) = (Reading.gl.val (ofNat 2))⁻¹ :=
    Slice.readE_inv (ofNat 2)
  rw [hinv, Fo.ofNat_val, Nat.cast_ofNat]
  exact Cb.Pv.Head.one_sub_half Cb.Pv.Head.gl_two_ne_zero

/-- **The premises of bridge_world can be met together at the library's reading of the program's
field.** -/
theorem floorB_not_empty_gl (lt d NI lNI lPd : ℕ) (np : ℕ → NormPar) (b : ℕ → ℕ → ℕ → ℕ → ℤ)
    (H : ∀ i < NI, ∀ t < 2 ^ lt, HonHyp (np i) d (b i t)) (hd : d ≤ 2 ^ lPd) (hN : NI ≤ 2 ^ lNI)
    (M : Masks Cb.Gl.E) (PE : List E) (hPE : PE.length = lt) (gam : E) (rhoE : List E)
    (hrho : rhoE.length = lNI) (om : E) :
    ∃ (R : Run) (W : World Cb.Gl.E), R.PE = PE ∧ R.gam = gam ∧ R.om = om ∧
      R.zsS = rhoE ++ List.replicate lPd Head.half ++ PE ∧
      R.Shapes Reading.gl (honData Cb.Gl.E lt d NI lNI np b) lPd ∧
      R.Consts Reading.gl (honData Cb.Gl.E lt d NI lNI np b) lPd W ∧
      R.Ledger Reading.gl (honData Cb.Gl.E lt d NI lNI np b) M W ∧
      R.FormsZero Reading.gl (honData Cb.Gl.E lt d NI lNI np b) W ∧
      R.ReadsTrue Reading.gl (honData Cb.Gl.E lt d NI lNI np b) lPd W ∧
      R.Clean Reading.gl (honData Cb.Gl.E lt d NI lNI np b) lPd M W ∧
      R.Good Reading.gl (honData Cb.Gl.E lt d NI lNI np b) W :=
  floorB_not_empty card_gl Reading.gl liftGl liftGl_val (honData Cb.Gl.E lt d NI lNI np b)
    (honData_holds lt d NI lNI np b H) lPd hd hN M Head.half half_gl PE hPE gam rhoE hrho om

end D6.Bridge

#print axioms D6.Bridge.floorB_not_empty_gl
