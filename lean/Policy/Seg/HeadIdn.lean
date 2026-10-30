-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/HeadIdn.lean

The values of the 21 identities of Policy/Seg/Head.lean: two statements of
Policy/Seg/HeadSteps.lean, `headPol_idn_val` and `headPol_led_val`, with their proofs.

The 17 identities of the final normalisation are the plain head's families, and `Plain.idn`
(Cm/Head.lean) has the body of `Head.N.idn` (Inst/Model/Head/TraceN.lean): their values come from
`TS.head_idn_val` (Cm/TargetSegHeadProofs.lean). Of the ledger's four, (Z) has a sum atom over 2^18
inner vertices, of which the 202,048 tokens are live (`val_exIn`, `sum_exIn`); (B2) and (B3) have
one each over the 2^10 positions. `val_jB4`, `val_jZ`: at the vertex i < `Head.nT` the values are
`Head.dB4`, `Head.dZ`. `val_sB2`, `val_sB3`: at the vertex 0 they are `Head.sB2`, `Head.sB3`.

Limits: nothing on well-formedness, on places, on the keys, or on the assembly.
-/
import Policy.Seg.HeadForms

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Finset Cm.Seg Cm.Seg.Ex

/-! ## The 17 identities of the final normalisation -/

theorem headPol_idn_val : Spec.headPol_idn_val := fun np k x W A i hi =>
  TS.head_idn_val np k x W A i hi

/-! ## The ledger's four identities -/

section Ledger
variable (pol : AcceptancePolicy) (x : XI) (W : ℕ → ℕ → Gl.F) (A : ℕ → ℕ → ℕ → Gl.E)

/-- (B4): at the vertex of a position the family's value is `Head.dB4`. -/
theorem val_jB4 {i : ℕ} (hi : i < Head.nT) :
    (jB4Fam pol).val TS.fmtRef x W A i = Head.dB4 (TS.tH A) (Head.Req.of pol x) i := by
  have e1 : vi i = i := Nat.mod_eq_of_lt hi
  unfold jB4Fam jB4Ex Head.dB4
  rw [fam_val, val1_sc, val1_sub, val1_aff, val1_con, val_add, e1, val_cHidC, val_cHidK,
    rhoCP_pos pol x hi]
  rfl

/-- The form under the sum of (Z): `Head.ex` at a token, 0 at a dead inner vertex. -/
theorem val_exIn {i j : ℕ} (hi : i < 1024) (hj : j < 2 ^ 18) :
    (exIn (i * 2 ^ 18 + j)).val A = if j < 202048 then Head.ex (TS.tH A) j i else 0 := by
  have a1 : (i * 2 ^ 18 + j) % 2 ^ 18 = j := by ar
  have a2 : (i * 2 ^ 18 + j) / 2 ^ 18 % 2 ^ 10 = i := by ar
  unfold exIn
  rw [a1, a2]
  split_ifs
  · exact val_cEx A j i
  · exact val_cK A 0

/-- The sum atom of (Z): the dead inner vertices add nothing. -/
theorem sum_exIn {i : ℕ} (hi : i < 1024) :
    ∑ j ∈ range (2 ^ 18), Ex0.val TS.fmtRef x W A (aff0 exIn) (10 + 18) (i * 2 ^ 18 + j) =
      ∑ v ∈ range Head.nV, Head.ex (TS.tH A) v i := by
  have key : ∀ j < 2 ^ 18,
      Ex0.val TS.fmtRef x W A (aff0 exIn) (10 + 18) (i * 2 ^ 18 + j) =
        if j < 202048 then Head.ex (TS.tH A) j i else 0 := fun j hj => by
    rw [val0_aff, val_exIn A hi hj]
  rw [sum_congr rfl fun j hj => key j (mem_range.1 hj)]
  rw [sum_range_dead (d := 202048) (by norm_num) _ fun j h1 _ => if_neg (not_lt.2 h1)]
  exact sum_congr rfl fun j hj => if_pos (mem_range.1 hj)

/-- (Z): at the vertex of a position the family's value is `Head.dZ`. -/
theorem val_jZ {i : ℕ} (hi : i < Head.nT) :
    jZFam.val TS.fmtRef x W A i = Head.dZ (TS.tH A) (Head.Req.of pol x) i := by
  have e1 : vi i = i := Nat.mod_eq_of_lt hi
  unfold jZFam jZEx Head.dZ
  rw [fam_val, val1_sc, val1_sub, val1_add, val1_aff, val1_sumA, val1_con, sum_exIn x W A hi, e1,
    val_cHidS, rhoCP_pos pol x hi]

/-- (B2): at its one vertex the family's value is `Head.sB2`. -/
theorem val_sB2 :
    (sB2Fam pol).val TS.fmtRef x W A 0 = Head.sB2 (TS.tH A) (Head.Req.of pol x) := by
  have key : ∀ j < 2 ^ 10,
      Ex0.val TS.fmtRef x W A
          (Ex.sc rhoCP
            (aff0 fun b' =>
              cHid 99 5 (vi b') + ((pol.C : ℕ) : Gl.E) • cHid 104 1 (vi b') + cHid 105 5 (vi b')))
          (0 + 10) (0 * 2 ^ 10 + j) =
        (((Head.Req.of pol x).rhoC j : ℤ) : Gl.E) *
          (Head.hidC (TS.tH A) j + ((pol.C : ℕ) : Gl.E) * Head.hidB (TS.tH A) j +
            Head.hidU (TS.tH A) j) := fun j hj => by
    have e1 : vi j = j := Nat.mod_eq_of_lt hj
    rw [Nat.zero_mul, Nat.zero_add j, val0_sc, val0_aff, val_add, val_add, val_smul, e1, val_cHidC,
      val_cHidB, val_cHidU, rhoCP_pos pol x hj]
  unfold sB2Fam sB2Ex Head.sB2
  rw [fam_val, val1_sub, val1_sumA, val1_pub, sum_congr rfl fun j hj => key j (mem_range.1 hj),
    (headPol_req pol x).2.2.1]
  rfl

/-- (B3): at its one vertex the family's value is `Head.sB3`. -/
theorem val_sB3 :
    (sB3Fam pol).val TS.fmtRef x W A 0 = Head.sB3 (TS.tH A) (Head.Req.of pol x) := by
  have key : ∀ j < 2 ^ 10,
      Ex0.val TS.fmtRef x W A
          (Ex.sc rhoCP (aff0 fun b' => cHid 104 1 (vi b') + cHid 115 2 (vi b')))
          (0 + 10) (0 * 2 ^ 10 + j) =
        (((Head.Req.of pol x).rhoC j : ℤ) : Gl.E) *
          (Head.hidB (TS.tH A) j + Head.hidZ (TS.tH A) j) := fun j hj => by
    have e1 : vi j = j := Nat.mod_eq_of_lt hj
    rw [Nat.zero_mul, Nat.zero_add j, val0_sc, val0_aff, val_add, e1, val_cHidB, val_cHidZ,
      rhoCP_pos pol x hj]
  unfold sB3Fam sB3Ex Head.sB3
  rw [fam_val, val1_sub, val1_sumA, val1_pub, sum_congr rfl fun j hj => key j (mem_range.1 hj),
    (headPol_req pol x).2.2.1]
  rfl

end Ledger

theorem headPol_led_val : Spec.headPol_led_val := fun pol x W A =>
  ⟨fun _ hi => ⟨val_jB4 pol x W A hi, val_jZ pol x W A hi⟩, val_sB2 pol x W A, val_sB3 pol x W A⟩

end Policy
