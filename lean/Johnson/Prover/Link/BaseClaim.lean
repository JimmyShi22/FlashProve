-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BaseClaim.lean: from "the row that the last stage is handed is true" to the
premises of Johnson/Prover/Link/Base.lean at the claim that the last part writes out (`claimAt`,
Johnson/Desc/K12/JoinGuarded.lean).

Why. The record inside a proximity test bears a row on a group: a structured form, a vector and a
target. The base case decides on a claim that is made of it: the form written out. The law of the
base case's yes is stated at that claim.

Main names (namespace `Johnson.Prover.Link`).
  `mainOf s w`, `maskOf s w`   the last stage's message w as two functions on ℕ, 0 from the codes'
      message lengths on
  `claim_of_holds`   the row is true at w as the soundness side reads it at the last stage
      (`Slf.Holds` of `stmGk s 1 0 row`, OnBytes/Slice/BlkRead.lean): then the written claim's left
      side at (mainOf, maskOf) reads as its target
  `sizes_of_claim`   the written claim's two vectors have the codes' message lengths, where the
      main code's is a power of two and the row's vector on the mask table has the mask code's
  `lt_wr`, `lt_tauSW`   the sent elements' words are below the prime, in the form in which the test
      on a whole view asks it (`viewWordsBelowPrime`, Johnson/Desc/Block.lean)

By: `stmIn_claimAt` (Johnson/Desc/K12/Law/BaseGives.lean), an equation; `claimAt_iff`
(Johnson/Desc/K12/Law/BaseAsks.lean); `Form.writeOut_val` (OnBytes/Iop/DotLaws.lean).

Limits. That the row is true is a premise. From what a record's rows say of the prover's tables to
`Slf.Holds` at the last stage: not here. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BasePart
import Johnson.Desc.K12.Law.BaseGives
import Johnson.Desc.K12.Law.BaseAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12

/-- The last stage's main message as a function on ℕ. -/
def mainOf (s : Sg) (w : s.cIn.J → GE) (j : ℕ) : GE :=
  if h : j < s.C.l then w (.inl (fun _ => false, ⟨j, h⟩)) else 0

/-- Its mask message. -/
def maskOf (s : Sg) (w : s.cIn.J → GE) (j : ℕ) : GE :=
  if h : j < s.Z.l then w (.inr (fun _ => false, ⟨j, h⟩)) else 0

/-- **From "the row is true" to the written claim.** -/
theorem claim_of_holds (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (K : Codes) (cu : IoppStage)
    (row : GroupRow) (cl : BaseClaim) (cd : OnBytes.Code) (hcd : K.base[cu.code]? = some cd)
    (hl : cd.ell = s.C.l) (hk : cu.k = 0) (hcl : claimAt K cu row = some cl)
    (hfit : (row.c.fixLow [zeroE]).fits (ceilLog2 cd.ell) = true) (hfix : FixLaw row.c [zeroE])
    (w : s.cIn.J → GE) (hw : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmGk s 1 0 row) w) :
    formG s.C.l cl.c (mainOf s w) + formG s.Z.l cl.d (maskOf s w) = toE cl.tau := by
  rw [← H2K.JointK.stmIn_claimAt s h0 g0 K cu row cl cd hcd hl hk hcl hfit hfix] at hw
  have hk' : s.h + s.g = 0 := by omega
  have e : ∑ j : s.cIn.J, vecIn s ⟨cl.c, cl.d, cl.tau⟩ j * w j = toE cl.tau := hw
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, sum_rows0 hk',
    sum_rows0 h0] at e
  rw [← e]
  unfold formG
  rw [Finset.sum_range, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    show vec cl.c j.val * mainOf s w j.val =
      vec cl.c (Sz.rowNo (fun _ => false) + 2 ^ (s.h + s.g) * j.val) * w (.inl (fun _ => false, j))
    have ei : Sz.rowNo (fun _ : Fin (s.h + s.g) => false) + 2 ^ (s.h + s.g) * j.val = j.val := by
      rw [rowNo_zero hk', hk', pow_zero, one_mul, zero_add]
    rw [ei]
    unfold mainOf
    rw [dif_pos j.isLt]
  · refine Finset.sum_congr rfl fun j _ => ?_
    show vec cl.d j.val * maskOf s w j.val =
      vec cl.d (Sz.rowNo (fun _ => false) + 2 ^ s.h * j.val) * w (.inr (fun _ => false, j))
    have ei : Sz.rowNo (fun _ : Fin s.h => false) + 2 ^ s.h * j.val = j.val := by
      rw [rowNo_zero h0, h0, pow_zero, one_mul, zero_add]
    rw [ei]
    unfold maskOf
    rw [dif_pos j.isLt]

/-- **The two sizes.** -/
theorem sizes_of_claim (s : Sg) (K : Codes) (cu : IoppStage) (row : GroupRow) (cl : BaseClaim)
    (cd : OnBytes.Code) (hcd : K.base[cu.code]? = some cd) (hl : cd.ell = s.C.l)
    (hcl : claimAt K cu row = some cl)
    (hfit : (row.c.fixLow [zeroE]).fits (ceilLog2 cd.ell) = true)
    (hp : cd.ell = 2 ^ ceilLog2 cd.ell) (hd : row.d.size = s.Z.l) :
    cl.c.size = s.C.l ∧ cl.d.size = s.Z.l := by
  obtain ⟨c', hc', -, -, rfl⟩ := (claimAt_iff K cu row cl).1 hcl
  obtain rfl : c' = cd := Option.some.inj (hc'.symm.trans hcd)
  refine ⟨?_, ?_⟩
  · show (((row.c.fixLow [zeroE]).writeOut (ceilLog2 c'.ell)).map (·.triple)).size = _
    rw [Array.size_map, (Form.writeOut_val rdE (row.c.fixLow [zeroE]) (ceilLog2 c'.ell)
      (fun v hv => (ProxRun.fits_tensors _ _ hfit v hv).1) 0 (Nat.two_pow_pos _)).1, ← hp, hl]
  · show (row.d.map (·.triple)).size = _
    rw [Array.size_map, hd]

/-- A written element's three words are below the prime, in the form of the test on a view. -/
theorem lt_ofE (x : GE) :
    (decide ((ofE x).1 < fieldPrimeWord) && decide ((ofE x).2.1 < fieldPrimeWord) &&
      decide ((ofE x).2.2 < fieldPrimeWord)) = true := by
  simp only [ofE, lt_ofF, decide_true, Bool.and_self]

theorem lt_wr (n : ℕ) (f : ℕ → GE) : ∀ e ∈ wr n f,
    (decide (e.1 < fieldPrimeWord) && decide (e.2.1 < fieldPrimeWord) && decide (e.2.2 < fieldPrimeWord)) = true := by
  intro e he
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
  exact lt_ofE _

theorem lt_tauSW (C Z : Fmt.M1.Code) (c d : Array Fmt.M1.E) (h0 h1 : ℕ → GE) :
    (decide ((tauSW C Z c d h0 h1).1 < fieldPrimeWord) && decide ((tauSW C Z c d h0 h1).2.1 < fieldPrimeWord) &&
      decide ((tauSW C Z c d h0 h1).2.2 < fieldPrimeWord)) = true :=
  lt_ofE _

end Johnson.Prover.Link
