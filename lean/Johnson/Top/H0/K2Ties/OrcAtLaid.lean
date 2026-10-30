-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/OrcAtLaid.lean: the code switch's law at the closed constant: THE
READING OF THE ORACLES OFF THE STRINGS IS THE STRINGS' OWN COLUMN AT EVERY TREE OF THE FIRST CHAIN:
the premise horc of K2Caller/TableSide.lean's tableSide_of (∀ j, j < trees → ∀ x, orc y j x = y.col
j x) at orc := K2.orcY (ProofFile.allAt Zp) (ProofFile.keyAt Zp), FROM «THE VALUE IS LAID». horc_of_laid under
LaidAt: at every tree j below the laid data's number of the first chain's trees (D.t₁). Two
calls: Opts/WholeOfLaid.lean's wholeAt_of_laid and K2Caller/OrcAtZ.lean's orcY_atZ
  horc_83      the same below 83, where D.t₁ = 83
WHO PAYS ht : D.t₁ = 83. P5J.AtMg.trees | t1_t2_at (Johnson/HB/LLHARD/HeadFacts.lean)
under the constant's head, with no pin: in scope the laid data are the
written ones. NOT IMPORTED HERE: two files beneath it were not in this file's build.
LIMITS. Two short joins. No soundness is claimed.
-/
import Johnson.Top.H0.Opts.WholeOfLaid
import Johnson.Top.H0.K2Caller.OrcAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs)
open P5J (LaidAt TS)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

theorem horc_of_laid (L : LaidAt o pol lay KL D r Zp Np cF) (y : Strs) (j : ℕ) (hj : j < D.t₁)
    (x : ℕ) : K2.orcY (ProofFile.allAt Zp) (ProofFile.keyAt Zp) y j x = y.col j x :=
  K2Caller.orcY_atZ Zp D (P1M2.wholeAt_of_laid L) y j x hj

theorem horc_83 (L : LaidAt o pol lay KL D r Zp Np cF) (ht : D.t₁ = 83) (y : Strs) :
    ∀ j, j < 83 → ∀ x, K2.orcY (ProofFile.allAt Zp) (ProofFile.keyAt Zp) y j x = y.col j x :=
  fun j hj x => horc_of_laid L y j (by rw [ht]; exact hj) x

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.horc_of_laid
#print axioms VerifiableInference.Desc.First.K2Ties.horc_83
