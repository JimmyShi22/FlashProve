-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/NoWrapN.lean: the head segment, for every valid final normalisation: the stream at a
position (`xAt`), the ledger's size conditions (`N.adm`), and four arrays as sums of their cells.

The final normalisation is an argument np with `NormPar.OK` (1 ≤ ϵ < 2^48, 24 ≤ M ≤ 47, 17 ≤ K ≤ 32,
M − 14 ≤ K), the range that the implementation's verifier admits with five limbs (`HeadTests`,
Inst/Model/ProgTests.lean); the reference scales have M = 44, K = 30, ϵ = 53,687.
Notation: `NormPar` (Inst/Model/Program.lean): "exponent of the reciprocal; shift; constant" of a
normalisation: `M`, `K`, `eps` (ϵ).
(Words of this library: lean/GLOSSARY.md.)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Head.TraceN
import Inst.Model.Common.LedgerSound
import Inst.Model.Common.Site

set_option autoImplicit false

namespace Inst.Model.Head

open Finset

/-- the residual stream at position i, as the borrowed cells give it -/
def xAt (t : Cells ℤ) (i : ℕ) : Vec := fun j => xv t j i

theorem xAt_eq {t : Cells ℤ} (i : ℕ) : xAt t i = Ledger.xOf fun l j => bl t l j i := rfl

namespace N

/-- the ledger's size conditions hold at 2^61 - 1 (the floor of `Cm.TI.Big p`) for every valid np -/
theorem adm {np : NormPar} (hn : np.OK) : Ledger.Adm (2 ^ 61 - 1) np nD (2 ^ 18) :=
  ⟨hn.1, hn.2.1, hn.2.2.2.1, by norm_num, by norm_num, by norm_num [nD], by norm_num⟩

section Steps
variable {t : Cells ℤ}

theorem nw_eq (j i : ℕ) : nw t j i = t.hf (fNw 0 j) i + 256 * t.hf (fNw 1 j) i := by
  simp [nw, rd, sum_range_succ]
theorem rn_eq (j i : ℕ) : rn t j i = 32896 + (t.hf (fRn 0 j) i + 256 * t.hf (fRn 1 j) i) := by
  simp [rn, rd, sum_range_succ]
theorem d1_eq (v i : ℕ) : d1 t v i = t.hf (fD1 0 v) i + 256 * t.hf (fD1 1 v) i := by
  simp [d1, rd, sum_range_succ]
theorem nrm_eq (j i : ℕ) : nrm t j i = t.hd (fNrm 0 j) i + 256 * t.hd (fNrm 1 j) i := by
  simp [nrm, rd, sum_range_succ]

end Steps

end N

end Inst.Model.Head
