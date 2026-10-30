-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/TablesRef.lean: `tbRef`: the table functions (`Tables`, Inst/Model/Program.lean) at
`ppref` as computable data.
To audit the relation `RinfPP` (Inst/Model/Scales.lean), read this file too (with the numbers of
Inst/Model/TablesData.lean).
    `dec`        how an entry is read from the data
    `tbRef`      the five table functions. Each accessor ends in the clamp of its declared range, so
                 that `Tables.OK`'s bounds hold by construction, whatever the numbers are; Exp[0] =
                 2^12 is evaluated (`refExp_zero`)
    `tbRef_ok`   `tbRef.OK ppref`: (Tab3), (Tab4), (Tab5), (Tab8)
No `Classical.choice` occurs in `tbRef`.
Limits: no theorem says that the numbers are the rounded values of the real functions.
-/
import Inst.Model.Tables
import Inst.Model.TablesData
import Mathlib.Tactic

set_option autoImplicit false

namespace Inst.Model

/-- entry k of the data a, at b bits for each entry, in blocks of 1,024 entries -/
def dec (a : Array ℕ) (b k : ℕ) : ℕ := (a.getD (k / 1024) 0 >>> (b * (k % 1024))) % 2 ^ b

/-- SILU[ι] depends on c = min(max(ι − 2^15, −2^14), 2^14 − 1) only -/
def refSILU (ι : ℤ) : ℤ :=
  clamp 4095
    ((dec Data.silu 13 (min (max (ι - 2 ^ 15) (-2 ^ 14)) (2 ^ 14 - 1) + 2 ^ 14).toNat : ℤ) - 4095)
def refSIGM (ι : ℤ) : ℤ := 16 * min (dec Data.sigm 13 (ι - 2 ^ 14).toNat : ℤ) 4096
def refExp (t : ℤ) : ℤ := max 1 (min (dec Data.exp 13 t.toNat : ℤ) 4096)
def refC (L i jj : ℕ) : ℤ :=
  if rotaryOff L then 2 ^ 12 else clamp 4096 ((dec Data.cos 14 (64 * i + jj) : ℤ) - 4096)
def refS (L i jj : ℕ) : ℤ :=
  if rotaryOff L then 0 else clamp 4096 ((dec Data.sin 14 (64 * i + jj) : ℤ) - 4096)

/-- The table functions at `ppref`. -/
def tbRef : Tables := ⟨refSILU, refSIGM, refExp, refC, refS⟩

theorem clamp_bounds {c : ℤ} (hc : 0 ≤ c) (a : ℤ) : -c ≤ clamp c a ∧ clamp c a ≤ c :=
  ⟨le_min (le_max_right _ _) (by omega), min_le_right _ _⟩

theorem refExp_zero : refExp 0 = 2 ^ 12 := by decide +kernel

theorem tbRef_ok : tbRef.OK ppref := by
  refine ⟨fun ι _ => clamp_bounds (by norm_num) _, fun ι _ => ?_, fun L _ i _ jj _ => ⟨?_, ?_⟩,
    fun t _ => ?_, refExp_zero⟩
  · simp only [tbRef, refSIGM]
    have h0 : (0 : ℤ) ≤ (dec Data.sigm 13 ((ι : ℤ) + 2 ^ 14 - 2 ^ 14).toNat : ℤ) :=
      Int.natCast_nonneg _
    constructor
    · have := le_min h0 (by norm_num : (0 : ℤ) ≤ 4096)
      omega
    · have := min_le_right (dec Data.sigm 13 ((ι : ℤ) + 2 ^ 14 - 2 ^ 14).toNat : ℤ) 4096
      omega
  · simp only [tbRef, refC]
    split_ifs
    · norm_num
    · exact clamp_bounds (by norm_num) _
  · simp only [tbRef, refS]
    split_ifs
    · norm_num
    · exact clamp_bounds (by norm_num) _
  · simp only [tbRef, refExp]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

end Inst.Model

/-! Evaluation at every build: the sum and a running hash of each table equal the literals below,
those that the generator (the head of Inst/Model/TablesData.lean) printed for its own numbers.
(#guard evaluates; it is a check of the build, not a theorem.) -/
namespace Inst.Model
def hashT (f : ℕ → ℤ) (n : ℕ) : ℤ × ℤ :=
  (List.range n).foldl
    (fun (p : ℤ × ℤ) k => (p.1 + f k, (p.2 * 1000003 + f k + 5000) % 2305843009213693951)) (0, 0)
#guard hashT (fun k => tbRef.SILU (k + 2 ^ 14)) 32768 == (33525516, 723515776591532844)
#guard hashT (fun k => tbRef.SIGM (k + 2 ^ 14)) 32768 == (1073709056, 900878014847636071)
#guard hashT (fun k => tbRef.Exp k) 2307 == (1050555, 1029249593465725222)
#guard hashT (fun k => tbRef.C 0 (k / 64) (k % 64)) 65536 == (133506231, 1294050433224703316)
#guard hashT (fun k => tbRef.S 0 (k / 64) (k % 64)) 65536 == (31834965, 2144425673137528335)
-- samples: SILU at ζ = 0 and at both ends, SIGM in the middle and at both ends, the first and last
-- rows of Exp, cos 1 and sin 1
#guard (tbRef.SILU (2 ^ 15), tbRef.SILU 0, tbRef.SILU (2 ^ 16 - 1)) == (0, 0, 4095)
#guard (tbRef.SIGM (2 ^ 15), tbRef.SIGM (2 ^ 14), tbRef.SIGM (3 * 2 ^ 14 - 1)) == (32768, 0, 65536)
#guard (tbRef.Exp 0, tbRef.Exp 1, tbRef.Exp 2306) == (4096, 4080, 1)
#guard (tbRef.C 0 1 0, tbRef.S 0 1 0, tbRef.C 3 1 0, tbRef.S 3 1 0, tbRef.C 0 0 5, tbRef.S 0 0 5) == (2213, 3447, 4096, 0, 4096, 0)
end Inst.Model

