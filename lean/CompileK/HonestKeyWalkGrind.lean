-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyWalkGrind.lean: the honest committer's typed count at a wire with searches
(`QueryLayout.grind`, Iop/GrindWire.lean), in the counts in which the library's other bounds have closed
forms.

This file is about the cost of making a key: an upper bound on the number of oracle queries of the
honest committer where rounds have proof of work.
One statement and its proof; a tool on prices (`hk_cost_scale`). Generic: any interface, any wire Wr
without searches, any data of the search, any lists of numbers of test bits. Nothing assumed beyond
the hypotheses of the statements and whatever the arguments hold as proofs.
`hkCom W p u`, the count at a price u on oracle names: CompileK/HonestKeyWalk.lean; the typed count
is its value at the price 1.

Main names:
  `Spec.honestKey_grind`: for an inhabited type Nn of nonces,
    hkCom (Wr.grind Dg gT gL gB) p (fun _ => 1) ≤ 2 · xTree Wr p 0 +
    (2 · rounds of Test + sumMo Dg gT + 1) + leaves · (2 · rounds of Link + sumMo Dg gL + 1).
    `xTree Wr p 0`: the leaves of all trees of the set-up (Compile/Batch/Counts.lean); twice: a leaf
    query, a vertex. `GBits.sumMo`: the tries after the first, every search at its cap
    (Compile/Batch/CountsGrind.lean).
  `hk_cost_scale`: an algorithm with at most t queries costs at most c · t at every price that is at
    most c at every name.

Limits: coarse, as `cCBW_le` (Compile/Batch/OneCallCostClosed.lean) is: a first try is charged twice
in every round (the 2). Worst case over the oracle. This file says nothing on the value of any
number.

Terms: lean/GLOSSARY.md.
-/
import CompileK.HonestKeyWalkProofs
import Compile.Batch.OneCallCostClosed
import Compile.Batch.CountsGrind
import Iop.GrindProofs

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.OneCall (cCBW wFSW sumB cCBW_le)

namespace Spec

/-- The typed count at a wire with searches. -/
def honestKey_grind : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (Wr : QueryLayout lam L)
      (Dg : GrData Nn) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (p : Params),
    hkCom (Wr.grind Dg gT gL gB) p (fun _ => 1) ≤
      2 * xTree Wr p 0 + (2 * L.offline.shape.length + GBits.sumMo Dg _ gT + 1) +
        p.leaves * (2 * L.link.shape.length + GBits.sumMo Dg _ gL + 1)

end Spec

theorem hk_sumB_one : ∀ (s : Shape) (i : ℕ), sumB (fun _ => 1) s i = s.length
  | [], _ => rfl
  | _ :: s, i => by
    show 1 + sumB (fun _ => 1) s (i + 1) = s.length + 1
    rw [hk_sumB_one s (i + 1), Nat.add_comm]

theorem honestKey_grind : Spec.honestKey_grind := by
  intro Nn _ I X lam L Wr Dg gT gL gB p
  rw [honestKey_sum]
  refine le_trans (cCBW_le (Wr.grind Dg gT gL gB) p 1 (bf := fun _ _ => 1) fun _ _ => le_rfl)
    (le_of_eq ?_)
  have eT : wFSW 1 (fun _ => 1) (Wr.grind Dg gT gL gB).T =
      2 * L.offline.shape.length + GBits.sumMo Dg _ gT + 1 := by
    show 2 * sumB (fun _ => 1) (L.offline.shape.grind Nn gT) 0 +
        1 * (sMoreJ _ _ (RoundsQueryLayout.grindLocal Wr.T.sh Dg gT) +
            sMore0 _ _ (RoundsQueryLayout.grindLocal Wr.T.sh Dg gT)) + 1 = _
    rw [hk_sumB_one, Shape.grind_length, sMoreJ_grindLocal, sMore0_grindLocal, Nat.one_mul]
    rfl
  have eL : wFSW 1 (fun _ => 1) (Wr.grind Dg gT gL gB).Lk =
      2 * L.link.shape.length + GBits.sumMo Dg _ gL + 1 := by
    show 2 * sumB (fun _ => 1) (L.link.shape.grind Nn gL) 0 +
        1 * (sMoreJ _ _ (RoundsQueryLayout.grindLocal Wr.Lk.sh Dg gL) +
            sMore0 _ _ (RoundsQueryLayout.grindLocal Wr.Lk.sh Dg gL)) + 1 = _
    rw [hk_sumB_one, Shape.grind_length, sMoreJ_grindLocal, sMore0_grindLocal, Nat.one_mul]
    rfl
  rw [xTree_grind, eT, eL]
  rfl

/-- At most t queries cost at most c · t, at every price that is at most c at every name. -/
theorem hk_cost_scale {S : OSpec} {α : Type} {w : S.ι → ℕ} {c : ℕ}
    (hw : ∀ o, w o ≤ c) {a : OComp S α} :
    ∀ {t : ℕ}, a.CostBound (fun _ => 1) t → a.CostBound w (c * t) := by
  induction a with
  | pure x => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro t ⟨t', rfl, h⟩
    have := hw o
    exact ⟨c * (1 + t') - w o,
      by rw [Nat.mul_add, Nat.mul_one]; omega,
      fun r => (ih r (h r)).mono (by rw [Nat.mul_add, Nat.mul_one]; omega)⟩

end Compile.Batch
