-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoRowsLaw.lean: one law for all virtual rows of a sub-proof's arrays, at
the weights that the state declares; and the three virtual rows of BZ as its values.

 - RowsLaw ρ F W cellAt: in the world W every entry of every virtual row that F has is the
   combination of its array's rows under the weights that F declares for the row (HRow.coef), read
   by ρ: W.entry t e i is the sum, over r below the array's number of rows, of ρ (coef[r]) times
   cellAt t r i. Pointwise in W and in the arrays' own entries cellAt. It is a hypothesis wherever
   it stands.
 - rowsLaw_some: some world meets it. RowsLaw.virt: it gives VirtRow at every row that F has, at the
   declared weights.
 - virt_bz: behind HTailF2.coefficientsF, under RowsLaw: the three VirtRow's on BZ that bits9_paid
   asks: rows 0 and 1 under the equality weights of the first five coordinates of the two points,
   row 2 under ones. Premises: those of coef_bz; BZ has 32 rows; the two points, read, are zb0 and
   zb1.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that RowsLaw holds of committed arrays. The chain takes a virtual row's weights in
a product form, which rowWeights (OnBytes/Model/Trees.lean) compares with coef; nothing on either is
stated here.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef
import OnBytes.Tie.Pv.Lookup.Ends.FoVirtRow
import OnBytes.Tie.Pv.Lookup.Port.FoTwins

set_option autoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- Every virtual row is the combination of its array's rows under its declared weights. -/
def RowsLaw (F : Fork) (W : World K) (cellAt : ℕ → ℕ → ℕ → K) : Prop :=
  ∀ t e i, HasRow F t e → W.entry t e i =
    ∑ r ∈ range (F.trees.getD t {}).R, ρ.val ((rowAt F t e).coef.getD r zeroE) * cellAt t r i

theorem rowsLaw_some (F : Fork) (slot : ℕ → K) (cellAt : ℕ → ℕ → ℕ → K) :
    ∃ W : World K, W.slot = slot ∧ RowsLaw ρ F W cellAt :=
  ⟨⟨slot, fun t e i =>
    ∑ r ∈ range (F.trees.getD t {}).R, ρ.val ((rowAt F t e).coef.getD r zeroE) * cellAt t r i⟩,
    rfl, fun _ _ _ _ => rfl⟩

/-- The law at one row. -/
theorem RowsLaw.virt {F : Fork} {W : World K} {cellAt : ℕ → ℕ → ℕ → K} (h : RowsLaw ρ F W cellAt)
    (t e n : ℕ) (hr : HasRow F t e) :
    VirtRow W.entry t e (fun r => (rdL ρ (rowAt F t e).coef).getD r 0) (cellAt t)
      (F.trees.getD t {}).R n := fun i _ => by
  rw [h t e i hr]
  exact Finset.sum_congr rfl fun r _ => by rw [rdL_getD]

theorem rdL_ones (n : ℕ) (r : ℕ) (hr : r < n) :
    (rdL ρ (Array.replicate n oneE)).getD r 0 = 1 := by
  rw [← rdL_getD]
  have e : (Array.replicate n oneE).getD r zeroE = oneE := by simp [Array.getD, hr]
  rw [e, ρ.one]

/-- Behind coefficientsF, under the law: the three virtual rows of BZ. -/
theorem virt_bz (tl : HTailF2) (g : Forest.Heard) (F : Fork) (h0 : HasRow F tl.ix.BZ 0)
    (h1 : HasRow F tl.ix.BZ 1) (h2 : HasRow F tl.ix.BZ 2)
    (hm : ∀ mu < tl.NM, tl.gtTree.getD mu 0 ≠ tl.ix.BZ) (hR : (F.trees.getD tl.ix.BZ {}).R = 32)
    (W : World K) (cellAt : ℕ → ℕ → ℕ → K) (hL : RowsLaw ρ (coefAll tl g F) W cellAt)
    (zb0 zb1 : List K) (e0 : rdL ρ g.zb0 = zb0) (e1 : rdL ρ g.zb1 = zb1) (n : ℕ) :
    VirtRow W.entry tl.ix.BZ 0 (fun r => (eqTabK (zb0.take 5)).getD r 0) (cellAt tl.ix.BZ) 32 n ∧
    VirtRow W.entry tl.ix.BZ 1 (fun r => (eqTabK (zb1.take 5)).getD r 0) (cellAt tl.ix.BZ) 32 n ∧
    VirtRow W.entry tl.ix.BZ 2 (fun _ => 1) (cellAt tl.ix.BZ) 32 n := by
  obtain ⟨c0, c1, c2⟩ := coef_bz tl g F h0 h1 h2 hm
  have hR' : ((coefAll tl g F).trees.getD tl.ix.BZ {}).R = 32 :=
    ((frame_all tl g F).2 tl.ix.BZ).1.trans hR
  have v0 := hL.virt ρ tl.ix.BZ 0 n ((frame_all tl g F).hasRow h0)
  have v1 := hL.virt ρ tl.ix.BZ 1 n ((frame_all tl g F).hasRow h1)
  have v2 := hL.virt ρ tl.ix.BZ 2 n ((frame_all tl g F).hasRow h2)
  rw [hR'] at v0 v1 v2
  rw [c0, eqTab_val, rdL_extract, e0] at v0
  rw [c1, eqTab_val, rdL_extract, e1] at v1
  rw [c2] at v2
  refine ⟨v0, v1, fun i hi => ?_⟩
  rw [v2 i hi]
  refine Finset.sum_congr rfl fun r hr => ?_
  show (rdL ρ (Array.replicate 32 oneE)).getD r 0 * _ = 1 * _
  rw [rdL_ones ρ 32 r (Finset.mem_range.mp hr)]

end
end Fo
