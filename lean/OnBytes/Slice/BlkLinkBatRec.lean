-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkBatRec.lean: the batching on the link's group, entry by entry, whatever list
of rows the test takes in.

OnBytes/Slice/BlkLinkBat.lean applies the laws on batching to the statement after the link's steps
(OnBytes/Slice/BlkLinkRan.lean: `linkSt`), for a group whose open rows are the equality row and
generator rows. Of the rows it uses one thing: which list the proximity test takes in. This file
says its theorems again with that list as a letter, `all`, and the equation as a hypothesis
(`hrun`), so that they serve for tables with a record too. The text is that file's, cut by a
program.

Main theorems.
 `linkBat_fitsR`          the rows meet the conditions of the laws after the test's beginning too.
 `linkBat_targetR`, `linkBat_target_sumR`   the batched row's target.
 `linkBat_mainR`, `linkBat_main_sumR`       its coefficient at a row of a member's block.
 `linkBat_maskR`          its mask table is 0, if no row has a term on a mask table.
Not claimed. That the rows meet the conditions of the laws on batching is a hypothesis here
(`hfit`); so is the list of rows that the test takes in (`hrun`). Nothing on soundness.

-/
import OnBytes.Slice.BlkLinkBat

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape FoldeqShape)

/-! ## The batching on the link's group -/

section
variable {K : Type} [CommRing K] (ρ : Model.Reading K) (S : LinkShape) (T : Statement)
  (places : List PadPlace) (s0 s1 : Row) (rows0 rows1 : List Row) (rE : Row)

variable (all : List Row)
  (hrun : runRows (linkSt S T places s0 s1 rows0 rows1 rE)
    (linkGrp S rows0 rows1 rE T.oracles.size) = all.toArray)
  (hfit : ∀ r ∈ all, RowFits (linkSt S T places s0 s1 rows0 rows1 rE) r)
  (x : E) (out : GroupRow)
  (h : Bat.combine (begun (linkSt S T places s0 s1 rows0 rows1 rE) T.groups.size
      (linkGrp S rows0 rows1 rE T.oracles.size)) T.groups.size
    ⟨linkLay S T, runRows (linkSt S T places s0 s1 rows0 rows1 rE)
      (linkGrp S rows0 rows1 rE T.oracles.size)⟩ x = some out)

include hrun hfit h

omit h in
/-- The rows that are batched meet the conditions of the laws on batching after the beginning of
the test too, given that they meet them before it (`hfit`). -/
theorem linkBat_fitsR : ∀ r ∈ (runRows (linkSt S T places s0 s1 rows0 rows1 rE)
      (linkGrp S rows0 rows1 rE T.oracles.size)).toList,
    RowFits (begun (linkSt S T places s0 s1 rows0 rows1 rE) T.groups.size
      (linkGrp S rows0 rows1 rE T.oracles.size)) r := by
  intro r hr
  rw [hrun] at hr
  exact rowFits_congr (fun o part => begun_rowBits _ _ _ o part) (hfit r (by simpa using hr))

/-- The target of the batched row: the sum of the rows' targets under the powers of x. -/
theorem linkBat_targetR :
    ρ.val out.target = hornerSum (ρ.val x)
      (all.map fun r => ρ.val r.target) := by
  have k := combine_target ρ _ _ _ x out h
    (linkBat_fitsR S T places s0 s1 rows0 rows1 rE all hrun hfit)
  rw [k]
  show hornerSum _ ((runRows _ _).toList.map _) = _
  rw [hrun]

/-- A coefficient of the batched row: at row r of the block of member b, at the place p, the sum
of the rows' coefficients on entry (r, p) of that member's own main table, under the powers of x. -/
theorem linkBat_mainR (b : Bool) (r p : Nat) (hr : r < 2 ^ ceilLog2 S.rows) :
    ρ.val (out.c.entry
      ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p)) =
      hornerSum (ρ.val x) (all.map fun q =>
        ρ.val (q.coefficient (T.oracles.size + b.toNat) .main (r + 2 ^ ceilLog2 S.rows * p))) := by
  have hb := linkBegun_rowBits S T places s0 s1 rows0 rows1 rE
  have k := combine_main_member ρ _ _ _ x out h (link_blocksOk S T _ hb)
    (linkBat_fitsR S T places s0 s1 rows0 rows1 rE all hrun hfit)
    (T.oracles.size + b.toNat)
    ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p)
    ((link_weight S T _ hb b b r p hr).trans (if_pos rfl))
    (fun o' ho' => by
      by_cases e : o' = T.oracles.size + (!b).toNat
      · rw [e]
        exact (link_weight S T _ hb b (!b) r p hr).trans (if_neg (by cases b <;> decide))
      · refine link_weight_other S T _ o' ?_ ?_ _
        · intro q
          cases b
          · exact ho' q
          · exact e q
        · intro q
          cases b
          · exact e q
          · exact ho' q)
  rw [k]
  show hornerSum _ ((runRows _ _).toList.map _) = _
  rw [hrun]
  dsimp only
  rw [link_back S T _ hb b r p hr]

/-- The mask table of the batched row is 0, if no row has a term on a mask table. -/
theorem linkBat_maskR
    (hmain : ∀ r ∈ all, ∀ t ∈ r.terms.toList, t.part = .main)
    (J : Nat) (hJ : J < 2 ^ ((linkLay S T).h + (linkLay S T).logEllZk)) :
    ρ.val (out.d.getD J zeroE) = 0 := by
  refine combine_mask_none ρ _ _ _ x out h (link_maskBlocksOk S T _) (fun r hr => ⟨linkBat_fitsR S T
    places s0 s1 rows0 rows1 rE all hrun hfit r hr, fun t ht hp => ?_⟩) J hJ
    fun o => link_maskWeight S T _ o J
  have hr' : r ∈ (runRows _ _).toList := hr
  rw [hrun] at hr'
  rw [hmain r hr' t ht] at hp
  cases hp

/-- The target of the batched row, as a sum over a range. -/
theorem linkBat_target_sumR :
    ρ.val out.target = ∑ b ∈ Finset.range all.length,
      ρ.val x ^ b * ρ.val (all.getD b default).target := by
  rw [linkBat_targetR ρ S T places s0 s1 rows0 rows1 rE all hrun hfit x out h, hornerSum_eq_sum,
    List.length_map]
  exact Finset.sum_congr rfl fun b hb => by
    rw [getD_map_of_lt _ _ b (Finset.mem_range.1 hb)]

/-- A coefficient of the batched row, as a sum over a range. -/
theorem linkBat_main_sumR (b : Bool) (r p : Nat) (hr : r < 2 ^ ceilLog2 S.rows) :
    ρ.val (out.c.entry
      ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p)) =
      ∑ i ∈ Finset.range all.length,
        ρ.val x ^ i * ρ.val ((all.getD i default).coefficient
          (if b then T.oracles.size + 1 else T.oracles.size) .main
          (r + 2 ^ ceilLog2 S.rows * p)) := by
  rw [linkBat_mainR ρ S T places s0 s1 rows0 rows1 rE all hrun hfit x out h b r p hr,
    hornerSum_eq_sum, List.length_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [getD_map_of_lt _ _ i (Finset.mem_range.1 hi)]
  cases b <;> rfl

end

end OnBytes.Slice
