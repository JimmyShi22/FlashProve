-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkBat.lean: the batching on the link's group, entry by entry.

The batching combines the rows of a group under the powers of one drawn element into one row on the
group's two tables (OnBytes/Iop/Bat.lean: `Bat.combine`). The laws of OnBytes/Iop/RowLaws.lean and
MaskLaws.lean say what the result reads as, entry by entry, in any commutative ring under a reading
of the program's field elements. This file applies them to the statement after the link's steps
(OnBytes/Slice/BlkLinkRan.lean: `linkSt`) and the layout of the link's group
(OnBytes/Slice/BlkLinkLay.lean: `linkLay`).

Main theorems.
 `hornerSum_eq_sum`      the sum of a list's entries under the powers of y, as a sum over a range.
 `linkBat_target`, `linkBat_target_sum`   the batched row's target.
 `linkBat_main`, `linkBat_main_sum`       its coefficient at a row of a member's block.
 `linkBat_mask`          its mask table is 0, if no row has a term on a mask table.
Not claimed. That the rows meet the conditions of the laws on batching is a hypothesis here
(`hfit`); so are the rows' kinds. Nothing on soundness.
-/
import OnBytes.Slice.BlkLinkLay
import OnBytes.Slice.BlkSend

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape FoldeqShape)

/-! ## A sum under powers -/

/-- The sum of a list's entries, entry number b times y^b, as a sum over a range. -/
theorem hornerSum_eq_sum {K : Type} [CommRing K] (y : K) : ∀ l : List K,
    hornerSum y l = ∑ b ∈ Finset.range l.length, y ^ b * l.getD b 0
  | [] => rfl
  | a :: l => by
    rw [hornerSum, hornerSum_eq_sum y l, List.length_cons, Finset.sum_range_succ', Finset.mul_sum,
      add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b _ => by rw [List.getD_cons_succ, pow_succ']; ring
    · simp

/-! ## The batching on the link's group -/

section
variable {K : Type} [CommRing K] (ρ : Model.Reading K) (S : LinkShape) (T : Statement)
  (places : List PadPlace) (s0 s1 : Row) (rows0 rows1 : List Row) (rE : Row)

/-- The two members' numbers of row bits, after the beginning of the test. -/
theorem linkBegun_rowBits (b : Bool) :
    (begun (linkSt S T places s0 s1 rows0 rows1 rE) T.groups.size
      (linkGrp S rows0 rows1 rE T.oracles.size)).rowBits (T.oracles.size + b.toNat) .main =
      ceilLog2 S.rows :=
  (begun_rowBits _ _ _ _ _).trans (linkSt_tables S T places s0 s1 rows0 rows1 rE b).2.1

variable (hE : rE.kind = .plain) (h0 : ∀ r ∈ rows0, r.kind = .generator)
  (h1 : ∀ r ∈ rows1, r.kind = .generator)
  (hfit : ∀ r ∈ rE :: s0 :: s1 :: (rows0 ++ rows1),
    RowFits (linkSt S T places s0 s1 rows0 rows1 rE) r)
  (x : E) (out : GroupRow)
  (h : Bat.combine (begun (linkSt S T places s0 s1 rows0 rows1 rE) T.groups.size
      (linkGrp S rows0 rows1 rE T.oracles.size)) T.groups.size
    ⟨linkLay S T, runRows (linkSt S T places s0 s1 rows0 rows1 rE)
      (linkGrp S rows0 rows1 rE T.oracles.size)⟩ x = some out)

include hE h0 h1 hfit h

omit h in
/-- The rows that are batched meet the conditions of the laws on batching after the beginning of
the test too, given that they meet them before it (`hfit`). -/
theorem linkBat_fits : ∀ r ∈ (runRows (linkSt S T places s0 s1 rows0 rows1 rE)
      (linkGrp S rows0 rows1 rE T.oracles.size)).toList,
    RowFits (begun (linkSt S T places s0 s1 rows0 rows1 rE) T.groups.size
      (linkGrp S rows0 rows1 rE T.oracles.size)) r := by
  intro r hr
  rw [linkSt_runRows S T places s0 s1 rows0 rows1 rE hE h0 h1] at hr
  exact rowFits_congr (fun o part => begun_rowBits _ _ _ o part) (hfit r (by simpa using hr))

/-- The target of the batched row: the sum of the rows' targets under the powers of x. -/
theorem linkBat_target :
    ρ.val out.target = hornerSum (ρ.val x)
      ((rE :: s0 :: s1 :: (rows0 ++ rows1)).map fun r => ρ.val r.target) := by
  have k := combine_target ρ _ _ _ x out h
    (linkBat_fits S T places s0 s1 rows0 rows1 rE hE h0 h1 hfit)
  rw [k]
  show hornerSum _ ((runRows _ _).toList.map _) = _
  rw [linkSt_runRows S T places s0 s1 rows0 rows1 rE hE h0 h1]

/-- A coefficient of the batched row: at row r of the block of member b, at the place p, the sum
of the rows' coefficients on entry (r, p) of that member's own main table, under the powers of x. -/
theorem linkBat_main (b : Bool) (r p : Nat) (hr : r < 2 ^ ceilLog2 S.rows) :
    ρ.val (out.c.entry
      ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p)) =
      hornerSum (ρ.val x) ((rE :: s0 :: s1 :: (rows0 ++ rows1)).map fun q =>
        ρ.val (q.coefficient (T.oracles.size + b.toNat) .main (r + 2 ^ ceilLog2 S.rows * p))) := by
  have hb := linkBegun_rowBits S T places s0 s1 rows0 rows1 rE
  have k := combine_main_member ρ _ _ _ x out h (link_blocksOk S T _ hb)
    (linkBat_fits S T places s0 s1 rows0 rows1 rE hE h0 h1 hfit)
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
  rw [linkSt_runRows S T places s0 s1 rows0 rows1 rE hE h0 h1]
  dsimp only
  rw [link_back S T _ hb b r p hr]

/-- The mask table of the batched row is 0, if no row has a term on a mask table. -/
theorem linkBat_mask
    (hmain : ∀ r ∈ rE :: s0 :: s1 :: (rows0 ++ rows1), ∀ t ∈ r.terms.toList, t.part = .main)
    (J : Nat) (hJ : J < 2 ^ ((linkLay S T).h + (linkLay S T).logEllZk)) :
    ρ.val (out.d.getD J zeroE) = 0 := by
  refine combine_mask_none ρ _ _ _ x out h (link_maskBlocksOk S T _) (fun r hr => ⟨linkBat_fits S T
    places s0 s1 rows0 rows1 rE hE h0 h1 hfit r hr, fun t ht hp => ?_⟩) J hJ
    fun o => link_maskWeight S T _ o J
  have hr' : r ∈ (runRows _ _).toList := hr
  rw [linkSt_runRows S T places s0 s1 rows0 rows1 rE hE h0 h1] at hr'
  rw [hmain r hr' t ht] at hp
  cases hp

omit hE h0 h1 hfit h in
/-- An entry of a list of values of a function, below the list's length. -/
theorem getD_map_of_lt {α : Type} [Inhabited α] (f : α → K) (l : List α) (b : Nat)
    (hb : b < l.length) : (l.map f).getD b 0 = f (l.getD b default) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hb]
  rfl

/-- The target of the batched row, as a sum over a range. -/
theorem linkBat_target_sum :
    ρ.val out.target = ∑ b ∈ Finset.range (rE :: s0 :: s1 :: (rows0 ++ rows1)).length,
      ρ.val x ^ b * ρ.val ((rE :: s0 :: s1 :: (rows0 ++ rows1)).getD b default).target := by
  rw [linkBat_target ρ S T places s0 s1 rows0 rows1 rE hE h0 h1 hfit x out h, hornerSum_eq_sum,
    List.length_map]
  exact Finset.sum_congr rfl fun b hb => by
    rw [getD_map_of_lt _ _ b (Finset.mem_range.1 hb)]

/-- A coefficient of the batched row, as a sum over a range. -/
theorem linkBat_main_sum (b : Bool) (r p : Nat) (hr : r < 2 ^ ceilLog2 S.rows) :
    ρ.val (out.c.entry
      ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p)) =
      ∑ i ∈ Finset.range (rE :: s0 :: s1 :: (rows0 ++ rows1)).length,
        ρ.val x ^ i * ρ.val (((rE :: s0 :: s1 :: (rows0 ++ rows1)).getD i default).coefficient
          (if b then T.oracles.size + 1 else T.oracles.size) .main
          (r + 2 ^ ceilLog2 S.rows * p)) := by
  rw [linkBat_main ρ S T places s0 s1 rows0 rows1 rE hE h0 h1 hfit x out h b r p hr,
    hornerSum_eq_sum, List.length_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [getD_map_of_lt _ _ i (Finset.mem_range.1 hi)]
  cases b <;> rfl

end

end OnBytes.Slice

#print axioms OnBytes.Slice.hornerSum_eq_sum
#print axioms OnBytes.Slice.linkBegun_rowBits
#print axioms OnBytes.Slice.linkBat_fits
#print axioms OnBytes.Slice.linkBat_target
#print axioms OnBytes.Slice.linkBat_main
#print axioms OnBytes.Slice.linkBat_mask
#print axioms OnBytes.Slice.getD_map_of_lt
#print axioms OnBytes.Slice.linkBat_target_sum
#print axioms OnBytes.Slice.linkBat_main_sum
