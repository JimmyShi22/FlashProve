-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkLay.lean: the layout of the link's group.

A group puts its members' tables into two tables of its own (OnBytes/Iop/Ground.lean:
`Statement.layout`, `layBlocks`). The link's group has two members, the oracle messages of the two
folded rows, each with the same number of main rows and without mask rows. This file computes the
group's layout: with 2^a the least power of two that holds a member's rows, the first member's block
begins at row 0, the second's at row 2^a, and the group's main table has 2^(a+1) rows. It then
meets, at that layout, the hypotheses of the laws on batching (OnBytes/Iop/RowLaws.lean,
MaskLaws.lean): the blocks are aligned and inside the table, an index of the group's main table lies
in the block of exactly one member, which entry of the member's own table belongs to it, and no
index of the group's mask table lies in a member's block.

Main definition: `linkLay`.
Main theorems.
 `layBlocks_pair`, `layBlocks_noRows`   two blocks of one size; two members without rows of a kind.
 `linkSt_layout`    the statement after the link's steps gives the group that layout.
 `linkLay_k`, `linkLay_find`   the layout's numbers of row variables; the members' places.
 `link_blocksOk`, `link_weight`, `link_weight_other`, `link_back`   the main table.
 `link_maskBlocksOk`, `link_maskWeight`   the mask table.
Not claimed. Nothing on what the batching computes. Nothing on soundness.
-/
import OnBytes.Iop.MaskLaws
import OnBytes.Slice.BlkLinkRan

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape FoldeqShape)

/-! ## Two blocks of one size -/

/-- A turn of the laying of blocks for a size that no member has changes nothing. -/
theorem layTurn_other (a e : Nat) (h : e ≠ a) (acc : Array (Option Nat) × Nat) :
    (List.range (#[some a, some a] : Array (Option Nat)).size).foldl
      (fun (acc : Array (Option Nat) × Nat) i =>
        if (#[some a, some a] : Array (Option Nat)).getD i none == some e then
          (acc.1.setIfInBounds i (some acc.2), acc.2 + 2 ^ e)
        else acc) acc = acc := by
  have h' : ¬ a = e := fun q => h q.symm
  simp [List.range_succ, h']

/-- The same for all turns of a list of such sizes. -/
theorem layTurns_other (a : Nat) : ∀ (l : List Nat) (acc : Array (Option Nat) × Nat),
    (∀ e ∈ l, e ≠ a) →
    l.foldl (fun acc e =>
      (List.range (#[some a, some a] : Array (Option Nat)).size).foldl
        (fun (acc : Array (Option Nat) × Nat) i =>
          if (#[some a, some a] : Array (Option Nat)).getD i none == some e then
            (acc.1.setIfInBounds i (some acc.2), acc.2 + 2 ^ e)
          else acc) acc) acc = acc
  | [], _, _ => rfl
  | e :: l, acc, h => by
    rw [List.foldl_cons, layTurn_other a e (h e List.mem_cons_self)]
    exact layTurns_other a l acc fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- Two members with blocks of 2^a rows: the first block begins at row 0, the second at row 2^a. -/
theorem layBlocks_pair (a : Nat) :
    layBlocks #[some a, some a] = (#[some 0, some (2 ^ a)], 2 ^ a + 2 ^ a) := by
  have htop :
      (#[some a, some a] : Array (Option Nat)).foldl (fun m s => max m (s.getD 0)) 0 = a := by
    simp
  unfold layBlocks
  dsimp only
  rw [htop, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.foldl_cons, layTurns_other a _ _ fun e he =>
      Nat.ne_of_lt (List.mem_range.1 (List.mem_reverse.1 he))]
  simp [List.range_succ]
  rfl

/-- Two members without rows of a kind take no block. -/
theorem layBlocks_noRows : layBlocks #[none, none] = (#[none, none], 0) := by
  decide

/-! ## The layout -/

section
variable (S : LinkShape) (T : Statement) (places : List PadPlace) (s0 s1 : Row)
  (rows0 rows1 : List Row) (rE : Row)

/-- The layout of the link's group: each of the two members has a block of 2^a main rows, where
2^a is the least power of two that holds a member's rows; the first block begins at row 0, the
second at row 2^a; there are no mask rows. -/
def linkLay : GroupLayout :=
  { k := max (max (ceilLog2 (2 ^ ceilLog2 S.rows + 2 ^ ceilLog2 S.rows)) (ceilLog2 0)) 1
    h := ceilLog2 0
    logEll := (T.codes.base.getD S.code default).logEll
    logEllZk := (T.codes.mask.getD S.maskCode default).logEll
    members := #[T.oracles.size, T.oracles.size + 1], kept := #[false, false]
    mainFirst := #[some 0, some (2 ^ ceilLog2 S.rows)], maskFirst := #[none, none] }

/-- What the statement after the steps says of the tables of a folded row's oracle message. -/
theorem linkSt_tables (a : Bool) :
    (linkSt S T places s0 s1 rows0 rows1 rE).has (T.oracles.size + a.toNat) .main =
        decide (0 < S.rows) ∧
      (linkSt S T places s0 s1 rows0 rows1 rE).rowBits (T.oracles.size + a.toNat) .main =
        ceilLog2 S.rows ∧
      (linkSt S T places s0 s1 rows0 rows1 rE).has (T.oracles.size + a.toNat) .mask = false := by
  unfold Statement.has Statement.rowBits
  cases a
  · rw [show T.oracles.size + false.toNat = T.oracles.size from rfl, linkSt_oracle0]
    exact ⟨rfl, rfl, rfl⟩
  · rw [show T.oracles.size + true.toNat = T.oracles.size + 1 from rfl, linkSt_oracle1]
    exact ⟨rfl, rfl, rfl⟩

/-- The statement after the link's steps gives the group that layout. -/
theorem linkSt_layout (hr : 0 < S.rows) :
    (linkSt S T places s0 s1 rows0 rows1 rE).layout T.groups.size = some (linkLay S T) := by
  obtain ⟨m0, b0, z0⟩ := linkSt_tables S T places s0 s1 rows0 rows1 rE false
  obtain ⟨m1, b1, z1⟩ := linkSt_tables S T places s0 s1 rows0 rows1 rE true
  rw [show T.oracles.size + false.toNat = T.oracles.size from rfl] at m0 b0 z0
  rw [show T.oracles.size + true.toNat = T.oracles.size + 1 from rfl] at m1 b1 z1
  unfold Statement.layout
  rw [linkSt_group]
  have hR : Array.range 2 = #[0, 1] := by decide
  simp [hR, m0, b0, z0, m1, b1, z1, hr, layBlocks_pair, layBlocks_noRows, linkLay, linkSt_codes]

end

/-! ## The numbers of the layout -/

/-- The least power of two that holds 2^(a+1) is 2^(a+1). -/
theorem ceilLog2_two_pow_succ (a : Nat) : ceilLog2 (2 ^ a + 2 ^ a) = a + 1 := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  unfold ceilLog2
  rw [if_neg (by omega)]
  have h2 : Nat.log2 (2 ^ a + 2 ^ a - 1) = a :=
    (Nat.log2_eq_iff (by omega)).2 ⟨by omega, by rw [Nat.pow_succ]; omega⟩
  rw [h2]

/-- The link's group has one row variable more than a member, and no mask variable. -/
theorem linkLay_k (S : LinkShape) (T : Statement) :
    (linkLay S T).k = ceilLog2 S.rows + 1 ∧ (linkLay S T).h = 0 := by
  refine ⟨?_, rfl⟩
  show max (max (ceilLog2 (2 ^ ceilLog2 S.rows + 2 ^ ceilLog2 S.rows)) (ceilLog2 0)) 1 = _
  rw [ceilLog2_two_pow_succ]
  show max (max (ceilLog2 S.rows + 1) 0) 1 = _
  omega

/-! ## Where an index of the group's main table belongs -/

section
variable {K : Type} [CommRing K] (S : LinkShape) (T St : Statement)
  (hb : ∀ b : Bool, St.rowBits (T.oracles.size + b.toNat) .main = ceilLog2 S.rows)

/-- The places of the two members in the layout. -/
theorem linkLay_find (o : Nat) :
    (linkLay S T).find o =
      if o = T.oracles.size then some 0 else if o = T.oracles.size + 1 then some 1 else none := by
  unfold GroupLayout.find linkLay
  by_cases h0 : o = T.oracles.size
  · subst h0
    simp [Array.idxOf?, List.finIdxOf?_cons]
    exact ⟨_, rfl, rfl⟩
  · by_cases h1 : o = T.oracles.size + 1
    · subst h1
      simp [Array.idxOf?, List.finIdxOf?_cons]
      exact ⟨_, rfl, rfl⟩
    · have h0' : ¬ T.oracles.size = o := fun e => h0 e.symm
      have h1' : ¬ T.oracles.size + 1 = o := fun e => h1 e.symm
      simp [Array.idxOf?, List.finIdxOf?_cons, h0, h1, h0', h1']
      rfl

include hb

/-- The two blocks are aligned and lie in the group's table. -/
theorem link_blocksOk : MainBlocksOk St (linkLay S T) := by
  have hk := (linkLay_k S T).1
  intro o i first hf hm
  rw [linkLay_find] at hf
  split at hf
  · next h0 =>
    obtain rfl := Option.some.inj hf
    obtain rfl : 0 = first := Option.some.inj hm
    rw [h0, hk, show St.rowBits T.oracles.size .main = ceilLog2 S.rows from hb false]
    exact ⟨Nat.zero_mod _, by rw [Nat.pow_succ]; omega⟩
  · split at hf
    · next h1 =>
      obtain rfl := Option.some.inj hf
      obtain rfl : 2 ^ ceilLog2 S.rows = first := Option.some.inj hm
      rw [h1, hk, show St.rowBits (T.oracles.size + 1) .main = ceilLog2 S.rows from hb true]
      exact ⟨Nat.mod_self _, by rw [Nat.pow_succ]; omega⟩
    · cases hf

/-- Whose block an index of the group's main table lies in. The index of row r of the block of
member b, at the place p, lies in the block of that member and of no other. -/
theorem link_weight (b b' : Bool) (r p : Nat) (hr : r < 2 ^ ceilLog2 S.rows) :
    mainWeight (K := K) St (linkLay S T) (T.oracles.size + b'.toNat)
      ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p) =
      if b' = b then 1 else 0 := by
  have hk := (linkLay_k S T).1
  have hmod : ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p) %
      2 ^ (linkLay S T).k = (if b then 2 ^ ceilLog2 S.rows else 0) + r := by
    rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
    rw [Nat.pow_succ]
    split <;> omega
  have hB := link_blocksOk S T St hb
  cases b'
  · rw [mainWeight_rows St (linkLay S T) _ 0 0 _ (by rw [linkLay_find]; exact if_pos rfl) rfl rfl
      (hB _ 0 0 (by rw [linkLay_find]; exact if_pos rfl) rfl), hmod, hb false]
    cases b
    · simp [hr]
    · simp
  · rw [mainWeight_rows St (linkLay S T) _ 1 (2 ^ ceilLog2 S.rows) _
      (by rw [linkLay_find]; simp) rfl rfl
      (hB _ 1 _ (by rw [linkLay_find]; simp) rfl), hmod, hb true]
    cases b
    · simp
      omega
    · simp [hr]

omit hb in
/-- An oracle message that is no member has no block. -/
theorem link_weight_other (o : Nat) (h0 : o ≠ T.oracles.size) (h1 : o ≠ T.oracles.size + 1)
    (J : Nat) : mainWeight (K := K) St (linkLay S T) o J = 0 := by
  unfold mainWeight
  rw [linkLay_find, if_neg h0, if_neg h1]

/-- The entry of a member's own table that belongs to an index of the group's main table. -/
theorem link_back (b : Bool) (r p : Nat) (hr : r < 2 ^ ceilLog2 S.rows) :
    mainBack St (linkLay S T) (T.oracles.size + b.toNat)
      ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p) =
      r + 2 ^ ceilLog2 S.rows * p := by
  have hk := (linkLay_k S T).1
  have hB : BlockOk (ceilLog2 S.rows) (if b then 2 ^ ceilLog2 S.rows else 0)
      (ceilLog2 S.rows + 1) := by
    cases b
    · exact ⟨Nat.zero_mod _, by rw [Nat.pow_succ]; simp⟩
    · exact ⟨Nat.mod_self _, by rw [Nat.pow_succ]; simp; omega⟩
  unfold mainBack
  rw [hb b, hk, ← groupIndex_closed r p _ _ _ hr, unshift_groupIndex _ _ _ _ hB]

omit hb in
/-- No member has mask rows, so nothing is asked of blocks of mask rows. -/
theorem link_maskBlocksOk : MaskBlocksOk St (linkLay S T) := by
  intro o i first hf hm
  rw [linkLay_find] at hf
  split at hf
  · obtain rfl := Option.some.inj hf
    cases hm
  · split at hf
    · obtain rfl := Option.some.inj hf
      cases hm
    · cases hf

omit hb in
/-- No index of the group's mask table lies in a member's block. -/
theorem link_maskWeight (o J : Nat) : maskWeight (K := K) St (linkLay S T) o J = 0 := by
  unfold maskWeight
  rw [linkLay_find]
  by_cases h0 : o = T.oracles.size
  · rw [if_pos h0]
    rfl
  · rw [if_neg h0]
    by_cases h1 : o = T.oracles.size + 1
    · rw [if_pos h1]
      rfl
    · rw [if_neg h1]

end

end OnBytes.Slice

#print axioms OnBytes.Slice.layTurn_other
#print axioms OnBytes.Slice.layTurns_other
#print axioms OnBytes.Slice.layBlocks_pair
#print axioms OnBytes.Slice.layBlocks_noRows
#print axioms OnBytes.Slice.linkSt_tables
#print axioms OnBytes.Slice.linkSt_layout
#print axioms OnBytes.Slice.ceilLog2_two_pow_succ
#print axioms OnBytes.Slice.linkLay_k
#print axioms OnBytes.Slice.linkLay_find
#print axioms OnBytes.Slice.link_blocksOk
#print axioms OnBytes.Slice.link_weight
#print axioms OnBytes.Slice.link_weight_other
#print axioms OnBytes.Slice.link_back
#print axioms OnBytes.Slice.link_maskBlocksOk
#print axioms OnBytes.Slice.link_maskWeight
