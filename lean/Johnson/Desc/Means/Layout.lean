-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Layout.lean: the layout that a statement gives a group is in order.

Statement.layout places the members' main rows and mask rows by layBlocks. This file shows, for
every group whose members have passed the tests of the joining (GroupOk): which members have a block
in which table; that the blocks are aligned, inside the tables and apart; and that a member's table
has as many places in a row as the group's.

Main definitions: sizesOf, layoutOf, LayFacts.
Main theorems: layout_eq, find_some, find_of_mem, main_block,
main_block_of, mask_block, mask_block_of, main_apart, mask_apart, placeBits_main, placeBits_mask,
layFacts, layoutRight.

What is not claimed. Nothing on the rows of the statement (Row) or on a group's row (GroupRow).

-/
import Johnson.Desc.Means.Says
import Johnson.Desc.Means.Blocks
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

/-- The sizes that the layout hands to layBlocks: for each member its number of row bits, if it has
the table and the table is folded with the group's. -/
def sizesOf (S : Statement) (G : Group) (part : Part) : Array (Option Nat) :=
  (Array.range G.members.size).map fun i =>
    let o := G.members.getD i noId
    if S.has o part && !(part == .main && G.kept.getD i false) then some (S.rowBits o part)
    else none

/-- The layout of a group. -/
def layoutOf (S : Statement) (G : Group) : GroupLayout :=
  { k := max (max (ceilLog2 (layBlocks (sizesOf S G .main)).2)
      (ceilLog2 (layBlocks (sizesOf S G .mask)).2)) 1
    h := ceilLog2 (layBlocks (sizesOf S G .mask)).2
    logEll := (S.codes.base.getD G.code default).logEll
    logEllZk := (S.codes.mask.getD G.maskCode default).logEll
    members := G.members
    kept := G.kept
    mainFirst := (layBlocks (sizesOf S G .main)).1
    maskFirst := (layBlocks (sizesOf S G .mask)).1 }

/-- Statement.layout gives layoutOf. -/
theorem layout_eq (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    S.layout g = some (layoutOf S G) := by
  unfold Statement.layout
  rw [hG]
  rfl

theorem getD_map_range (f : Nat → Option Nat) (n i : Nat) :
    ((Array.range n).map f).getD i none = if i < n then f i else none := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split <;> rfl

/-- A member has a size just if it has the table and the table is folded. -/
theorem sizesOf_some {S : Statement} {G : Group} {part : Part} {i a : Nat}
    (h : (sizesOf S G part).getD i none = some a) :
    i < G.members.size ∧ S.has (G.members.getD i noId) part = true ∧
      (part = .main → G.kept.getD i false = false) ∧
      a = S.rowBits (G.members.getD i noId) part := by
  unfold sizesOf at h
  rw [getD_map_range] at h
  by_cases hi : i < G.members.size
  · rw [if_pos hi] at h
    change (if (S.has (G.members.getD i noId) part &&
      !(part == .main && G.kept.getD i false)) = true then
        some (S.rowBits (G.members.getD i noId) part) else none) = some a at h
    by_cases hc : (S.has (G.members.getD i noId) part &&
        !(part == .main && G.kept.getD i false)) = true
    · rw [if_pos hc] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
        ne_eq] at hc
      refine ⟨hi, hc.1, ?_, (Option.some.inj h).symm⟩
      intro hp
      rcases hc.2 with c | c
      · exact absurd hp c
      · exact c
    · rw [if_neg hc] at h
      cases h
  · rw [if_neg hi] at h
    cases h

@[inherit_doc sizesOf_some]
theorem sizesOf_of {S : Statement} {G : Group} {part : Part} {i : Nat} (hi : i < G.members.size)
    (hh : S.has (G.members.getD i noId) part = true)
    (hk : part = .main → G.kept.getD i false = false) :
    (sizesOf S G part).getD i none = some (S.rowBits (G.members.getD i noId) part) := by
  unfold sizesOf
  rw [getD_map_range, if_pos hi]
  dsimp only
  rw [if_pos]
  rw [hh, Bool.true_and]
  cases part with
  | main => rw [hk rfl]; rfl
  | mask => rfl

/-- The place of a member. -/
theorem find_some {L : GroupLayout} {o i : Nat} (h : L.find o = some i) :
    i < L.members.size ∧ L.members.getD i noId = o := by
  unfold GroupLayout.find at h
  rcases hm : L.members with ⟨l⟩
  rw [hm, List.idxOf?_toArray, List.idxOf?_eq_some_iff] at h
  obtain ⟨hi, e, _⟩ := h
  refine ⟨by simpa using hi, ?_⟩
  simp [hi, e]

/-- Every member has a place. -/
theorem find_of_mem {L : GroupLayout} {o : Nat} (h : o ∈ L.members.toList) :
    ∃ i, L.find o = some i := by
  unfold GroupLayout.find
  apply Option.isSome_iff_exists.1
  rw [Array.isSome_idxOf?]
  exact Array.mem_toList_iff.1 h

/-- What has a place is a member. -/
theorem mem_of_find {L : GroupLayout} {o i : Nat} (h : L.find o = some i) :
    o ∈ L.members.toList := by
  unfold GroupLayout.find at h
  apply Array.mem_toList_iff.2
  rw [← Array.isSome_idxOf?, h]
  rfl

variable (S : Statement) (G : Group)

/-- A block in the main table: the member has main rows, is not kept, and the block is aligned and
inside. -/
theorem main_block {o i first : Nat} (hf : (layoutOf S G).find o = some i)
    (hm : (layoutOf S G).mainFirst.getD i none = some first) :
    S.has o .main = true ∧ (layoutOf S G).kept.getD i false = false ∧
      BlockOk (S.rowBits o .main) first (layoutOf S G).k := by
  obtain ⟨_, ho⟩ := find_some hf
  obtain ⟨a, ha, hd, hle⟩ := (layBlocks_right (sizesOf S G .main)).1 i first hm
  obtain ⟨_, h1, h2, rfl⟩ := sizesOf_some ha
  have ho' : G.members.getD i noId = o := ho
  rw [ho'] at h1 hd hle
  refine ⟨h1, h2 rfl, Nat.mod_eq_zero_of_dvd hd, Nat.le_trans hle ?_⟩
  refine Nat.le_trans (Slice.le_two_pow_ceilLog2 _) (Nat.pow_le_pow_right (by decide) ?_)
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

/-- A member with main rows that is not kept has a block in the main table. -/
theorem main_block_of {o i : Nat} (hf : (layoutOf S G).find o = some i)
    (hh : S.has o .main = true) (hk : (layoutOf S G).kept.getD i false = false) :
    ∃ first, (layoutOf S G).mainFirst.getD i none = some first := by
  obtain ⟨hi, ho⟩ := find_some hf
  have ho' : G.members.getD i noId = o := ho
  exact (layBlocks_right (sizesOf S G .main)).2.2 i _
    (sizesOf_of hi (by rw [ho']; exact hh) (fun _ => hk))

/-- A block in the mask table: the member has mask rows, and the block is aligned and inside. -/
theorem mask_block {o i first : Nat} (hf : (layoutOf S G).find o = some i)
    (hm : (layoutOf S G).maskFirst.getD i none = some first) :
    S.has o .mask = true ∧ BlockOk (S.rowBits o .mask) first (layoutOf S G).h := by
  obtain ⟨_, ho⟩ := find_some hf
  obtain ⟨a, ha, hd, hle⟩ := (layBlocks_right (sizesOf S G .mask)).1 i first hm
  obtain ⟨_, h1, _, rfl⟩ := sizesOf_some ha
  have ho' : G.members.getD i noId = o := ho
  rw [ho'] at h1 hd hle
  exact ⟨h1, Nat.mod_eq_zero_of_dvd hd, Nat.le_trans hle (Slice.le_two_pow_ceilLog2 _)⟩

/-- A member with mask rows has a block in the mask table. -/
theorem mask_block_of {o i : Nat} (hf : (layoutOf S G).find o = some i)
    (hh : S.has o .mask = true) :
    ∃ first, (layoutOf S G).maskFirst.getD i none = some first := by
  obtain ⟨hi, ho⟩ := find_some hf
  have ho' : G.members.getD i noId = o := ho
  exact (layBlocks_right (sizesOf S G .mask)).2.2 i _
    (sizesOf_of hi (by rw [ho']; exact hh) (fun c => by cases c))

/-- Two members' blocks in the main table have no row in common. -/
theorem main_apart {o o' i i' a a' : Nat} (hne : o ≠ o') (hf : (layoutOf S G).find o = some i)
    (hf' : (layoutOf S G).find o' = some i')
    (hm : (layoutOf S G).mainFirst.getD i none = some a)
    (hm' : (layoutOf S G).mainFirst.getD i' none = some a') :
    a + 2 ^ S.rowBits o .main ≤ a' ∨ a' + 2 ^ S.rowBits o' .main ≤ a := by
  obtain ⟨_, ho⟩ := find_some hf
  obtain ⟨_, ho'⟩ := find_some hf'
  have e : G.members.getD i noId = o := ho
  have e' : G.members.getD i' noId = o' := ho'
  obtain ⟨b, hb, _⟩ := (layBlocks_right (sizesOf S G .main)).1 i a hm
  obtain ⟨b', hb', _⟩ := (layBlocks_right (sizesOf S G .main)).1 i' a' hm'
  have r := (layBlocks_right (sizesOf S G .main)).2.1 i i' a a' b b'
    (fun c => hne (by rw [← e, ← e', c])) hm hm' hb hb'
  obtain ⟨_, _, _, rfl⟩ := sizesOf_some hb
  obtain ⟨_, _, _, rfl⟩ := sizesOf_some hb'
  rw [e, e'] at r
  exact r

/-- Two members' blocks in the mask table have no row in common. -/
theorem mask_apart {o o' i i' a a' : Nat} (hne : o ≠ o') (hf : (layoutOf S G).find o = some i)
    (hf' : (layoutOf S G).find o' = some i')
    (hm : (layoutOf S G).maskFirst.getD i none = some a)
    (hm' : (layoutOf S G).maskFirst.getD i' none = some a') :
    a + 2 ^ S.rowBits o .mask ≤ a' ∨ a' + 2 ^ S.rowBits o' .mask ≤ a := by
  obtain ⟨_, ho⟩ := find_some hf
  obtain ⟨_, ho'⟩ := find_some hf'
  have e : G.members.getD i noId = o := ho
  have e' : G.members.getD i' noId = o' := ho'
  obtain ⟨b, hb, _⟩ := (layBlocks_right (sizesOf S G .mask)).1 i a hm
  obtain ⟨b', hb', _⟩ := (layBlocks_right (sizesOf S G .mask)).1 i' a' hm'
  have r := (layBlocks_right (sizesOf S G .mask)).2.1 i i' a a' b b'
    (fun c => hne (by rw [← e, ← e', c])) hm hm' hb hb'
  obtain ⟨_, _, _, rfl⟩ := sizesOf_some hb
  obtain ⟨_, _, _, rfl⟩ := sizesOf_some hb'
  rw [e, e'] at r
  exact r

variable {S G}

/-- A member's main table has as many places in a row as the group's. -/
theorem placeBits_main (hOk : GroupOk S G) {o : Nat} (hm : o ∈ G.members.toList)
    (hh : S.has o .main = true) : S.placeBits o .main = (layoutOf S G).logEll := by
  unfold Statement.has at hh
  unfold Statement.placeBits
  cases hx : S.oracles[o]? with
  | none =>
    rw [hx] at hh
    cases hh
  | some x =>
    rw [hx] at hh
    have h0 : 0 < x.shape.mainRows := by simpa [OracleShape.rows] using hh
    rcases hOk.mainCode o hm x hx with c | c
    · omega
    · have h1 : (x.shape.rows .main == 0) = false := by
        simp [OracleShape.rows]
        omega
      simp only [h1, c, Bool.false_eq_true, if_false]
      rfl

/-- A member's mask table has as many places in a row as the group's. -/
theorem placeBits_mask (hOk : GroupOk S G) {o : Nat} (hm : o ∈ G.members.toList)
    (hh : S.has o .mask = true) : S.placeBits o .mask = (layoutOf S G).logEllZk := by
  unfold Statement.has at hh
  unfold Statement.placeBits
  cases hx : S.oracles[o]? with
  | none =>
    rw [hx] at hh
    cases hh
  | some x =>
    rw [hx] at hh
    have h0 : 0 < x.shape.maskRows := by simpa [OracleShape.rows] using hh
    rcases hOk.maskCode o hm x hx with c | c
    · omega
    · have h1 : (x.shape.rows .mask == 0) = false := by
        simp [OracleShape.rows]
        omega
      simp only [h1, c, Bool.false_eq_true, if_false]
      rfl

/-- What the laws on rows use of a layout. -/
structure LayFacts (S : Statement) (G : Group) (L : GroupLayout) : Prop where
  find_of_mem : ∀ o, o ∈ G.members.toList → ∃ i, L.find o = some i
  mem_of_find : ∀ o i, L.find o = some i → o ∈ G.members.toList
  main_block : ∀ o i first, L.find o = some i → L.mainFirst.getD i none = some first →
    S.has o .main = true ∧ L.kept.getD i false = false ∧ BlockOk (S.rowBits o .main) first L.k
  main_block_of : ∀ o i, L.find o = some i → S.has o .main = true →
    L.kept.getD i false = false → ∃ first, L.mainFirst.getD i none = some first
  mask_block : ∀ o i first, L.find o = some i → L.maskFirst.getD i none = some first →
    S.has o .mask = true ∧ BlockOk (S.rowBits o .mask) first L.h
  mask_block_of : ∀ o i, L.find o = some i → S.has o .mask = true →
    ∃ first, L.maskFirst.getD i none = some first
  main_apart : ∀ o o' i i' a a', o ≠ o' → L.find o = some i → L.find o' = some i' →
    L.mainFirst.getD i none = some a → L.mainFirst.getD i' none = some a' →
    a + 2 ^ S.rowBits o .main ≤ a' ∨ a' + 2 ^ S.rowBits o' .main ≤ a
  mask_apart : ∀ o o' i i' a a', o ≠ o' → L.find o = some i → L.find o' = some i' →
    L.maskFirst.getD i none = some a → L.maskFirst.getD i' none = some a' →
    a + 2 ^ S.rowBits o .mask ≤ a' ∨ a' + 2 ^ S.rowBits o' .mask ≤ a
  main_places : ∀ o, o ∈ G.members.toList → S.has o .main = true → S.placeBits o .main = L.logEll
  mask_places : ∀ o, o ∈ G.members.toList → S.has o .mask = true →
    S.placeBits o .mask = L.logEllZk

/-- The layout that a statement gives a group has them all. -/
theorem layFacts {g : Nat} {L : GroupLayout} (hG : S.groups[g]? = some G)
    (hL : S.layout g = some L) (hOk : GroupOk S G) : LayFacts S G L := by
  rw [layout_eq S g G hG] at hL
  obtain rfl := Option.some.inj hL
  exact ⟨fun o h => find_of_mem (L := layoutOf S G) h,
    fun o i h => mem_of_find (L := layoutOf S G) h,
    fun o i first hf hm => main_block S G hf hm,
    fun o i hf hh hk => main_block_of S G hf hh hk,
    fun o i first hf hm => mask_block S G hf hm,
    fun o i hf hh => mask_block_of S G hf hh,
    fun o o' i i' a a' hne hf hf' hm hm' => main_apart S G hne hf hf' hm hm',
    fun o o' i i' a a' hne hf hf' hm hm' => mask_apart S G hne hf hf' hm hm',
    fun o hm hh => placeBits_main hOk hm hh,
    fun o hm hh => placeBits_mask hOk hm hh⟩

/-- **The layout is in order.** -/
theorem layoutRight : LayoutRight := by
  intro S g G L hG hL
  rw [layout_eq S g G hG] at hL
  obtain rfl := Option.some.inj hL
  exact ⟨fun o i first hf hm => (main_block S G hf hm).2.2,
    fun o i first hf hm => (mask_block S G hf hm).2,
    fun o o' i i' a a' hne hf hf' hm hm' => main_apart S G hne hf hf' hm hm',
    fun o o' i i' a a' hne hf hf' hm hm' => mask_apart S G hne hf hf' hm hm'⟩

end OnBytes.Means
