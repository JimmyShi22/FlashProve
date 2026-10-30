-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LayBlocks.lean: the layout of a group, as the verifier's own function
makes it (`Statement.layout`, over `layBlocks`: OnBytes/Iop/Ground.lean), has its blocks in order,
at every statement and every group. Definitions, statements and proofs.

The laws on the batching of a group's rows (OnBytes/Iop/RowLaws.lean, MaskLaws.lean; BatVector.lean,
BatApply.lean and BatCount.lean beside this file) ask `MainBlocksOk` and `MaskBlocksOk`: each
member's block of rows begins at a multiple of its number of rows and lies inside the group's table.
The library shows that of two written layouts (`link_blocksOk`, OnBytes/Slice/BlkLinkLay.lean;
`layout_one`, OnBytes/Slice/BlkCsLay.lean). Here it is shown of whatever `Statement.layout` returns.
  `Laid sizes acc`: what holds of the blocks laid so far: each belongs to a member with a size,
    begins at a multiple of its number of rows and ends inside the rows taken; two blocks lie apart.
  `layStep`: one step of `layBlocks`, with a name. `layStep_laid`, `layInner_laid`, `layOuter_laid`:
    a step, a pass over the members, all passes keep `Laid`. Why: blocks are laid by falling size,
    so the rows taken so far are a multiple of the next block's number of rows.
  `layBlocks_laid`: `Laid sizes (layBlocks sizes)`, at every array of sizes.
  `laySizes`, `layout_eq`: `Statement.layout` written out. `laySizes_some`, `idxOf_getD`,
    `find_getD`.
  `layout_blocksOk`: if `S.layout g = some L` then `MainBlocksOk S L` and `MaskBlocksOk S L`.

Limits. That two members' blocks lie apart is in `Laid` and is not yet carried to the weights
(`mainWeight`, `maskWeight`). That every member with a size gets a block is not shown. Nothing on
the rows (`RowFits`, `MaskFits`), on place bits, or on soundness.

-/
import OnBytes.Iop.RowLaws
import OnBytes.Iop.MaskLaws
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.LayLaw

/-- What holds of the blocks laid so far. sizes: the members' sizes. acc: the first rows, and the
rows taken in all. Each block that is laid belongs to a member with a size, begins at a multiple of
its number of rows and ends inside the rows taken; two blocks lie apart. -/
structure Laid (sizes : Array (Option Nat)) (acc : Array (Option Nat) × Nat) : Prop where
  size : acc.1.size = sizes.size
  block : ∀ (i f : Nat), acc.1[i]? = some (some f) →
    ∃ s, sizes[i]? = some (some s) ∧ 2 ^ s ∣ f ∧ f + 2 ^ s ≤ acc.2
  apart : ∀ (i j f f' s s' : Nat), i ≠ j → acc.1[i]? = some (some f) →
    acc.1[j]? = some (some f') →
    sizes[i]? = some (some s) → sizes[j]? = some (some s') → f + 2 ^ s ≤ f' ∨ f' + 2 ^ s' ≤ f

/-- One step of layBlocks, with a name. -/
def layStep (sizes : Array (Option Nat)) (e : Nat) (acc : Array (Option Nat) × Nat) (i : Nat) :
    Array (Option Nat) × Nat :=
  if sizes.getD i none == some e then (acc.1.setIfInBounds i (some acc.2), acc.2 + 2 ^ e) else acc

theorem getD_some {α : Type} (a : Array (Option α)) (i : Nat) (x : α) :
    a.getD i none = some x ↔ a[i]? = some (some x) := by
  rw [Array.getD_eq_getD_getElem?]
  cases a[i]? <;> simp

theorem layStep_laid (sizes : Array (Option Nat)) (e : Nat) (acc : Array (Option Nat) × Nat)
    (i : Nat) (h : Laid sizes acc) (hd : 2 ^ e ∣ acc.2) :
    Laid sizes (layStep sizes e acc i) ∧ 2 ^ e ∣ (layStep sizes e acc i).2 := by
  unfold layStep
  split
  · rename_i hs
    have hs' : sizes[i]? = some (some e) := (getD_some _ _ _).1 (eq_of_beq hs)
    refine ⟨⟨by simpa using h.size, ?_, ?_⟩, Dvd.dvd.add hd (dvd_refl _)⟩
    · intro j f hj
      dsimp only at hj ⊢
      rw [Array.getElem?_setIfInBounds] at hj
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at hj
        split at hj
        · obtain rfl : acc.2 = f := Option.some.inj (Option.some.inj hj)
          exact ⟨e, hs', hd, le_refl _⟩
        · cases hj
      · rw [if_neg hij] at hj
        obtain ⟨s, a1, a2, a3⟩ := h.block j f hj
        exact ⟨s, a1, a2, a3.trans (Nat.le_add_right _ _)⟩
    · intro j j' f f' s s' hne hj hj' hsj hsj'
      dsimp only at hj hj'
      rw [Array.getElem?_setIfInBounds] at hj hj'
      by_cases h1 : i = j
      · subst h1
        rw [if_pos rfl] at hj
        rw [if_neg hne] at hj'
        split at hj
        · obtain rfl : acc.2 = f := Option.some.inj (Option.some.inj hj)
          obtain ⟨t, a1, -, a3⟩ := h.block j' f' hj'
          rw [a1] at hsj'
          obtain rfl : t = s' := Option.some.inj (Option.some.inj hsj')
          exact Or.inr a3
        · cases hj
      · rw [if_neg h1] at hj
        by_cases h2 : i = j'
        · subst h2
          rw [if_pos rfl] at hj'
          split at hj'
          · obtain rfl : acc.2 = f' := Option.some.inj (Option.some.inj hj')
            obtain ⟨t, a1, -, a3⟩ := h.block j f hj
            rw [a1] at hsj
            obtain rfl : t = s := Option.some.inj (Option.some.inj hsj)
            exact Or.inl a3
          · cases hj'
        · rw [if_neg h2] at hj'
          exact h.apart j j' f f' s s' hne hj hj' hsj hsj'
  · exact ⟨h, hd⟩

theorem layInner_laid (sizes : Array (Option Nat)) (e : Nat) : ∀ (l : List Nat)
    (acc : Array (Option Nat) × Nat), Laid sizes acc → 2 ^ e ∣ acc.2 →
    Laid sizes (l.foldl (layStep sizes e) acc) ∧ 2 ^ e ∣ (l.foldl (layStep sizes e) acc).2
  | [], _, h, hd => ⟨h, hd⟩
  | i :: l, acc, h, hd => by
    obtain ⟨a, b⟩ := layStep_laid sizes e acc i h hd
    exact layInner_laid sizes e l _ a b

theorem layOuter_laid (sizes : Array (Option Nat)) (l : List Nat) : ∀ (m : Nat)
    (acc : Array (Option Nat) × Nat), Laid sizes acc → 2 ^ m ∣ acc.2 →
    Laid sizes ((List.range (m + 1)).reverse.foldl (fun a e => l.foldl (layStep sizes e) a) acc)
  | 0, acc, h, hd => by
    simpa using (layInner_laid sizes 0 l acc h hd).1
  | m + 1, acc, h, hd => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    obtain ⟨a, b⟩ := layInner_laid sizes (m + 1) l acc h hd
    exact layOuter_laid sizes l m _ a ((pow_dvd_pow 2 (Nat.le_succ m)).trans b)

/-- **The blocks that layBlocks lays**: each belongs to a member with a size, begins at a multiple
of its number of rows, ends inside the rows taken in all; two blocks lie apart. -/
theorem layBlocks_laid (sizes : Array (Option Nat)) : Laid sizes (layBlocks sizes) := by
  unfold layBlocks
  have h0 : ∀ (i f : Nat),
      (Array.replicate sizes.size (none : Option Nat))[i]? ≠ some (some f) := by
    intro i f hi
    rw [Array.getElem?_replicate] at hi
    split at hi <;> cases hi
  exact layOuter_laid sizes (List.range sizes.size) _ _
    ⟨by simp, fun i f hi => absurd hi (h0 i f), fun i _ f _ _ _ _ hi => absurd hi (h0 i f)⟩
    (dvd_zero _)

/-! ## The layout of a group -/

/-- The sizes that `Statement.layout` hands to layBlocks, with a name. -/
def laySizes (S : Statement) (G : Group) (part : Part) : Array (Option Nat) :=
  (Array.range G.members.size).map fun i =>
    let o := G.members.getD i noId
    if S.has o part && !(part == .main && G.kept.getD i false) then some (S.rowBits o part)
    else none

/-- `Statement.layout`, written out. -/
theorem layout_eq (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    S.layout g = some
      { k := max (max (ceilLog2 (layBlocks (laySizes S G .main)).2)
          (ceilLog2 (layBlocks (laySizes S G .mask)).2)) 1,
        h := ceilLog2 (layBlocks (laySizes S G .mask)).2,
        logEll := (S.codes.base.getD G.code default).logEll,
        logEllZk := (S.codes.mask.getD G.maskCode default).logEll,
        members := G.members, kept := G.kept,
        mainFirst := (layBlocks (laySizes S G .main)).1,
        maskFirst := (layBlocks (laySizes S G .mask)).1 } := by
  unfold Statement.layout
  rw [hG]
  rfl

/-- A size that is there is the row bits of the member at that place. -/
theorem laySizes_some (S : Statement) (G : Group) (part : Part) (i s : Nat)
    (h : (laySizes S G part)[i]? = some (some s)) : s = S.rowBits (G.members.getD i noId) part := by
  unfold laySizes at h
  rw [Array.getElem?_map] at h
  cases hr : (Array.range G.members.size)[i]? with
  | none => rw [hr] at h; cases h
  | some j =>
    have hj : j = i := by
      rw [Array.getElem?_range] at hr
      split at hr
      · exact (Option.some.inj hr).symm
      · cases hr
    subst hj
    rw [hr] at h
    have h' := Option.some.inj h
    dsimp only at h'
    split at h'
    · exact (Option.some.inj h').symm
    · cases h'

/-- The place that is found for a number in an array holds it. -/
theorem idxOf_getD (a : Array Nat) (o i d : Nat) (h : a.idxOf? o = some i) : a.getD i d = o := by
  obtain ⟨l⟩ := a
  rw [List.idxOf?_toArray] at h
  obtain ⟨h1, h2, -⟩ := List.idxOf?_eq_some_iff.1 h
  rw [← h2]
  simp [Array.getD, h1]

/-- The place that is found for an oracle message holds it. -/
theorem find_getD (L : GroupLayout) (o i : Nat) (h : L.find o = some i) :
    L.members.getD i noId = o := idxOf_getD L.members o i noId h

/-- **THE LAYOUT THAT THE VERIFIER's OWN FUNCTION RETURNS MEETS MainBlocksOk AND MaskBlocksOk**, at
every statement and group. -/
theorem layout_blocksOk (S : Statement) (g : Nat) (L : GroupLayout) (h : S.layout g = some L) :
    MainBlocksOk S L ∧ MaskBlocksOk S L := by
  cases hG : S.groups[g]? with
  | none =>
    unfold Statement.layout at h
    rw [hG] at h
    cases h
  | some G =>
    rw [layout_eq S g G hG] at h
    obtain rfl := Option.some.inj h
    constructor
    · intro o i first hf hm
      have hm' := (getD_some _ _ _).1 hm
      obtain ⟨s, a1, a2, a3⟩ := (layBlocks_laid (laySizes S G .main)).block i first hm'
      have hs := laySizes_some S G .main i s a1
      have ho : G.members.getD i noId = o := find_getD _ o i hf
      rw [ho] at hs
      subst hs
      refine ⟨Nat.mod_eq_zero_of_dvd a2, a3.trans ?_⟩
      refine (Slice.le_two_pow_ceilLog2 _).trans (Nat.pow_le_pow_right (by decide) ?_)
      exact (le_max_left _ _).trans (le_max_left _ _)
    · intro o i first hf hm
      have hm' := (getD_some _ _ _).1 hm
      obtain ⟨s, a1, a2, a3⟩ := (layBlocks_laid (laySizes S G .mask)).block i first hm'
      have hs := laySizes_some S G .mask i s a1
      have ho : G.members.getD i noId = o := find_getD _ o i hf
      rw [ho] at hs
      subst hs
      exact ⟨Nat.mod_eq_zero_of_dvd a2, a3.trans (Slice.le_two_pow_ceilLog2 _)⟩

end OnBytes.LayLaw

#print axioms OnBytes.LayLaw.layBlocks_laid
#print axioms OnBytes.LayLaw.layout_blocksOk
