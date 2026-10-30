-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LayTables.lean: at the layout that the verifier's own function returns
(`Statement.layout`, OnBytes/Iop/Ground.lean) the group's two tables exist, and the laws on the
batching of the group's rows hold with nothing asked of the layout or of these tables. Definitions,
statements and proofs.

`combine_defect` (BatApply.lean) and `combine_few` (BatCount.lean), beside this file, ask four
things beside the rows' own conditions: `MainBlocksOk`, `MaskBlocksOk`, and of each of the group's
two tables that it holds, at every index at which an oracle message has a weight, that message's own
entry. LayBlocks.lean pays the first two. Here the last two are paid.
  `mainWeight_ne`, `maskWeight_ne`: what a weight other than 0 says: it is 1; the message is a
    member with a block; the row of the index lies in that block.
  `mainWeight_apart`, `maskWeight_apart`: at no index do two oracle messages have a weight.
  `groupMain`, `groupMask`: the group's two tables, made of the oracle messages' own tables.
  `groupMain_at`, `groupMask_at`: they hold what is asked.
  `defect_at_layout`: `combine_defect` at that layout and these tables.
  `few_at_layout`: `combine_few` there: the oracle messages' tables fixed first, one row that does
    not hold on them is saved by at most (the number of rows - 1) values of the drawn element.

Limits. `RowFits` and `MaskFits` are still asked of the rows. The statement S is the one at which
`Bat.combine` is called and at which the layout is made: that the closing of a link makes the layout
just before it marks the group's test as begun, and that this marking leaves the layout as it was,
is not shown here. ONE OBJECT: the count is at fixed tables: no bound on a prover's chance (the
limits of BatCount.lean).

-/
import Johnson.Desc.First.Close.Law.LayWeights
import Johnson.Desc.First.Close.Law.BatCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.LayLaw

variable {K : Type} [CommRing K]

/-- What a weight other than 0 on the main table says, at the verifier's own layout: the message is
a member at a place i with a block from the row f on, and the row of J lies in that block. -/
theorem mainWeight_ne (S : Statement) (G : Group) (L : GroupLayout) (hM : MainBlocksOk S L)
    (hL : L.mainFirst = (layBlocks (laySizes S G .main)).1) (hmem : L.members = G.members)
    (o J : Nat) (h : mainWeight (K := K) S L o J ≠ 0) :
    mainWeight (K := K) S L o J = 1 ∧ ∃ i f, L.find o = some i ∧
      (layBlocks (laySizes S G .main)).1[i]? = some (some f) ∧
      (laySizes S G .main)[i]? = some (some (S.rowBits o .main)) ∧
      f ≤ J % 2 ^ L.k ∧ J % 2 ^ L.k < f + 2 ^ S.rowBits o .main := by
  cases hf : L.find o with
  | none =>
    refine absurd ?_ h
    unfold mainWeight
    rw [hf]
  | some i =>
    cases hk : L.kept.getD i false with
    | true =>
      refine absurd ?_ h
      unfold mainWeight
      rw [hf]
      simp [hk]
    | false =>
      cases hm : L.mainFirst.getD i none with
      | none =>
        refine absurd ?_ h
        unfold mainWeight
        rw [hf]
        simp [hk, hm]
      | some f =>
        have hb := hM o i f hf hm
        have e := mainWeight_rows (K := K) S L o i f J hf hk hm hb
        by_cases hc : f ≤ J % 2 ^ L.k ∧ J % 2 ^ L.k < f + 2 ^ S.rowBits o .main
        · rw [if_pos hc] at e
          have hm' : (layBlocks (laySizes S G .main)).1[i]? = some (some f) := by
            rw [← hL]
            exact (getD_some _ _ _).1 hm
          obtain ⟨s, a1, -, -⟩ := (layBlocks_laid (laySizes S G .main)).block i f hm'
          have hs := laySizes_some S G .main i s a1
          have ho : G.members.getD i noId = o := by
            rw [← hmem]
            exact find_getD L o i hf
          rw [ho] at hs
          subst hs
          exact ⟨e, i, f, rfl, hm', a1, hc.1, hc.2⟩
        · rw [if_neg hc] at e
          exact absurd e h

/-- **AT NO INDEX OF THE GROUP's MAIN TABLE DO TWO ORACLE MESSAGES HAVE A WEIGHT**, at the layout
that the verifier's own function returns. -/
theorem mainWeight_apart (S : Statement) (g : Nat) (L : GroupLayout) (h : S.layout g = some L)
    (o o' J : Nat) (hne : o ≠ o') (hw : mainWeight (K := K) S L o J ≠ 0) :
    mainWeight (K := K) S L o' J = 0 := by
  by_contra hw'
  have hM := (layout_blocksOk S g L h).1
  cases hG : S.groups[g]? with
  | none =>
    unfold Statement.layout at h
    rw [hG] at h
    cases h
  | some G =>
    rw [layout_eq S g G hG] at h
    obtain rfl := Option.some.inj h
    obtain ⟨-, i, f, a1, a2, a3, a4, a5⟩ := mainWeight_ne S G _ hM rfl rfl o J hw
    obtain ⟨-, j, f', b1, b2, b3, b4, b5⟩ := mainWeight_ne S G _ hM rfl rfl o' J hw'
    have hij : i ≠ j := by
      rintro rfl
      exact hne ((find_getD _ o i a1).symm.trans (find_getD _ o' i b1))
    rcases (layBlocks_laid (laySizes S G .main)).apart i j f f' _ _ hij a2 b2 a3 b3 with c | c <;>
      omega

/-- The group's main table, made of the oracle messages' own main tables. -/
def groupMain (S : Statement) (L : GroupLayout) (N : Nat) (tab : Nat → Nat → K) (J : Nat) : K :=
  ∑ o ∈ Finset.range N, mainWeight (K := K) S L o J * tab o (mainBack S L o J)

/-- **THE GROUP's MAIN TABLE EXISTS**: at every index at which an oracle message has a weight,
`groupMain` holds the entry of that message's own main table that belongs to the index. -/
theorem groupMain_at (S : Statement) (g : Nat) (L : GroupLayout) (h : S.layout g = some L)
    (N : Nat) (hN : L.top ≤ N) (tab : Nat → Nat → K) (o J : Nat)
    (hw : mainWeight (K := K) S L o J ≠ 0) :
    groupMain S L N tab J = tab o (mainBack S L o J) := by
  have hoN : o < N := by
    by_contra hn
    exact hw (mainWeight_top S L o J (hN.trans (Nat.le_of_not_lt hn)))
  have h1 : mainWeight (K := K) S L o J = 1 := by
    have hM := (layout_blocksOk S g L h).1
    cases hG : S.groups[g]? with
    | none =>
      unfold Statement.layout at h
      rw [hG] at h
      cases h
    | some G =>
      rw [layout_eq S g G hG] at h
      obtain rfl := Option.some.inj h
      exact (mainWeight_ne S G _ hM rfl rfl o J hw).1
  unfold groupMain
  rw [Finset.sum_eq_single o]
  · rw [h1, one_mul]
  · intro o' _ hne
    rw [mainWeight_apart S g L h o o' J (Ne.symm hne) hw, zero_mul]
  · intro hn
    exact absurd (Finset.mem_range.2 hoN) hn

/-! ## The mask table -/

/-- What a weight other than 0 on the mask table says. -/
theorem maskWeight_ne (S : Statement) (G : Group) (L : GroupLayout) (hZ : MaskBlocksOk S L)
    (hL : L.maskFirst = (layBlocks (laySizes S G .mask)).1) (hmem : L.members = G.members)
    (o J : Nat) (h : maskWeight (K := K) S L o J ≠ 0) :
    maskWeight (K := K) S L o J = 1 ∧ ∃ i f, L.find o = some i ∧
      (layBlocks (laySizes S G .mask)).1[i]? = some (some f) ∧
      (laySizes S G .mask)[i]? = some (some (S.rowBits o .mask)) ∧
      f ≤ J % 2 ^ L.h ∧ J % 2 ^ L.h < f + 2 ^ S.rowBits o .mask := by
  cases hf : L.find o with
  | none =>
    refine absurd ?_ h
    unfold maskWeight
    rw [hf]
  | some i =>
    cases hm : L.maskFirst.getD i none with
    | none =>
      refine absurd ?_ h
      unfold maskWeight
      rw [hf]
      simp [hm]
    | some f =>
      have hb := hZ o i f hf hm
      have e := maskWeight_rows (K := K) S L o i f J hf hm hb
      by_cases hc : f ≤ J % 2 ^ L.h ∧ J % 2 ^ L.h < f + 2 ^ S.rowBits o .mask
      · rw [if_pos hc] at e
        have hm' : (layBlocks (laySizes S G .mask)).1[i]? = some (some f) := by
          rw [← hL]
          exact (getD_some _ _ _).1 hm
        obtain ⟨s, a1, -, -⟩ := (layBlocks_laid (laySizes S G .mask)).block i f hm'
        have hs := laySizes_some S G .mask i s a1
        have ho : G.members.getD i noId = o := by
          rw [← hmem]
          exact find_getD L o i hf
        rw [ho] at hs
        subst hs
        exact ⟨e, i, f, rfl, hm', a1, hc.1, hc.2⟩
      · rw [if_neg hc] at e
        exact absurd e h

/-- At no index of the group's mask table do two oracle messages have a weight. -/
theorem maskWeight_apart (S : Statement) (g : Nat) (L : GroupLayout) (h : S.layout g = some L)
    (o o' J : Nat) (hne : o ≠ o') (hw : maskWeight (K := K) S L o J ≠ 0) :
    maskWeight (K := K) S L o' J = 0 := by
  by_contra hw'
  have hZ := (layout_blocksOk S g L h).2
  cases hG : S.groups[g]? with
  | none =>
    unfold Statement.layout at h
    rw [hG] at h
    cases h
  | some G =>
    rw [layout_eq S g G hG] at h
    obtain rfl := Option.some.inj h
    obtain ⟨-, i, f, a1, a2, a3, a4, a5⟩ := maskWeight_ne S G _ hZ rfl rfl o J hw
    obtain ⟨-, j, f', b1, b2, b3, b4, b5⟩ := maskWeight_ne S G _ hZ rfl rfl o' J hw'
    have hij : i ≠ j := by
      rintro rfl
      exact hne ((find_getD _ o i a1).symm.trans (find_getD _ o' i b1))
    rcases (layBlocks_laid (laySizes S G .mask)).apart i j f f' _ _ hij a2 b2 a3 b3 with c | c <;>
      omega

/-- The group's mask table, made of the oracle messages' own mask tables. -/
def groupMask (S : Statement) (L : GroupLayout) (N : Nat) (tab : Nat → Nat → K) (J : Nat) : K :=
  ∑ o ∈ Finset.range N, maskWeight (K := K) S L o J * tab o (maskBack S L o J)

/-- The group's mask table exists. -/
theorem groupMask_at (S : Statement) (g : Nat) (L : GroupLayout) (h : S.layout g = some L)
    (N : Nat) (hN : L.top ≤ N) (tab : Nat → Nat → K) (o J : Nat)
    (hw : maskWeight (K := K) S L o J ≠ 0) :
    groupMask S L N tab J = tab o (maskBack S L o J) := by
  have hoN : o < N := by
    by_contra hn
    exact hw (maskWeight_top S L o J (hN.trans (Nat.le_of_not_lt hn)))
  have h1 : maskWeight (K := K) S L o J = 1 := by
    have hZ := (layout_blocksOk S g L h).2
    cases hG : S.groups[g]? with
    | none =>
      unfold Statement.layout at h
      rw [hG] at h
      cases h
    | some G =>
      rw [layout_eq S g G hG] at h
      obtain rfl := Option.some.inj h
      exact (maskWeight_ne S G _ hZ rfl rfl o J hw).1
  unfold groupMask
  rw [Finset.sum_eq_single o]
  · rw [h1, one_mul]
  · intro o' _ hne
    rw [maskWeight_apart S g L h o o' J (Ne.symm hne) hw, zero_mul]
  · intro hn
    exact absurd (Finset.mem_range.2 hoN) hn

/-! ## The batching at the verifier's own layout -/

/-- **THE BATCHED ROW's DEFECT, AT THE LAYOUT THAT THE VERIFIER's OWN FUNCTION RETURNS**: nothing is
asked of the layout or of the group's tables, which are made of the oracle messages' own tables. -/
theorem defect_at_layout (ρ : Model.Reading K) (S : Statement) (g : Nat) (L : GroupLayout)
    (h : S.layout g = some L) (rows : Array Row) (x : E) (out : GroupRow)
    (hc : Bat.combine S g ⟨L, rows⟩ x = some out)
    (hr : ∀ r ∈ rows.toList, RowFits S r ∧ MaskFits S L r) (N : Nat) (hN : L.top ≤ N)
    (tab : Nat → Part → Nat → K) :
    groupSum ρ S L N tab (groupMain S L N fun o => tab o .main)
        (groupMask S L N fun o => tab o .mask) out - ρ.val out.target =
      hornerSum (ρ.val x) (rows.toList.map fun r => rowSumIn ρ S L N tab r - ρ.val r.target) :=
  combine_defect ρ S g ⟨L, rows⟩ x out hc (layout_blocksOk S g L h).1 (layout_blocksOk S g L h).2
    hr N hN tab _ _ (fun o J hw => groupMain_at S g L h N hN (fun o => tab o .main) o J hw)
    (fun o J hw => groupMask_at S g L h N hN (fun o => tab o .mask) o J hw)

open Classical in
/-- **AT FIXED TABLES OF THE ORACLE MESSAGES, A FALSE ROW IS SAVED BY FEW DRAWN ELEMENTS**, at the
layout that the verifier's own function returns. -/
theorem few_at_layout {F : Type} [Field F] [Fintype F] (ρ : Model.Reading F) (S : Statement)
    (g : Nat) (L : GroupLayout) (h : S.layout g = some L) (rows : Array Row)
    (hr : ∀ r ∈ rows.toList, RowFits S r ∧ MaskFits S L r) (N : Nat) (hN : L.top ≤ N)
    (tab : Nat → Part → Nat → F)
    (hbad : ∃ r ∈ rows.toList, rowSumIn ρ S L N tab r ≠ ρ.val r.target) :
    (Finset.univ.filter fun y : F => ∃ x out, ρ.val x = y ∧
      Bat.combine S g ⟨L, rows⟩ x = some out ∧
      groupSum ρ S L N tab (groupMain S L N fun o => tab o .main)
        (groupMask S L N fun o => tab o .mask) out = ρ.val out.target).card ≤ rows.size - 1 :=
  combine_few ρ S g ⟨L, rows⟩ (layout_blocksOk S g L h).1 (layout_blocksOk S g L h).2 hr N hN tab
    _ _ (fun o J hw => groupMain_at S g L h N hN (fun o => tab o .main) o J hw)
    (fun o J hw => groupMask_at S g L h N hN (fun o => tab o .mask) o J hw) hbad

end OnBytes.LayLaw

#print axioms OnBytes.LayLaw.few_at_layout
#print axioms OnBytes.LayLaw.defect_at_layout
#print axioms OnBytes.LayLaw.maskWeight_apart
#print axioms OnBytes.LayLaw.groupMask_at
#print axioms OnBytes.LayLaw.mainWeight_apart
#print axioms OnBytes.LayLaw.groupMain_at
