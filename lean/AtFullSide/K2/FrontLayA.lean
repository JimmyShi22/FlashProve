-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FrontLayA.lean: helpers for AtFullSide/K2/FrontLay.lean, at letters: what follows, for
any statement S and any carried rows old, from "the layout's fields are the group G's own layout"
(LayIs, Johnson/Desc/K2/Honest/Returns/LayoutReached.lean) and from the text of the definitions
sizesAt, membersTrue, shapeOf, keptOf, keptNos. No definition. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.K2.Honest.Returns.LayoutReached
import Johnson.Desc.K2.Honest.Carry.OfRows
import Johnson.Desc.K2.Honest.Inner.Statement
import Johnson.Desc.Means.Blocks
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open OnBytes
open OnBytes.Slice (GE readE readL)
open VerifiableInference.Desc.K2.Honest (Sizes GroupMember sizesAt membersTrue keptOf shapeOf zeroG)
open VerifiableInference.Desc.K2.Honest.Returns (LayIs)
open VerifiableInference.Desc.Own (keptNos layoutOf blockBits tableThere)

/-- The fold's challenges, read one by one, are the list's entries read. -/
theorem gammaRead (g : List E) (t : Nat) : (g.map readE).getD t zeroG = readL g t := by
  have hz : zeroG = readE zeroE := by
    rw [OnBytes.Slice.readE_zero]
    exact OnBytes.Slice.toE_zeroE
  unfold OnBytes.Slice.readL
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases g[t]? with
  | none => exact hz
  | some a => rfl

/-- A list is its entries, read in order. -/
theorem list_eq_range_map {α : Type} (d : α) (l : List α) :
    l = (List.range l.length).map (fun w => l.getD w d) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h1]

/-- An entry of the pairs of members and marks. -/
theorem zip_at (M : Array Nat) (K : Array Bool) (hsz : K.size = M.size) {w : Nat}
    (hw : w < M.size) :
    (M.zip K).toList.getD w (noId, false) = (M.getD w noId, K.getD w false) := by
  have hk : w < K.size := hsz ▸ hw
  have hz : w < (M.zip K).size := by
    rw [Array.size_zip]
    omega
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_eq_getElem hz,
    Array.getElem_zip, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hw, Array.getElem?_eq_getElem hk]
  rfl

variable {S : Statement} {old : SingleRows}

/-- As many members as the layout has. -/
theorem members_length (hsz : old.layout.kept.size = old.layout.members.size) :
    (membersTrue S old).length = old.layout.members.size := by
  unfold membersTrue
  rw [List.length_map, Array.length_toList, Array.size_zip, hsz, Nat.min_self]

/-- A member, by its number. -/
theorem member_at (hsz : old.layout.kept.size = old.layout.members.size) {w : Nat}
    (hw : w < old.layout.members.size) :
    (membersTrue S old)[w]? =
      some { shape := (S.oracles.getD (old.layout.members.getD w noId) default).shape,
             kept := old.layout.kept.getD w false } := by
  have e := zip_at old.layout.members old.layout.kept hsz hw
  have hz : w < (old.layout.members.zip old.layout.kept).toList.length := by
    rw [Array.length_toList, Array.size_zip, hsz, Nat.min_self]
    exact hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz] at e
  unfold membersTrue
  rw [List.getElem?_map, List.getElem?_eq_getElem hz]
  have e' : (old.layout.members.zip old.layout.kept).toList[w] =
      (old.layout.members.getD w noId, old.layout.kept.getD w false) := e
  rw [e']
  rfl

theorem shapeOf_at (hsz : old.layout.kept.size = old.layout.members.size) {w : Nat}
    (hw : w < old.layout.members.size) :
    shapeOf (membersTrue S old) w =
      (S.oracles.getD (old.layout.members.getD w noId) default).shape := by
  show (Option.map (fun x => x.shape) (membersTrue S old)[w]?).getD {} = _
  rw [member_at hsz hw]
  rfl

theorem keptOf_at (hsz : old.layout.kept.size = old.layout.members.size) {w : Nat}
    (hw : w < old.layout.members.size) :
    keptOf (membersTrue S old) w = old.layout.kept.getD w false := by
  show (Option.map (fun x => x.kept) (membersTrue S old)[w]?).getD false = _
  rw [member_at hsz hw]
  rfl

/-- The kept members' numbers, off the members and off the layout. -/
theorem keptNos_true (hsz : old.layout.kept.size = old.layout.members.size) :
    ((List.range (membersTrue S old).length).filter fun w => keptOf (membersTrue S old) w) =
      keptNos old.layout := by
  rw [members_length hsz]
  unfold VerifiableInference.Desc.Own.keptNos
  exact List.filter_congr fun w hw => keptOf_at hsz (List.mem_range.1 hw)

/-- The kept members, in the order of sending, by their numbers. -/
theorem switchKept_list (hsz : old.layout.kept.size = old.layout.members.size) :
    (switchKept old).toList = (keptNos old.layout).map fun w => old.layout.members.getD w noId := by
  have hn : (old.layout.members.zip old.layout.kept).toList.length = old.layout.members.size := by
    rw [Array.length_toList, Array.size_zip, hsz, Nat.min_self]
  have e := list_eq_range_map (noId, false) (old.layout.members.zip old.layout.kept).toList
  rw [hn] at e
  unfold switchKept VerifiableInference.Desc.Own.keptNos
  rw [Array.toList_map, Array.toList_filter, e, List.filter_map, List.map_map]
  have hf : (List.range old.layout.members.size).filter
      ((fun x : Nat × Bool => x.2) ∘
        fun w => (old.layout.members.zip old.layout.kept).toList.getD w (noId, false)) =
      (List.range old.layout.members.size).filter fun w => old.layout.kept.getD w false :=
    List.filter_congr fun w hw => by
      show ((old.layout.members.zip old.layout.kept).toList.getD w (noId, false)).2 = _
      rw [zip_at _ _ hsz (List.mem_range.1 hw)]
  rw [hf]
  apply List.map_congr_left
  intro w hw
  show ((old.layout.members.zip old.layout.kept).toList.getD w (noId, false)).1 = _
  rw [zip_at _ _ hsz (List.mem_range.1 (List.mem_filter.1 hw).1)]

/-- The kept members' shapes, off the sizes and off the members. -/
theorem keptShapes_true (hsz : old.layout.kept.size = old.layout.members.size) (T : SwitchTarget) :
    (sizesAt S old T).kept = (keptNos old.layout).map (shapeOf (membersTrue S old)) := by
  show List.map (fun o => (S.oracles.getD o default).shape) (switchKept old).toList = _
  rw [switchKept_list hsz, List.map_map]
  apply List.map_congr_left
  intro w hw
  have hw' : w < old.layout.members.size := by
    unfold VerifiableInference.Desc.Own.keptNos at hw
    exact List.mem_range.1 (List.mem_filter.1 hw).1
  rw [shapeOf_at hsz hw']
  rfl

/-- The number of pairs (kept member, main row). -/
theorem keptPairs_length (l : List OracleShape) :
    (l.zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b)).length =
      (l.map fun s => s.mainRows).sum := by
  rw [List.length_flatMap]
  have : (l.zipIdx.map fun s => ((List.range s.1.mainRows).map fun b => (s.2, b)).length) =
      l.zipIdx.map fun s => s.1.mainRows := by
    apply List.map_congr_left
    intro s _
    rw [List.length_map, List.length_range]
  rw [this]
  have h2 : (l.zipIdx.map fun s => s.1.mainRows) =
      (l.zipIdx.map Prod.fst).map fun s => s.mainRows := by
    rw [List.map_map]
    rfl
  rw [h2, List.zipIdx_map_fst]

/-- The kept rows' number in the form of the front's layout, from the form of OldFits.rows. -/
theorem keptRows_true (T : SwitchTarget)
    (hr : old.keptRows = (List.map (fun o => (S.oracles.getD o default).shape.mainRows)
      (switchKept old).toList).sum) :
    old.keptRows = ((Sizes.kept (sizesAt S old T)).zipIdx.flatMap fun s =>
      (List.range s.1.mainRows).map fun b => (s.2, b)).length := by
  rw [keptPairs_length, hr]
  show _ = (List.map (fun s => s.mainRows)
    (List.map (fun o => (S.oracles.getD o default).shape) (switchKept old).toList)).sum
  rw [List.map_map]
  rfl

/-- An entry of the blocks' bits. -/
theorem blockBits_at (G : Group) (part : Part) {w : Nat} (hw : w < G.members.size) :
    (blockBits S G part).getD w none =
      if tableThere S (G.members.getD w noId) part && !(part == .main && G.kept.getD w false) then
        some (S.rowBits (G.members.getD w noId) part)
      else none := by
  unfold VerifiableInference.Desc.Own.blockBits
  have h1 : w < (Array.range G.members.size).size := by
    rw [Array.size_range]
    exact hw
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem h1,
    Array.getElem_range]
  rfl

/-- Where a member has a block, its rows fit the block. -/
theorem rows_le_of_bits (G : Group) (part : Part) {w a : Nat} (hw : w < G.members.size)
    (ha : (blockBits S G part).getD w none = some a) :
    ((S.oracles.getD (G.members.getD w noId) default).shape.rows part) ≤ 2 ^ a := by
  rw [blockBits_at G part hw] at ha
  by_cases hc : (tableThere S (G.members.getD w noId) part &&
      !(part == .main && G.kept.getD w false)) = true
  · rw [if_pos hc] at ha
    obtain rfl : S.rowBits (G.members.getD w noId) part = a := Option.some.inj ha
    have ht : tableThere S (G.members.getD w noId) part = true :=
      (Eq.mp (Bool.and_eq_true _ _) hc).1
    unfold VerifiableInference.Desc.Own.tableThere at ht
    unfold Statement.rowBits
    rw [Array.getD_eq_getD_getElem?]
    cases ho : S.oracles[G.members.getD w noId]? with
    | none =>
      rw [ho] at ht
      cases ht
    | some x => exact OnBytes.Slice.le_two_pow_ceilLog2 _
  · rw [if_neg hc] at ha
    cases ha

/-- A kept member has no block among the main rows. -/
theorem keptFirst_true {G : Group} (hL : LayIs S G old) : ∀ w, w < old.layout.members.size →
    old.layout.kept.getD w false = true → old.layout.mainFirst.getD w none = none := by
  intro w hw hk
  rw [hL.mainFirst]
  show (layBlocks (blockBits S G .main)).1.getD w none = none
  cases hf : (layBlocks (blockBits S G .main)).1.getD w none with
  | none => rfl
  | some f =>
    obtain ⟨a, ha, -⟩ := (OnBytes.Means.layBlocks_right _).1 w f hf
    rw [hL.members] at hw
    rw [hL.kept] at hk
    rw [blockBits_at G .main hw, hk] at ha
    simp at ha

/-- Two members' blocks lie apart: the common form. -/
theorem apart_true {G : Group} (hL : LayIs S G old) (part : Part) (first : Array (Option Nat))
    (hfirst : first = (layBlocks (blockBits S G part)).1) :
    ∀ w w', w < old.layout.members.size → w' < old.layout.members.size → w ≠ w' → ∀ f f',
    first.getD w none = some f → first.getD w' none = some f' →
    f + (shapeOf (membersTrue S old) w).rows part ≤ f' ∨
      f' + (shapeOf (membersTrue S old) w').rows part ≤ f := by
  intro w w' hw hw' hne f f' hf hf'
  have hsz : old.layout.kept.size = old.layout.members.size := by
    rw [hL.kept, hL.members]
    exact hL.sizes
  rw [shapeOf_at hsz hw, shapeOf_at hsz hw', hL.members]
  rw [hL.members] at hw hw'
  subst hfirst
  obtain ⟨a, ha, -⟩ := (OnBytes.Means.layBlocks_right _).1 w f hf
  obtain ⟨a', ha', -⟩ := (OnBytes.Means.layBlocks_right _).1 w' f' hf'
  have h1 := rows_le_of_bits G part hw ha
  have h2 := rows_le_of_bits G part hw' ha'
  rcases (OnBytes.Means.layBlocks_right _).2.1 w w' f f' a a' hne hf hf' ha ha' with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end AtFullSide.K2

#print axioms AtFullSide.K2.gammaRead
#print axioms AtFullSide.K2.members_length
#print axioms AtFullSide.K2.keptNos_true
#print axioms AtFullSide.K2.keptShapes_true
#print axioms AtFullSide.K2.keptRows_true
#print axioms AtFullSide.K2.keptFirst_true
#print axioms AtFullSide.K2.apart_true
