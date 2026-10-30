-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Carry/OfRows.lean: THE CLAIM AT WHAT A FOLD OF ROWS IN FULL LEAVES IS THE
CLAIM AT WHAT IT LEAVES OF THE WORDS (`leftAt`, Johnson/Desc/K2/Honest/Carry/Left.lean), WHERE THE
ROWS' WORDS ARE THESE WORDS: AT THE CARRIED ROWS' OWN LAYOUT. For whoever spends the exact carry at
what an honest prover's closing returns: such a closing folds rows in full (with tails, over the
base field or the extension field); the exact carry speaks of a witness's words. None of its Lean
terms is a state, a way in, a front or a witness (the letter w stands for words that a caller
hands); but one of its imports (the library's Johnson/Top/H0/K2Hears/KeptNos.lean) stands over files
on the switch's fronts. One definition, three short names; statements with their proofs.

  `tableRow_lt` a row that `tableRow` finds lies within its member's rows
  `shapeOf` with `keptOf`, `keptNo`: short names for `foldEndAt`'s own inner terms: a member's
                    shape; its flag; the number of the kept member number a
  `foldEndAt_rows` the folded main row and the two folded mask rows are the same at two lists of
                    members and rows in full that have the same numbers of rows and agree BELOW EACH
                    MEMBER's REAL ROWS; of the fresh masks the rows below 2 ^ h alone are asked
  `foldEndAt_kept` the kept members' tables likewise
  `foldEndAt_lay` WHAT A FOLD LEAVES READS OF THE LAYOUT the two numbers of row variables and the
                    two lists of first rows alone
  `membersTrue` the closed group's members, as the carried rows' layout names them, AT THEIR TRUE
                    SHAPES (`membersAt` reads every one in the extension field)
  `member_at` with `pair_at`, `shapeOf_true`, `shapeOf_at`: small laws on the layout's list of
                    members with their flags: an entry's member and place; the entry at a place,
                    where the two lists are of one length; a member's shape in `membersTrue` and in
                    `membersAt`
  `sizesKept_true` the sizes' kept shapes (`sizesAt`: by `switchKept`) are the kept members', in the
                    same order: by the library's `switchKept_list`; where the layout's list of flags
                    is as long as its list of members
  `claimTrue_of_rows` THE JOIN: the layout's two lists are of one length · row by row and place by
                    place: each member's main and mask entries, AT ITS REAL ROWS, are w's at the
                    table's index (row + place * 2 ^ the rows' bits), for the members at the places
                    below the layout's members' number · the fresh mask's entries AT THE ROWS BELOW
                    2 ^ h are w's likewise ⊢ `ClaimTrue` at `leftAt S old w` ↔ `ClaimTrue` at
                    `foldEndAt old.layout … (membersTrue S old) M fresh ‹the carried rows'
                    challenges›`

By: `foldEndAt` (Johnson/Desc/K2/Honest/FoldEnd.lean) · `claimTrue_congr`, `leftAt`, `membersAt`,
`rowsOfWords` (Carry/Left.lean) · the library's `rowNo_lt` (OnBytes/Slice/Cells.lean),
`switchKept_list`, `keptNos` (Johnson/Top/H0/K2Hears/KeptNos.lean, KeptAtIndex.lean). NEAR, NOT
CALLED: `word_main`, `word_mask` (Johnson/Prover/Send/Held.lean): they lead from rows' words by
index to the entries by row and place that the join asks.

Limits. THE JOIN's PREMISES ARE PREMISES: one public, on the layout's two lists (the program's test
on a fold's shape asks it: `foldShapeOk`, OnBytes/Iop/Fold.lean); three on the rows' entries: shown
of no run. These three range over every place j, also from a code's message length on: there they
ask of words what no reading of a message fixes; at rows and words that are 0 there they hold. OF
`leftAt` ITSELF: `rowsOfWords` HAS NO GUARD AT ROWS BEYOND A MESSAGE's REAL ONES; the members are
read at real rows alone (`tableRow_lt`); THE FRESH MASK IS READ AT EVERY ROW BELOW 2 ^ h: SO THAT
`leftAt` IS THE FOLD OF THE WORDS' ROWS IS SAFE WHERE THE FRESH MASK HAS AT LEAST 2 ^ h MASK ROWS
(enough; not shown needed); with fewer, from 2 ^ the rows' bits on, a row's index runs into the next
place: the program's test on a fold's fresh mask asks just 2 ^ h (`foldMaskOk`,
OnBytes/Iop/Fold.lean), and no fold begins without it; at the written lists of the full size the
library has that a layout's h is 0 (`layout_full`,
Johnson/Desc/First/Close/Law/LayoutOfShapes.lean). IT SPEAKS OF `foldEndAt` AT THE CARRIED ROWS' OWN
LAYOUT, NOT OF `foldEnd`: that the layout which `foldEnd` makes anew of the members' shapes has the
carried rows' layout's four read fields is not shown here (`foldEndAt_lay` is the tool for it).
Nothing ties `membersTrue`, the rows or the challenges to what a plan, a closing or a run holds.
Nothing on tails, pads or symbols. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Carry.Left
import OnBytes.Slice.Cells
import Johnson.Top.H0.K2Hears.KeptNos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE formAt)
open OnBytes.Means (Words)
open Johnson.Prover.Send (Rows)

/-- A row that the table finds lies within its member's rows. -/
theorem tableRow_lt (first : Array (Option Nat)) (rows : Nat → Nat) (ρ w b : Nat)
    (h : tableRow first rows ρ = some (w, b)) : b < rows w := by
  unfold tableRow at h
  obtain ⟨a, -, ha⟩ := List.exists_of_findSome?_eq_some h
  cases hf : first.getD a none with
  | none => rw [hf] at ha; cases ha
  | some f =>
    rw [hf] at ha
    simp only [Option.bind_some] at ha
    split at ha
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ha)
      omega
    · cases ha

/-- The shape of member number w of a list. -/
abbrev shapeOf (ms : List GroupMember) (w : Nat) : OracleShape := ((ms[w]?).map (·.shape)).getD {}

/-- **The folded main row and the two folded mask rows are the same** at two lists of members and
rows in full that have the same numbers of rows and agree below each member's real rows; the fresh
masks agree at the rows below 2 ^ h. -/
theorem foldEndAt_rows (L : GroupLayout) (codes : Codes) (code maskCode : Nat)
    (ms ms' : List GroupMember) (M M' : Nat → Rows) (fresh fresh' : Rows) (γ : List Cb.Gl.E)
    (hr : ∀ w, (shapeOf ms' w).mainRows = (shapeOf ms w).mainRows)
    (hz : ∀ w, (shapeOf ms' w).maskRows = (shapeOf ms w).maskRows)
    (hm : ∀ w b j, b < (shapeOf ms w).mainRows →
      (M' w).main ((shapeOf ms' w).mainDeg == 3) b j = (M w).main ((shapeOf ms w).mainDeg == 3) b j)
    (hk : ∀ w b j, b < (shapeOf ms w).maskRows → (M' w).mask b j = (M w).mask b j)
    (hf : ∀ b j, b < 2 ^ L.h → fresh'.mask b j = fresh.mask b j) :
    (foldEndAt L codes code maskCode ms' M' fresh' γ).main =
        (foldEndAt L codes code maskCode ms M fresh γ).main ∧
      (foldEndAt L codes code maskCode ms' M' fresh' γ).mask =
        (foldEndAt L codes code maskCode ms M fresh γ).mask := by
  have hr' : (fun w => (shapeOf ms' w).mainRows) = fun w => (shapeOf ms w).mainRows := funext hr
  have hz' : (fun w => (shapeOf ms' w).maskRows) = fun w => (shapeOf ms w).maskRows := funext hz
  have c1 : ∀ ρ j : Nat,
      (match tableRow L.mainFirst (fun w => (shapeOf ms' w).mainRows) ρ with
        | some (w, b) => (M' w).main ((shapeOf ms' w).mainDeg == 3) b j
        | none => zeroG) =
      match tableRow L.mainFirst (fun w => (shapeOf ms w).mainRows) ρ with
        | some (w, b) => (M w).main ((shapeOf ms w).mainDeg == 3) b j
        | none => zeroG := by
    intro ρ j
    rw [hr']
    cases h : tableRow L.mainFirst (fun w => (shapeOf ms w).mainRows) ρ with
    | none => rfl
    | some p => exact hm p.1 p.2 j (tableRow_lt _ _ _ _ _ h)
  have c2 : ∀ ρ j : Nat,
      (match tableRow L.maskFirst (fun w => (shapeOf ms' w).maskRows) ρ with
        | some (w, b) => (M' w).mask b j
        | none => zeroG) =
      match tableRow L.maskFirst (fun w => (shapeOf ms w).maskRows) ρ with
        | some (w, b) => (M w).mask b j
        | none => zeroG := by
    intro ρ j
    rw [hz']
    cases h : tableRow L.maskFirst (fun w => (shapeOf ms w).maskRows) ρ with
    | none => rfl
    | some p => exact hk p.1 p.2 j (tableRow_lt _ _ _ _ _ h)
  unfold foldEndAt
  dsimp only
  refine ⟨funext fun j => ?_, funext fun r => funext fun i => ?_⟩
  · split
    · exact congrFun (congrFun (congrArg₂ (Johnson.Prover.Link.foldMsg _)
        (funext fun x => by
          rcases x with x | x
          · exact c1 _ _
          · exact c2 _ _) (funext fun x => hf _ _ (OnBytes.Slice.rowNo_lt x.1))) _) _
    · rfl
  · split
    · split
      · exact congrFun (congrFun (congrArg₂ (Johnson.Prover.Link.foldMsg _)
          (funext fun x => by
            rcases x with x | x
            · exact c1 _ _
            · exact c2 _ _) (funext fun x => hf _ _ (OnBytes.Slice.rowNo_lt x.1))) _) _
      · exact congrFun (congrFun (congrArg₂ (Johnson.Prover.Link.foldMsg _)
          (funext fun x => by
            rcases x with x | x
            · exact c1 _ _
            · exact c2 _ _) (funext fun x => hf _ _ (OnBytes.Slice.rowNo_lt x.1))) _) _
    · rfl

/-- Whether member number w of a list is kept. -/
abbrev keptOf (ms : List GroupMember) (w : Nat) : Bool := ((ms[w]?).map (·.kept)).getD false

/-- The number, in the list, of the kept member number a; the list's length beyond the last. -/
abbrev keptNo (ms : List GroupMember) (a : Nat) : Nat :=
  ((List.range ms.length).filter fun w => keptOf ms w).getD a ms.length

/-- The kept members' tables are the same there, read at a shape with no more main rows. -/
theorem foldEndAt_kept (L : GroupLayout) (codes : Codes) (code maskCode : Nat)
    (ms ms' : List GroupMember) (M M' : Nat → Rows) (fresh fresh' : Rows) (γ : List Cb.Gl.E)
    (hl : ms'.length = ms.length)
    (hq : ∀ w, keptOf ms' w = keptOf ms w)
    (hm : ∀ w b j, b < (shapeOf ms w).mainRows →
      (M' w).main ((shapeOf ms' w).mainDeg == 3) b j = (M w).main ((shapeOf ms w).mainDeg == 3) b j)
    (a : Nat) (s : OracleShape) (hs : s.mainRows ≤ (shapeOf ms (keptNo ms a)).mainRows) (i : Nat) :
    ((foldEndAt L codes code maskCode ms' M' fresh' γ).kept a).entryIn s i =
      ((foldEndAt L codes code maskCode ms M fresh γ).kept a).entryIn s i := by
  have hn : keptNo ms' a = keptNo ms a := by
    unfold keptNo
    rw [hl, show (fun w => keptOf ms' w) = fun w => keptOf ms w from funext hq]
  unfold Held.entryIn
  split
  · rename_i hb
    unfold Held.entry
    show (M' (keptNo ms' a)).main ((shapeOf ms' (keptNo ms' a)).mainDeg == 3) _ _ =
      (M (keptNo ms a)).main ((shapeOf ms (keptNo ms a)).mainDeg == 3) _ _
    rw [hn]
    exact hm _ _ _ (Nat.lt_of_lt_of_le hb hs)
  · rfl

/-- **What a fold leaves reads of the layout** the two numbers of row variables and the two lists of
first rows alone. -/
theorem foldEndAt_lay (L L' : GroupLayout) (hk : L'.k = L.k) (hh : L'.h = L.h)
    (h1 : L'.mainFirst = L.mainFirst) (h2 : L'.maskFirst = L.maskFirst) (codes : Codes)
    (code maskCode : Nat) (ms : List GroupMember) (M : Nat → Rows) (fresh : Rows)
    (γ : List Cb.Gl.E) :
    foldEndAt L' codes code maskCode ms M fresh γ =
      foldEndAt L codes code maskCode ms M fresh γ := by
  obtain ⟨k, h, e, z, mem, kp, mf, zf⟩ := L
  obtain ⟨k', h', e', z', mem', kp', mf', zf'⟩ := L'
  obtain rfl : k' = k := hk
  obtain rfl : h' = h := hh
  obtain rfl : mf' = mf := h1
  obtain rfl : zf' = zf := h2
  rfl

/-- The closed group's members, as the carried rows' layout names them: AT THEIR TRUE SHAPES. -/
def membersTrue (S : Statement) (old : SingleRows) : List GroupMember :=
  (old.layout.members.zip old.layout.kept).toList.map fun p =>
    ⟨(S.oracles.getD p.1 default).shape, p.2⟩

/-- An entry of the layout's list of members with their flags: its member, and that its place is
one of the layout's. -/
theorem member_at (old : SingleRows) (i : Nat) (p : Nat × Bool)
    (h : (old.layout.members.zip old.layout.kept).toList[i]? = some p) :
    old.layout.members.getD i noId = p.1 ∧ i < old.layout.members.size := by
  rw [Array.toList_zip, List.getElem?_zip_eq_some] at h
  refine ⟨?_, ?_⟩
  · rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h.1]
    rfl
  · have := (List.getElem?_eq_some_iff.1 h.1).1
    simpa using this

/-- A member's shape in `membersTrue`. -/
theorem shapeOf_true (S : Statement) (old : SingleRows) (i : Nat) :
    shapeOf (membersTrue S old) i =
      (((old.layout.members.zip old.layout.kept).toList[i]?).map fun p =>
        (S.oracles.getD p.1 default).shape).getD {} := by
  unfold shapeOf membersTrue
  rw [List.getElem?_map, Option.map_map]
  rfl

/-- A member's shape in `membersAt`. -/
theorem shapeOf_at (S : Statement) (old : SingleRows) (i : Nat) :
    shapeOf (membersAt S old) i =
      (((old.layout.members.zip old.layout.kept).toList[i]?).map fun p =>
        { (S.oracles.getD p.1 default).shape with mainDeg := 3 }).getD {} := by
  unfold shapeOf membersAt
  rw [List.getElem?_map, Option.map_map]
  rfl

/-- An entry of the layout's list of members with their flags, where the two lists are of one
length. -/
theorem pair_at (old : SingleRows) (hsz : old.layout.kept.size = old.layout.members.size) (w : Nat)
    (hw : w < old.layout.members.size) :
    (old.layout.members.zip old.layout.kept).toList[w]? =
      some (old.layout.members[w], old.layout.kept[w]'(hsz ▸ hw)) := by
  rw [Array.toList_zip, List.getElem?_zip_eq_some]
  exact ⟨by simp [hw], by simp [hsz ▸ hw]⟩

/-- The sizes' kept shapes are the kept members', in the same order: where the layout's two lists
are of one length. -/
theorem sizesKept_true (S : Statement) (old : SingleRows) (T : SwitchTarget) (a : Nat)
    (hsz : old.layout.kept.size = old.layout.members.size) :
    (sizesAt S old T).kept.getD a {} =
      shapeOf (membersTrue S old) (keptNo (membersTrue S old) a) := by
  have hn : (membersTrue S old).length = old.layout.members.size := by
    unfold membersTrue
    rw [List.length_map, Array.length_toList, Array.size_zip, hsz, Nat.min_self]
  have hz : (old.layout.members.zip old.layout.kept).toList.length = old.layout.members.size := by
    rw [Array.length_toList, Array.size_zip, hsz, Nat.min_self]
  have hq : (fun w => keptOf (membersTrue S old) w) = fun w => old.layout.kept.getD w false := by
    funext w
    unfold keptOf membersTrue
    rw [List.getElem?_map, Option.map_map, Array.getD_eq_getD_getElem?]
    by_cases hw : w < old.layout.members.size
    · rw [pair_at old hsz w hw, Array.getElem?_eq_getElem (hsz ▸ hw)]
      rfl
    · rw [List.getElem?_eq_none (by rw [hz]; exact Nat.le_of_not_lt hw),
        Array.getElem?_eq_none (by rw [hsz]; exact Nat.le_of_not_lt hw)]
      rfl
  show ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape).getD a {} = _
  rw [Own.switchKept_list, List.map_map, shapeOf_true]
  unfold keptNo
  rw [hq, hn]
  show _ = (((old.layout.members.zip old.layout.kept).toList[(Own.keptNos old.layout).getD a
    old.layout.members.size]?).map fun p => (S.oracles.getD p.1 default).shape).getD {}
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hw : (Own.keptNos old.layout)[a]? with
  | none =>
    rw [Option.getD_none, List.getElem?_eq_none (by rw [hz])]
    rfl
  | some w =>
    have hlt : w < old.layout.members.size :=
      List.mem_range.1 (List.mem_filter.1 (List.mem_of_getElem? hw)).1
    rw [Option.getD_some, pair_at old hsz w hlt]
    have e : old.layout.members.getD w 0 = old.layout.members[w] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
      rfl
    show (S.oracles.getD (old.layout.members.getD w 0) default).shape = _
    rw [e]
    rfl

/-- **THE CLAIM AT WHAT A FOLD OF ROWS IN FULL LEAVES IS THE CLAIM AT WHAT IT LEAVES OF THE WORDS**,
where the rows' entries are these words': at the carried rows' own layout. M: each member in full,
by its place in the layout. fresh: the fresh mask in full. -/
theorem claimTrue_of_rows (S : Statement) (old : SingleRows) (T : SwitchTarget) (w : Words GE)
    (M : Nat → Rows) (fresh : Rows)
    (hsz : old.layout.kept.size = old.layout.members.size)
    (hM : ∀ i b j, i < old.layout.members.size →
      b < (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows →
      (M i).main
          ((S.oracles.getD (old.layout.members.getD i noId) default).shape.mainDeg == 3) b j =
        w (old.layout.members.getD i noId) .main (b + j * 2 ^ ceilLog2
          (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows))
    (hZ : ∀ i b j, i < old.layout.members.size →
      b < (S.oracles.getD (old.layout.members.getD i noId) default).shape.maskRows →
      (M i).mask b j = w (old.layout.members.getD i noId) .mask (b + j * 2 ^ ceilLog2
        (S.oracles.getD (old.layout.members.getD i noId) default).shape.maskRows))
    (hF : ∀ b j, b < 2 ^ old.layout.h → fresh.mask b j = w old.fresh .mask
      (b + j * 2 ^ ceilLog2 (S.oracles.getD old.fresh default).shape.maskRows)) :
    ClaimTrue (sizesAt S old T) old (leftAt S old w) ↔
      ClaimTrue (sizesAt S old T) old (foldEndAt old.layout S.codes old.code old.maskCode
        (membersTrue S old) M fresh (old.gamma.map readE)) := by
  have hr : ∀ i, (shapeOf (membersAt S old) i).mainRows =
      (shapeOf (membersTrue S old) i).mainRows := fun i => by
    rw [shapeOf_at, shapeOf_true]
    cases (old.layout.members.zip old.layout.kept).toList[i]? <;> rfl
  have hz : ∀ i, (shapeOf (membersAt S old) i).maskRows =
      (shapeOf (membersTrue S old) i).maskRows := fun i => by
    rw [shapeOf_at, shapeOf_true]
    cases (old.layout.members.zip old.layout.kept).toList[i]? <;> rfl
  have hm : ∀ i b j, b < (shapeOf (membersTrue S old) i).mainRows →
      (rowsOfWords w (old.layout.members.getD i noId)
        (S.oracles.getD (old.layout.members.getD i noId) default).shape).main
          ((shapeOf (membersAt S old) i).mainDeg == 3) b j =
        (M i).main ((shapeOf (membersTrue S old) i).mainDeg == 3) b j := fun i b j hb => by
    rw [shapeOf_true] at hb ⊢
    rw [shapeOf_at]
    cases hp : (old.layout.members.zip old.layout.kept).toList[i]? with
    | none =>
      rw [hp] at hb
      exact absurd hb (Nat.not_lt_zero _)
    | some p =>
      rw [hp] at hb
      have hb' : b < (S.oracles.getD p.1 default).shape.mainRows := hb
      obtain ⟨e, hi⟩ := member_at old i p hp
      have h1 := hM i b j hi (by rw [e]; exact hb')
      rw [e] at h1 ⊢
      exact h1.symm
  have hk : ∀ i b j, b < (shapeOf (membersTrue S old) i).maskRows →
      (rowsOfWords w (old.layout.members.getD i noId)
        (S.oracles.getD (old.layout.members.getD i noId) default).shape).mask b j =
        (M i).mask b j := fun i b j hb => by
    rw [shapeOf_true] at hb
    cases hp : (old.layout.members.zip old.layout.kept).toList[i]? with
    | none =>
      rw [hp] at hb
      exact absurd hb (Nat.not_lt_zero _)
    | some p =>
      rw [hp] at hb
      have hb' : b < (S.oracles.getD p.1 default).shape.maskRows := hb
      obtain ⟨e, hi⟩ := member_at old i p hp
      have h1 := hZ i b j hi (by rw [e]; exact hb')
      rw [e] at h1 ⊢
      exact h1.symm
  have hf : ∀ b j, b < 2 ^ old.layout.h →
      (rowsOfWords w old.fresh (S.oracles.getD old.fresh default).shape).mask b j =
        fresh.mask b j := fun b j hb => (hF b j hb).symm
  have hl : (membersAt S old).length = (membersTrue S old).length := by
    unfold membersAt membersTrue
    rw [List.length_map, List.length_map]
  have hq : ∀ i, keptOf (membersAt S old) i = keptOf (membersTrue S old) i := fun i => by
    unfold keptOf membersAt membersTrue
    rw [List.getElem?_map, List.getElem?_map, Option.map_map, Option.map_map]
    rfl
  have R := foldEndAt_rows old.layout S.codes old.code old.maskCode (membersTrue S old)
    (membersAt S old) M _ fresh _ (old.gamma.map readE) hr hz hm hk hf
  unfold leftAt
  exact claimTrue_congr _ old _ _ (fun j _ => congrFun R.1 j)
    (fun a i => foldEndAt_kept old.layout S.codes old.code old.maskCode (membersTrue S old)
      (membersAt S old) M _ fresh _ (old.gamma.map readE) hl hq hm a _
      (Nat.le_of_eq (congrArg OracleShape.mainRows (sizesKept_true S old T a hsz))) i)
    (fun r i _ _ => congrFun (congrFun R.2 r) i)

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.tableRow_lt
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt_rows
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt_kept
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt_lay
#print axioms VerifiableInference.Desc.K2.Honest.member_at
#print axioms VerifiableInference.Desc.K2.Honest.shapeOf_true
#print axioms VerifiableInference.Desc.K2.Honest.shapeOf_at
#print axioms VerifiableInference.Desc.K2.Honest.pair_at
#print axioms VerifiableInference.Desc.K2.Honest.sizesKept_true
#print axioms VerifiableInference.Desc.K2.Honest.claimTrue_of_rows
#print axioms VerifiableInference.Desc.K2.Honest.shapeOf
#print axioms VerifiableInference.Desc.K2.Honest.keptOf
#print axioms VerifiableInference.Desc.K2.Honest.keptNo
#print axioms VerifiableInference.Desc.K2.Honest.membersTrue
