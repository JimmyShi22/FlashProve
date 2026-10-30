-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/SymbolsAgree.lean: a yardstick beside, which no block imports: the two
readings of Johnson/Desc/Own/Symbols.lean say just what the hand-written program's say, at all
arguments.
  `symbolsAt_eq`: symbolsAt = Blk.symbolsOf (OnBytes/Iop/Ground.lean).
  `layRows_eq`: layRows = putRows (OnBytes/Iop/Fold.lean).
  `rowsSymbols_eq`: rowsSymbols = singleRowsSymbols (the same file).

-/
import Johnson.Desc.Own.Symbols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem symbolsAt_eq (S : Statement) (B : TreeBook) (pos : Positions) (cols : List Opened) (o : Nat)
    (p : Nat × Nat) : symbolsAt S B pos cols o p = Blk.symbolsOf S B pos cols o p := by
  unfold symbolsAt Blk.symbolsOf
  cases h1 : B.trees[p.1]? with
  | none => simp
  | some tree =>
    cases h2 : S.oracles[o]? with
    | none => simp
    | some x =>
      cases h3 : cols.find? (·.1 == p.1) with
      | none => simp
      | some mine =>
        simp only [Option.bind_eq_bind, Option.bind_some, Array.mapM_eq_mapM_toList,
          Array.toList_range]
        congr 1
        congr 1
        funext i
        unfold whereOpened
        by_cases hs : (tree.shape.logN == pos.logN) = true
        · rw [if_pos hs, if_pos hs]
          cases hc : mine.2.2[i]? <;> simp [hc]
        · rw [if_neg hs, if_neg hs]
          cases hw : mine.2.1.idxOf? (pos.all.getD i 0 % 2 ^ tree.shape.logN) with
          | none => rfl
          | some here => cases hc : mine.2.2[here]? <;> simp [hc]

theorem layFrom_eq : ∀ (l : List E) (table : Array E) (f : Nat),
    (List.range l.length).foldl
        (fun t b => t.setIfInBounds (f + b) (l.toArray.getD b zeroE)) table = layFrom table f l
  | [], _, _ => rfl
  | e :: es, table, f => by
      rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have := layFrom_eq es (table.setIfInBounds f e) (f + 1)
      simp only [layFrom]
      rw [← this]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem layRows_eq (table : Array E) (first : Option Nat) (col : Array E) :
    layRows table first col = putRows table first col := by
  obtain ⟨l⟩ := col
  cases l with
  | nil => simp [layRows, putRows]
  | cons e es =>
    cases first with
    | none => simp [layRows, putRows]
    | some f =>
      simp only [layRows, putRows]
      rw [← layFrom_eq]
      simp

/-- One member, as the hand-written text's loop lays it. -/
theorem layMembers_eq (L : GroupLayout) (opened : Array (Array Column)) (i : Nat) :
    ∀ (ws : List Nat) (t : Tables),
      ws.foldlM (fun (t : Array E × Array E × Array E) w => do
        let col ← (← opened[w]?)[i]?
        let mask ← putRows t.2.1 (L.maskFirst.getD w none) col.mask
        if L.kept.getD w false then pure (t.1, mask, t.2.2 ++ col.main)
        else pure (← putRows t.1 (L.mainFirst.getD w none) col.main, mask, t.2.2))
        (t.main, t.mask, t.kept) =
      (layMembers L opened i ws t).map fun t => (t.main, t.mask, t.kept)
  | [], _ => rfl
  | w :: ws, t => by
      rw [List.foldlM_cons]
      simp only [layMembers, layMember, layRows_eq]
      cases h1 : opened[w]? with
      | none => rfl
      | some c1 =>
        cases h2 : c1[i]? with
        | none => simp [h2]
        | some col =>
          cases h3 : putRows t.mask (L.maskFirst.getD w none) col.mask with
          | none =>
            simp only [Option.bind_eq_bind, Option.bind_some, h2, h3, Option.bind_none,
              Option.map_none]
          | some mask =>
            by_cases hk : L.kept.getD w false = true
            · simp only [Option.bind_eq_bind, Option.bind_some, h2, h3, hk, if_true,
                Option.pure_def]
              exact layMembers_eq L opened i ws ⟨t.main, mask, t.kept ++ col.main⟩
            · cases h4 : putRows t.main (L.mainFirst.getD w none) col.main with
              | none =>
                simp only [Option.bind_eq_bind, Option.bind_some, h2, h3, hk, h4, Option.bind_none,
                  Option.map_none, if_false, Bool.false_eq_true]
              | some main =>
                simp only [Option.bind_eq_bind, Option.bind_some, h2, h3, hk, h4, Option.pure_def,
                  Option.map_some, if_false, Bool.false_eq_true]
                exact layMembers_eq L opened i ws ⟨main, mask, t.kept⟩

/-- One position, as the hand-written text's loop lays it: that loop's body, under a name. -/
def olderStep (s : SingleRows) (opened : Array (Array Column)) (y : Array E) (i : Nat) :
    Option (Array E) := do
  let start : Array E × Array E × Array E :=
    (Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[])
  let t ← (List.range s.layout.members.size).foldlM
    (fun (t : Array E × Array E × Array E) w => do
      let col ← (← opened[w]?)[i]?
      let mask ← putRows t.2.1 (s.layout.maskFirst.getD w none) col.mask
      if s.layout.kept.getD w false then pure (t.1, mask, t.2.2 ++ col.main)
      else pure (← putRows t.1 (s.layout.mainFirst.getD w none) col.main, mask, t.2.2)) start
  if t.2.2.size != s.keptRows then none
  let y1 := (y.push ((foldLow t.1 s.gamma).getD 0 zeroE)) ++ t.2.2
  let low := s.gamma.take s.layout.h
  let y2 := if 1 ≤ s.masks then y1.push ((foldLow t.2.1 low).getD 0 zeroE) else y1
  if s.masks == 2 then
    let fresh ← (← opened[s.layout.members.size]?)[i]?
    if fresh.mask.size != 2 ^ s.layout.h then none
    pure (y2.push ((foldLow fresh.mask low).getD 0 zeroE))
  else pure y2

theorem olderStep_eq (s : SingleRows) (opened : Array (Array Column)) (y : Array E) (i : Nat) :
    olderStep s opened y i = rowsAt s opened y i := by
  unfold olderStep
  simp only [rowsAt]
  rw [layMembers_eq s.layout opened i (List.range s.layout.members.size)
    ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩]
  cases ht : layMembers s.layout opened i (List.range s.layout.members.size)
    ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩ with
  | none => rfl
  | some t =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    by_cases hk : (t.kept.size != s.keptRows) = true
    · simp only [hk, if_true, Option.bind_none]
    · simp only [hk, if_false, Bool.false_eq_true, Option.pure_def, Option.bind_some]
      by_cases hm : (s.masks == 2) = true
      · simp only [hm, if_true]
        cases h1 : opened[s.layout.members.size]? with
        | none => rfl
        | some c1 =>
          cases h2 : c1[i]? with
          | none => simp only [Option.bind_some, h2, Option.bind_none]
          | some fresh =>
            simp only [Option.bind_some, h2]
            by_cases hf : (fresh.mask.size != 2 ^ s.layout.h) = true
            · simp only [hf, if_true, Option.bind_none]
            · simp only [hf, if_false, Bool.false_eq_true]
      · simp only [hm, if_false, Bool.false_eq_true]

theorem rowsFrom_eq (s : SingleRows) (opened : Array (Array Column)) :
    ∀ (is : List Nat) (y : Array E), is.foldlM (olderStep s opened) y = rowsFrom s opened is y
  | [], _ => rfl
  | i :: is, y => by
      rw [List.foldlM_cons, olderStep_eq]
      simp only [rowsFrom]
      cases rowsAt s opened y i with
      | none => rfl
      | some r => exact rowsFrom_eq s opened is r

/-- The hand-written text, with its loop's body under its name. -/
theorem older_unfold (s : SingleRows) (opened : Array (Array Column)) (positions : Nat) :
    singleRowsSymbols s opened positions = (do
      if s.gamma.length != s.layout.k || s.layout.k < s.layout.h then none
      if s.layout.kept.size != s.layout.members.size ||
          s.layout.mainFirst.size != s.layout.members.size ||
          s.layout.maskFirst.size != s.layout.members.size then none
      (List.range positions).foldlM (olderStep s opened) #[]) := rfl

/-- **The carried rows' symbols: the two texts agree at all arguments.** -/
theorem rowsSymbols_eq (s : SingleRows) (opened : Array (Array Column)) (positions : Nat) :
    rowsSymbols s opened positions = singleRowsSymbols s opened positions := by
  rw [older_unfold, rowsFrom_eq]
  unfold rowsSymbols
  generalize rowsFrom s opened (List.range positions) #[] = r
  by_cases h1 : s.gamma.length = s.layout.k <;> by_cases h2 : s.layout.h ≤ s.layout.k <;>
    by_cases h3 : s.layout.kept.size = s.layout.members.size <;>
    by_cases h4 : s.layout.mainFirst.size = s.layout.members.size <;>
    by_cases h5 : s.layout.maskFirst.size = s.layout.members.size <;>
    simp [shapeFits, h1, h2, h3, h4, h5, Nat.not_lt.2, Nat.not_le.1]

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.symbolsAt_eq
#print axioms VerifiableInference.Desc.Own.layRows_eq
#print axioms VerifiableInference.Desc.Own.rowsSymbols_eq
