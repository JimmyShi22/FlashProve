-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/KeptAtFront.lean: the code switch: OF THE CARRIED ROWS' SYMBOLS AT A
POSITION, THE KEPT ROWS' ARE THE KEPT MEMBERS' OWN MAIN SYMBOLS, member after member, row after row:
nothing is folded into them.

Johnson/Desc/Own/Symbols.lean's rowsAt lays the members' columns at a position and returns: the
folded main symbol · the kept rows · the folded old mask · the folded fresh mask.
  layMembers_kept   the kept rows behind the laying are those in front, and then, for each member of
                    the list that the layout marks as kept, in order, that member's column's main
                    symbols
  rowsAt_list       what rowsAt returns, as a list: one symbol, the kept rows, two symbols
  rowsAt_kept       so the kept rows in what rowsAt returns are the kept members' own main symbols
WHAT IT IS FOR. The typed open word in front of a switch is made of what rowsAt returns
(K2Hands/StrMade.lean). Its kept slots are then the kept members' own words. That is the first of
three steps from «each held slot of the open word decodes» to «the kept member's own committed word
decodes».
LIMITS. On lists of symbols alone: no typed word, no decoder here. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.LongLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- A member's column at position number i; the empty column where there is none. -/
def colAtW (opened : Array (Array Column)) (i w : Nat) : Column :=
  ((opened[w]?).bind (fun (c : Array Column) => c[i]?)).getD default

theorem layMembers_kept (L : GroupLayout) (opened : Array (Array Column)) (i : Nat) :
    ∀ (ws : List Nat) (t t' : Tables), layMembers L opened i ws t = some t' →
      t'.kept.toList = t.kept.toList ++
        (ws.filter fun w => L.kept.getD w false).flatMap fun w => (colAtW opened i w).main.toList
  | [], t, t', h => by
    cases h
    simp
  | w :: ws, t, t', h => by
    unfold layMembers at h
    obtain ⟨col, hc, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have ih := layMembers_kept L opened i ws t1 t' h2
    have hcol : colAtW opened i w = col := by
      unfold colAtW
      rw [hc]
      rfl
    unfold layMember at h1
    obtain ⟨mask, -, h1⟩ := Option.bind_eq_some_iff.1 h1
    by_cases hk : L.kept.getD w false = true
    · rw [if_pos hk] at h1
      cases h1
      have e : (w :: ws).filter (fun w => L.kept.getD w false) =
          w :: ws.filter (fun w => L.kept.getD w false) :=
        List.filter_cons_of_pos (p := fun w => L.kept.getD w false) hk
      rw [ih, e, List.flatMap_cons, hcol, Array.toList_append, List.append_assoc]
    · rw [if_neg hk] at h1
      obtain ⟨main, -, rfl⟩ := Option.map_eq_some_iff.1 h1
      have e : (w :: ws).filter (fun w => L.kept.getD w false) =
          ws.filter (fun w => L.kept.getD w false) :=
        List.filter_cons_of_neg (p := fun w => L.kept.getD w false) hk
      rw [ih, e]

/-- **What rowsAt returns, as a list.** -/
theorem rowsAt_list (s : SingleRows) (hm : s.masks = 2) (opened : Array (Array Column)) (i : Nat)
    (seg : Array E) (h : rowsAt s opened #[] i = some seg) :
    ∃ (t : Tables) (a b c : E),
      layMembers s.layout opened i (List.range s.layout.members.size)
        ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩ =
          some t ∧ seg.toList = a :: (t.kept.toList ++ [b, c]) := by
  unfold rowsAt at h
  dsimp only at h
  generalize layMembers s.layout opened i (List.range s.layout.members.size)
      ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩ = r at h
  generalize (opened[s.layout.members.size]?).bind (fun (c : Array Column) => c[i]?) = fr at h
  cases r with
  | none => cases h
  | some t =>
    by_cases h1 : t.kept.size = s.keptRows
    · cases fr with
      | none => simp [h1, hm] at h
      | some fresh =>
        by_cases h2 : fresh.mask.size = 2 ^ s.layout.h
        · simp [h1, h2, hm] at h
          subst h
          exact ⟨t, (foldLow t.main s.gamma).getD 0 zeroE,
            (foldLow t.mask (s.gamma.take s.layout.h)).getD 0 zeroE,
            (foldLow fresh.mask (s.gamma.take s.layout.h)).getD 0 zeroE, rfl, by simp⟩
        · simp [h1, h2, hm] at h
    · simp [h1] at h

/-- **The kept rows are the kept members' own main symbols.** -/
theorem rowsAt_kept (s : SingleRows) (hm : s.masks = 2) (opened : Array (Array Column)) (i : Nat)
    (seg : Array E) (h : rowsAt s opened #[] i = some seg) :
    ∃ a b c : E, seg.toList = a ::
      (((List.range s.layout.members.size).filter fun w => s.layout.kept.getD w false).flatMap
        (fun w => (colAtW opened i w).main.toList) ++ [b, c]) := by
  obtain ⟨t, a, b, c, h1, h2⟩ := rowsAt_list s hm opened i seg h
  refine ⟨a, b, c, ?_⟩
  rw [h2, layMembers_kept _ _ _ _ _ _ h1]
  simp

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.rowsAt_kept
