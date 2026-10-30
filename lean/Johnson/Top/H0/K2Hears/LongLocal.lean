-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/LongLocal.lean: the code switch: WHAT THE TEXT HEARS AT A DRAWN
POSITION HANGS ON THE COLUMNS AT THAT POSITION ALONE. First part: the carried rows' symbols,
position by position.

The text's rowsSymbols (Johnson/Desc/Own/Symbols.lean) lays the symbols of all drawn positions into
one array.
  layMembers_congr, rowsAt_congr  rowsAt at position number i reads of «opened» just each member's
                column number i
  rowsAt_acc    what rowsAt lays behind y is what it lays behind nothing, behind y
  rowsAt_size   it lays as many symbols as the carried rows have rows
  rowsFrom_at   the stretch of position number m in the array is what rowsAt lays at that position
                alone
  symbols_at    the same of rowsSymbols: entry k * rows + j is entry j of rowsAt … #[] k
rowsAt_acc, rowsAt_size, rowsFrom_at and symbols_at take the premise «the carried rows have two
masks» (hm : s.masks = 2). The six names are declared in the namespace VerifiableInference.Desc.Own,
beside the text of which they speak, though the file lies here. No soundness is claimed.

-/
import Johnson.Desc.Own.Symbols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem layMembers_congr (L : GroupLayout) (opened opened' : Array (Array Column)) (i i' : Nat)
    (h : ∀ w : Nat, (opened'[w]?).bind (fun (c : Array Column) => c[i']?) =
      (opened[w]?).bind (fun (c : Array Column) => c[i]?)) :
    ∀ (ws : List Nat) (t : Tables), layMembers L opened' i' ws t = layMembers L opened i ws t
  | [], _ => rfl
  | w :: ws, t => by
    unfold layMembers
    rw [h w]
    congr 1
    funext col
    congr 1
    funext t'
    exact layMembers_congr L opened opened' i i' h ws t'

/-- **rowsAt reads each member's column at its own position alone.** -/
theorem rowsAt_congr (s : SingleRows) (opened opened' : Array (Array Column)) (y : Array E)
    (i i' : Nat) (h : ∀ w : Nat, (opened'[w]?).bind (fun (c : Array Column) => c[i']?) =
      (opened[w]?).bind (fun (c : Array Column) => c[i]?)) :
    rowsAt s opened' y i' = rowsAt s opened y i := by
  unfold rowsAt
  simp only [layMembers_congr s.layout opened opened' i i' h, h]

theorem rowsAt_acc (s : SingleRows) (hm : s.masks = 2) (opened : Array (Array Column))
    (y : Array E) (i : Nat) : rowsAt s opened y i = (rowsAt s opened #[] i).map (y ++ ·) := by
  unfold rowsAt
  dsimp only
  generalize layMembers s.layout opened i (List.range s.layout.members.size)
      ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩ = r
  generalize (opened[s.layout.members.size]?).bind (fun (c : Array Column) => c[i]?) = fr
  cases r with
  | none => rfl
  | some t =>
    by_cases h1 : t.kept.size = s.keptRows
    · cases fr with
      | none => simp [h1, hm]
      | some fresh =>
        by_cases h2 : fresh.mask.size = 2 ^ s.layout.h
        · first
            | (simp [h1, h2, hm]; done)
            | (simp [h1, h2, hm]; apply Array.toList_inj.1; simp)
        · simp [h1, h2, hm]
    · simp [h1]

theorem rowsAt_size (s : SingleRows) (hm : s.masks = 2) (opened : Array (Array Column)) (i : Nat)
    (seg : Array E) (h : rowsAt s opened #[] i = some seg) : seg.size = s.rows := by
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
          simp [SingleRows.rows, hm, h1]
          omega
        · simp [h1, h2, hm] at h
    · simp [h1] at h

/-- **The stretch of a position in the array.** -/
theorem rowsFrom_at (s : SingleRows) (hm : s.masks = 2) (opened : Array (Array Column)) :
    ∀ (is : List Nat) (y Y : Array E), rowsFrom s opened is y = some Y →
      Y.size = y.size + is.length * s.rows ∧ (∀ j, j < y.size → Y[j]? = y[j]?) ∧
      ∀ m (hmm : m < is.length), ∃ seg, rowsAt s opened #[] is[m] = some seg ∧
        ∀ j, j < s.rows → Y[y.size + m * s.rows + j]? = seg[j]?
  | [], y, Y, h => by
    cases h
    exact ⟨by simp, fun _ _ => rfl, fun m hmm => absurd hmm (Nat.not_lt_zero _)⟩
  | i :: is, y, Y, h => by
    unfold rowsFrom at h
    obtain ⟨y1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rw [rowsAt_acc s hm] at h1
    obtain ⟨seg, hseg, rfl⟩ := Option.map_eq_some_iff.1 h1
    have hsz := rowsAt_size s hm opened i seg hseg
    obtain ⟨a, b, c⟩ := rowsFrom_at s hm opened is (y ++ seg) Y h2
    rw [Array.size_append, hsz] at a b c
    refine ⟨by rw [a, List.length_cons, Nat.succ_mul]; omega, fun j hj => ?_, fun m hmm => ?_⟩
    · rw [b j (by omega), Array.getElem?_append_left hj]
    · cases m with
      | zero =>
        refine ⟨seg, hseg, fun j hj => ?_⟩
        rw [Nat.zero_mul, Nat.add_zero, b _ (by omega),
          Array.getElem?_append_right (by omega)]
        congr 1
        omega
      | succ m =>
        obtain ⟨seg', hs', hc⟩ := c m (by simpa using hmm)
        refine ⟨seg', hs', fun j hj => ?_⟩
        rw [← hc j hj]
        congr 1
        rw [Nat.succ_mul]
        omega

/-- **Entry k * rows + j of the symbols is entry j of what is laid at position number k alone.** -/
theorem symbols_at (s : SingleRows) (hm : s.masks = 2) (opened : Array (Array Column)) (n : Nat)
    (Y : Array E) (h : rowsSymbols s opened n = some Y) (k : Nat) (hk : k < n) :
    ∃ seg, rowsAt s opened #[] k = some seg ∧ ∀ j, j < s.rows → Y[k * s.rows + j]? = seg[j]? := by
  unfold rowsSymbols at h
  split at h
  · obtain ⟨-, -, c⟩ := rowsFrom_at s hm opened _ #[] Y h
    obtain ⟨seg, hs, hc⟩ := c k (by simpa using hk)
    rw [List.getElem_range] at hs
    exact ⟨seg, hs, fun j hj => by simpa using hc j hj⟩
  · cases h

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.rowsAt_congr
#print axioms VerifiableInference.Desc.Own.symbols_at
