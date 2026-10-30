-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/KeptRows.lean: THE KEPT MEMBERS IN THE PROGRAM's FRAME OF A CODE
SWITCH, IN THE STATEMENT's TERMS: tools for the rows that read a kept member (Inner/KeptHold.lean,
SampleHold.lean, CarriedHold.lean). Statements and proofs.

  `Lists.getD_at`, `Lists.toList_range`   an entry of an array of numbers; the array as a list,
                    entry by entry
  `kept_at`         the entry of a kept member in the program's frame, in the statement's terms
  `worth_addKept`   a form carried over at an entry of the frame: the form on the member's entries
  `Lists.row_pick`        a sum over a table's indices that picks one row
  `rows_list`, `rows_count`   the frame's entries have the kept members' rows; the single rows count
                    them
  `keptRow_at`      the kept row number (rows in front + b) is row b of member a

By: `frame_fields`, `range_map_at`, `rowBits_main` (Johnson/Top/H/SwitchMapsCheck.lean);
`frame_inv` (Johnson/Top/H0/Tw/K2/RowsMadeAgree.lean); `flatMap_at`
(Johnson/Top/H0/K2Hands/RowsAt.lean); Inner/KeptWorth.lean, Inner/RestIsPartsProof.lean.

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.GenRows
import Johnson.Top.H0.K2Hands.FormOnReads
import Johnson.Top.H0.Tw.K2.RowsMadeAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE readE coefAt formAt stretchAt codeOf wM wT)
open OnBytes.Means (Says value)
open Johnson.Prover.Send (Rows)
open Johnson.Prover.Link (symG)
open Finset (range)

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- An entry of an array of numbers. -/
theorem Lists.getD_at (a : Array Nat) {i : Nat} (hi : i < a.size) : a.getD i noId = a[i] := by
  simp [hi]

/-- The entry of a kept member in the program's frame. -/
theorem kept_at {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr) (a : Nat)
    (k : KeptPlace) (hk : Fr.kept[a]? = some k) :
    ∃ s o, (sizesAt S old T).kept[a]? = some s ∧ anew.toList[a]? = some o ∧ k.anew = o ∧
      k.pad = padPlaces S.codes s ∧ k.oldPadAt = (switchParts S old).oldPadAt.getD a 0 ∧
      k.rows = s.mainRows ∧ k.rowBits = ceilLog2 s.mainRows ∧
      (switchKept old).toList[a]? = some k.old ∧ s = (S.oracles.getD k.old default).shape := by
  obtain ⟨_, _, _, _, _, _, _, f8⟩ := Johnson.Top.H.frame_fields S old T g anew Fr hFr
  obtain ⟨hi, e⟩ := Johnson.Top.H.range_map_at _ _ _ _ (f8 ▸ hk)
  obtain ⟨_, _, _, hsz, _⟩ := _root_.Tw.K2.frame_inv hFr
  have hsz' : anew.size = (switchKept old).size := by simpa using hsz
  have ko : (switchKept old).toList[a]? = some ((switchKept old).getD a noId) := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hi, Lists.getD_at _ hi]
  have ka : anew.toList[a]? = some (anew.getD a noId) := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by omega),
      Lists.getD_at _ (by omega)]
  subst e
  refine ⟨(S.oracles.getD ((switchKept old).getD a noId) default).shape, anew.getD a noId, ?_, ka,
    rfl, rfl, rfl, rfl, Johnson.Top.H.rowBits_main S _, ko, rfl⟩
  show ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape)[a]? = _
  rw [List.getElem?_map, ko]
  rfl

/-- A form carried over at an entry of the frame. -/
theorem worth_addKept (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (c : Form) :
    worthOf S (newWords (sizesAt S old T) g anew V) g anew (coefAt (Fr.addKept {} k c)) =
      ∑ J ∈ range (2 ^ (k.rowBits + (S.codes.base.getD old.code default).logEll)),
        formAt c J * (W.kept a).entryIn (S.oracles.getD k.old default).shape J := by
  have I := frameIs hFr
  obtain ⟨s, o, hs, ho, e1, e2, e3, _, e5, _, e7⟩ := kept_at hFr a k hk
  have h := worth_kept A a s o hs ho c
  unfold SwitchFrame.addKept
  rw [e2, e1, I.gIs, I.restPart, A.restMain, I.places, e3, e5, ← e7]
  exact h

/-- A sum over a table's indices that picks the row b. -/
theorem Lists.row_pick (rb le b : Nat) (hb : b < 2 ^ rb) (F e : Nat → GE) :
    ∑ J ∈ range (2 ^ (rb + le)), (if J % 2 ^ rb = b then F (J / 2 ^ rb) else 0) * e J =
      ∑ j ∈ range (2 ^ le), F j * e (b + 2 ^ rb * j) := by
  have hpos : 0 < 2 ^ rb := Nat.two_pow_pos _
  have hsub : (range (2 ^ le)).image (fun j => b + 2 ^ rb * j) ⊆ range (2 ^ (rb + le)) := by
    intro J hJ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hJ
    have hj' := Finset.mem_range.1 hj
    rw [Finset.mem_range, Nat.pow_add]
    calc b + 2 ^ rb * j < 2 ^ rb + 2 ^ rb * j := by omega
      _ = 2 ^ rb * (j + 1) := by ring
      _ ≤ 2 ^ rb * 2 ^ le := Nat.mul_le_mul_left _ hj'
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _
    have h1 : (b + 2 ^ rb * j) % 2 ^ rb = b := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    have h2 : (b + 2 ^ rb * j) / 2 ^ rb = j := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hb, Nat.zero_add]
    rw [if_pos h1, h2]
  · intro j _ j' _ h
    have h' : b + 2 ^ rb * j = b + 2 ^ rb * j' := h
    exact Nat.eq_of_mul_eq_mul_left hpos (by omega)
  · intro J hJ hn
    by_cases h : J % 2 ^ rb = b
    · exfalso
      apply hn
      refine Finset.mem_image.2 ⟨J / 2 ^ rb, ?_, ?_⟩
      · rw [Finset.mem_range]
        apply Nat.div_lt_of_lt_mul
        rw [← Nat.pow_add]
        exact Finset.mem_range.1 hJ
      · show b + 2 ^ rb * (J / 2 ^ rb) = J
        rw [← h]
        exact Nat.mod_add_div _ _
    · rw [if_neg h, zero_mul]

/-- An array of numbers as a list, entry by entry. -/
theorem Lists.toList_range (a : Array Nat) :
    a.toList = (List.range a.size).map fun i => a.getD i noId := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < a.size
  · rw [Array.getElem?_toList, Array.getElem?_eq_getElem hi, List.getElem?_map,
      List.getElem?_range hi]
    show some a[i] = some (a.getD i noId)
    rw [Lists.getD_at a hi]
  · rw [List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by simpa using hi)]

/-- The frame's entries have the kept members' rows. -/
theorem rows_list {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr) :
    Fr.kept.map (·.rows) = (sizesAt S old T).kept.map (·.mainRows) := by
  obtain ⟨_, _, _, _, _, _, _, f8⟩ := Johnson.Top.H.frame_fields S old T g anew Fr hFr
  show _ = ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape).map _
  rw [f8, Lists.toList_range, List.map_map, List.map_map, List.map_map]
  rfl

/-- The single rows count the frame's kept rows. -/
theorem rows_count (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) :
    old.keptRows = (Fr.kept.map (·.rows)).sum := by
  rw [rows_list hFr, A.fits.rows]
  show _ = (((switchKept old).toList.map fun o => (S.oracles.getD o default).shape).map _).sum
  rw [List.map_map]
  rfl

/-- The kept row number (rows in front + b) is row b of member a. -/
theorem keptRow_at {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr) (a : Nat)
    (k : KeptPlace) (hk : Fr.kept[a]? = some k) (b : Nat) (hb : b < k.rows) :
    ((sizesAt S old T).kept.zipIdx.flatMap fun s =>
      (List.range s.1.mainRows).map fun b => (s.2, b))[
        ((Fr.kept.take a).map (·.rows)).sum + b]? = some (a, b) := by
  obtain ⟨s, _, hs, _, _, _, _, e4, _⟩ := kept_at hFr a k hk
  have hbefore := Lists.before_zipIdx
    (fun s : OracleShape × Nat => (List.range s.1.mainRows).map fun b => (s.2, b))
    (fun s => s.mainRows) (fun x => by simp) (sizesAt S old T).kept 0 a
  rw [List.map_take, rows_list hFr, ← List.map_take, ← hbefore,
    VerifiableInference.Desc.First.K2Hands.flatMap_at _ _ a b (s, a) (Lists.zipIdx_at _ _ _ hs)
      (by simp; omega)]
  show ((List.range s.mainRows).map fun b => (a, b))[b]? = some (a, b)
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.worth_addKept
#print axioms VerifiableInference.Desc.K2.Honest.Lists.row_pick
#print axioms VerifiableInference.Desc.K2.Honest.keptRow_at
