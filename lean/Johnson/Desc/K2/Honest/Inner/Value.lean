-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/Value.lean: WHAT A ROW IS WORTH ON THE HONEST NEW MESSAGES OF A CODE
SWITCH BETWEEN TWO SEGMENTS: the sum over all tables of the statement (`value`,
Johnson/Desc/Means/Says.lean) is the sum over the carrying message's main table and the copies' main
tables: the words (`newWords`, Inner/Statement.lean) are 0 everywhere else. Statements and proofs.

  `Lists.idxOf_none`    a number that is not in a list has no place in it
  `kept_bare`     a kept member has no mask row
  `word_off`      the words are 0 outside the main tables of the carrying message and the copies
  `value_split`   a row's worth: on the carrying message's main table, and on each copy's

Limits. Nothing on the rows' coefficients. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE coefAt)
open OnBytes.Means (value onTable tableSize)
open Johnson.Prover.Send (Rows)

/-- A number that is not in a list has no place in it. -/
theorem Lists.idxOf_none : ∀ (l : List Nat) (o : Nat), o ∉ l → l.idxOf? o = none
  | [], _, _ => rfl
  | x :: l, o, h => by
    rw [List.mem_cons, not_or] at h
    rw [List.idxOf?_cons, Lists.idxOf_none l o h.2]
    simp [Ne.symm h.1]

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- A kept member has no mask row. -/
theorem kept_bare (A : AtSwitch S old T g anew W V) (a : Nat) :
    ((sizesAt S old T).kept.getD a {}).maskRows = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (sizesAt S old T).kept[a]? with
  | none => rfl
  | some s =>
    have hs : ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape)[a]? =
        some s := h
    rw [List.getElem?_map] at hs
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hs
    have ha : a < (switchKept old).toList.length := (List.getElem?_eq_some_iff.1 ho).1
    have hk : a < T.kept.toList.length := by
      have := A.target.keptCount
      simp only [Array.length_toList] at ha ⊢
      omega
    have hz : (o, T.kept.toList[a]) ∈ (switchKept old).toList.zip T.kept.toList := by
      apply List.mem_of_getElem? (i := a)
      rw [List.getElem?_zip_eq_some]
      exact ⟨ho, List.getElem?_eq_getElem hk⟩
    have hm : (o, T.kept.toList[a]) ∈ (switchKept old).zip T.kept := by
      rw [← Array.mem_toList_iff, Array.toList_zip]
      exact hz
    exact (A.target.keptShapes _ hm).oldBare

/-- The words are 0 outside the main tables of the carrying message and the copies. -/
theorem word_off (A : AtSwitch S old T g anew W V) (o : Nat) (part : Part) (i : Nat)
    (h : part = .mask ∨ (o ≠ g ∧ o ∉ anew.toList)) :
    newWords (sizesAt S old T) g anew V o part i = 0 := by
  have fill := A.target.fill
  unfold _root_.Tw.K2.BlocksFill at fill
  rw [A.restMain] at fill
  unfold newWords
  by_cases hg : o = g
  · rw [if_pos hg]
    rcases h with rfl | h
    · show (if i % 2 ^ ceilLog2 T.shape.maskRows < T.shape.maskRows then _ else 0) = 0
      rw [fill.1, if_neg (Nat.not_lt_zero _)]
    · exact absurd hg h.1
  · rw [if_neg hg]
    cases e : anew.toList.idxOf? o with
    | none => rfl
    | some a =>
      rcases h with rfl | h
      · show (if i % 2 ^ ceilLog2 ((sizesAt S old T).kept.getD a {}).maskRows <
          ((sizesAt S old T).kept.getD a {}).maskRows then _ else 0) = 0
        rw [kept_bare A a, if_neg (Nat.not_lt_zero _)]
      · rw [Lists.idxOf_none _ _ h.2] at e
        cases e

/-- **A row's worth on the honest new messages.** hn: each copy's number names a message of the
statement. -/
theorem value_split (A : AtSwitch S old T g anew W V) (hn : ∀ o ∈ anew.toList, o < S.oracles.size)
    (r : OnBytes.Row) :
    value rdE S r (newWords (sizesAt S old T) g anew V) =
      onTable rdE S r (newWords (sizesAt S old T) g anew V) g .main +
        (anew.toList.map fun o =>
          onTable rdE S r (newWords (sizesAt S old T) g anew V) o .main).sum := by
  have hmask : ∀ o, onTable rdE S r (newWords (sizesAt S old T) g anew V) o .mask = 0 := by
    intro o
    unfold onTable
    apply Finset.sum_eq_zero
    intro i _
    rw [word_off A o .mask i (Or.inl rfl), mul_zero]
  have hoff : ∀ o, o ∉ g :: anew.toList →
      onTable rdE S r (newWords (sizesAt S old T) g anew V) o .main = 0 := by
    intro o ho
    rw [List.mem_cons, not_or] at ho
    unfold onTable
    apply Finset.sum_eq_zero
    intro i _
    rw [word_off A o .main i (Or.inr ho), mul_zero]
  have hap := A.seated.apart
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hap
  have hnd : (g :: anew.toList).Nodup :=
    List.nodup_cons.2 ⟨fun h => hap.1 (List.mem_append_left _ h), hap.2.1⟩
  have hg : g < S.oracles.size := by
    have h := A.seated.carrying
    obtain ⟨x, hx, _⟩ := Option.map_eq_some_iff.1 h
    exact (Array.getElem?_eq_some_iff.1 hx).1
  unfold value
  simp only [hmask, add_zero]
  have hsub : (g :: anew.toList).toFinset ⊆ Finset.range S.oracles.size := by
    intro o ho
    rw [List.mem_toFinset, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact Finset.mem_range.2 hg
    · exact Finset.mem_range.2 (hn o ho)
  rw [← Finset.sum_subset hsub (fun o _ ho => hoff o (fun h => ho (List.mem_toFinset.2 h))),
    List.sum_toFinset _ hnd, List.map_cons, List.sum_cons]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.value_split
