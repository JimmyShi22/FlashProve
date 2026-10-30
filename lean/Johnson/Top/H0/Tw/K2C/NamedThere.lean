-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/NamedThere.lean: WHERE THE STATE's BOOK FOLLOWS THE PLAN's LIST OF TENANTS AND
THE STATE HOLDS THE OOD SAMPLE AT A TENANT, A SAMPLED ORACLE MESSAGE STANDS AT THE FIXED NUMBER BY
WHICH THE NAMED READER OF OOD SAMPLES FINDS THAT TENANT's MEMBER. At a state; general: no scope, no
kind. NO SUB-PROTOCOL IMPORTS THIS FILE.
WHY. The named reader (smpNamed, Johnson/Desc/Sound/SmpNamed.lean) finds a member's message by a
fixed number: the first place of the member's tenant in the plan's list. The promise's clause «the
sample is held» (smpHeld, Johnson/Desc/SmpRows.lean) finds it through the state's book: the first
number whose place is that tenant. «The reader gives behind a code switch what it gives in front»
(smpNamed_left, Johnson/Top/H0/K2Ties/SmpLeft.lean) asks for a sampled message at the FIXED number.
  find_min · idx_first   two small facts on lists: what find? finds in a range is the least; the
                         least place of a member is idxOf's
  number_is              under placesAre (Johnson/Desc/Sound/SmpPlaces.lean): where
                         oracleNo answers o at (j, t): idxOf (j, t) in the list is o. NO «each once»
                         IS ASKED OF THE LIST: both numbers are the FIRST, and the two lists are one
                         below the book's size
  named_there            THE STATEMENT, at a tenant
  named_there_mem        the same at a member that sits there
LIMITS. placesAre at a reached state, and that the list at which it is had is the reader's own, are
others' or owed: not here. No soundness is claimed.
-/
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.Sound.SmpPlaces
import Johnson.Desc.Sound.MeaningSig
import Johnson.Top.H0.Tw.K2C.HeldAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Named
open VerifiableInference.Desc (placesAre smpHeld oracleNo)
open VerifiableInference.Desc.Sound (Mem SitsAt seatOf)

theorem find_min (p : Nat → Bool) : ∀ (n o : Nat), (List.range n).find? p = some o →
    ∀ k, k < o → p k = false
  | 0, o, h, _, _ => by simp at h
  | n + 1, o, h, k, hk => by
    rw [List.range_succ, List.find?_append] at h
    cases hf : (List.range n).find? p with
    | some o' =>
      rw [hf] at h
      have e : o' = o := by simpa using h
      subst e
      exact find_min p n o' hf k hk
    | none =>
      rw [hf] at h
      have h2 : [n].find? p = some o := by simpa using h
      have ho : o = n := by simpa using List.mem_of_find?_eq_some h2
      subst ho
      simpa using List.find?_eq_none.1 hf k (List.mem_range.2 hk)

theorem idx_first {α : Type} [BEq α] [LawfulBEq α] : ∀ (l : List α) (a : α) (o : Nat),
    l[o]? = some a → (∀ k, k < o → l[k]? ≠ some a) → l.idxOf a = o
  | [], _, _, h, _ => by simp at h
  | b :: l, a, 0, h, _ => by
    have e : b = a := by simpa using h
    subst e
    simp
  | b :: l, a, o + 1, h, hm => by
    have hne : b ≠ a := fun e => hm 0 (Nat.succ_pos o) (by simp [e])
    have h' : l[o]? = some a := by simpa using h
    have ih := idx_first l a o h' fun k hk => by
      have := hm (k + 1) (Nat.succ_lt_succ hk)
      simpa using this
    have hb : (b == a) = false := by simpa using hne
    rw [List.idxOf_cons, ih, hb]
    rfl

theorem number_is {seats : List (Nat × Nat)} {st : OnBytes.Statement} {bk : OnBytes.TreeBook}
    {j t o : Nat} (hP : placesAre seats st bk = true) (ho : oracleNo bk j t = some o) :
    seats.idxOf (j, t) = o := by
  unfold placesAre at hP
  simp only [Bool.and_eq_true] at hP
  have hall := hP.2
  unfold oracleNo at ho
  have hlt : o < bk.place.size := List.mem_range.1 (List.mem_of_find?_eq_some ho)
  have hpo : bk.place[o]? = some (j, t) := by simpa using List.find?_some ho
  have same : ∀ k, k < bk.place.size → seats[k]? = bk.place[k]? := fun k hk =>
    (beq_iff_eq.1 (List.all_eq_true.1 hall k (List.mem_range.2 hk))).symm
  refine idx_first seats (j, t) o ((same o hlt).trans hpo) fun k hk e => ?_
  have hmin := find_min _ _ _ ho k hk
  rw [← same k (Nat.lt_trans hk hlt), e] at hmin
  simp at hmin

/-- **A sampled message stands at the tenant's fixed number.** -/
theorem named_there {seats : List (Nat × Nat)} {st : OnBytes.Statement} {bk : OnBytes.TreeBook}
    {j t : Nat} (hP : placesAre seats st bk = true) (hH : smpHeld st bk j t = true) :
    ∃ Y, st.oracles[seats.idxOf (j, t)]? = some Y ∧ Y.sampled = true := by
  obtain ⟨o, x, _, ho, hx, hs, -⟩ := VerifiableInference.Desc.First.K2.smpHeld_inv hH
  rw [number_is hP ho]
  exact ⟨x, hx, hs⟩

/-- **The same at a member that sits there.** -/
theorem named_there_mem {seats : List (Nat × Nat)} {st : OnBytes.Statement}
    {bk : OnBytes.TreeBook} {j t : Nat} (hP : placesAre seats st bk = true)
    (hH : smpHeld st bk j t = true) (x : Mem) (hx : SitsAt x j t) :
    ∃ Y, st.oracles[VerifiableInference.Desc.Sound.numAt seats x]? = some Y ∧
      Y.sampled = true := by
  have e : VerifiableInference.Desc.Sound.numAt seats x = seats.idxOf (j, t) := by
    unfold VerifiableInference.Desc.Sound.numAt seatOf
    rw [show x.1.seat x.2 = (j, t) from hx]
  rw [e]
  exact named_there hP hH

end P1Named

#print axioms P1Named.number_is
#print axioms P1Named.named_there
#print axioms P1Named.named_there_mem
