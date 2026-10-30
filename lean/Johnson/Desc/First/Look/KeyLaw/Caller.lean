-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Caller.lean: WHAT A CALLER OF THE KIND "LOOKUP" AT A KEY FILE
ESTABLISHES: a ledger opened with just the face's slots is ready; and K3Key's table of homes, made
of what is left of the two messages' lists of mask entries and tested to have a home for every slot,
meets HomeIs.

Main names:
  ready_slots: ({} : Fork).slots f.slots is ready at the count 0.
  homesFrom_full: a table of homes of full length, made of any two lists, is the pattern's entries.
  homeIs_of_size: the caller's one test (the table has f.slots members) gives HomeIs at the count 0,
    at the two lists read as functions; homeArr_getD: and the function is the array.

Limits. Nothing on whether the lists' members are different mask entries. K3Key's maskSide reads the
table of homes at the slot's own number: these readings meet it at first = 0 alone, that is, where
each lookup opens a ledger of its own.

-/
import Johnson.Desc.First.Look.KeyLaw.Out
import Johnson.Desc.First.Look.KeyLaw.MaskSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork)

/-- **A ledger opened with just the face's slots is ready.** -/
theorem ready_slots (f : Face) : Ready f 0 (({} : Fork).slots f.slots) where
  next := rfl
  sized := PscRun.slots_sized _ _
  room := Nat.le_of_eq (Nat.zero_add _)
  free := fun j hj => by
    show (Array.replicate f.slots false).getD (0 + j) true = false
    rw [Nat.zero_add, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos hj]
    rfl

theorem homesFrom_le : ∀ (pat : List Bool) (o k : List Slot), (homesFrom pat o k).length ≤
    pat.length
  | [], _, _ => by cases ‹List Slot› <;> simp [homesFrom]
  | false :: bs, [], k => by simp [homesFrom]
  | false :: bs, s :: o, k => by
    show (homesFrom bs o k).length + 1 ≤ bs.length + 1
    exact Nat.succ_le_succ (homesFrom_le bs o k)
  | true :: bs, o, [] => by cases o <;> simp [homesFrom]
  | true :: bs, o, s :: k => by
    have : homesFrom (true :: bs) o (s :: k) = s :: homesFrom bs o k := by cases o <;> rfl
    rw [this]
    exact Nat.succ_le_succ (homesFrom_le bs o k)

/-- A table of homes of full length is the pattern's entries. -/
theorem homesFrom_full (L1 L2 : List Slot) : ∀ (pat : List Bool) (a b : ℕ),
    (homesFrom pat (L1.drop a) (L2.drop b)).length = pat.length →
    homesFrom pat (L1.drop a) (L2.drop b) =
      hs (fun n => L1.getD n default) (fun n => L2.getD n default) pat a b
  | [], a, b, _ => by cases (L1.drop a) <;> rfl
  | false :: bs, a, b, h => by
    cases hd : L1.drop a with
    | nil => rw [hd] at h; simp [homesFrom] at h
    | cons s o =>
      rw [hd] at h
      have ha : a < L1.length := by
        by_contra hc
        rw [List.drop_eq_nil_of_le (by omega)] at hd
        cases hd
      have e := List.drop_eq_getElem_cons ha
      rw [hd] at e
      obtain ⟨rfl, rfl⟩ := List.cons.inj e
      show L1[a] :: homesFrom bs (L1.drop (a + 1)) (L2.drop b) = L1.getD a default :: _
      rw [homesFrom_full L1 L2 bs (a + 1) b (by simpa [homesFrom] using h),
        List.getD_eq_getElem _ _ ha]
  | true :: bs, a, b, h => by
    cases hd : L2.drop b with
    | nil =>
      rw [hd] at h
      cases (L1.drop a) <;> simp [homesFrom] at h
    | cons s k =>
      rw [hd] at h
      have hb : b < L2.length := by
        by_contra hc
        rw [List.drop_eq_nil_of_le (by omega)] at hd
        cases hd
      have e := List.drop_eq_getElem_cons hb
      rw [hd] at e
      obtain ⟨rfl, rfl⟩ := List.cons.inj e
      have e2 : ∀ o : List Slot, homesFrom (true :: bs) o (L2[b] :: L2.drop (b + 1)) =
          L2[b] :: homesFrom bs o (L2.drop (b + 1)) := fun o => by cases o <;> rfl
      rw [e2] at h ⊢
      show _ = L2.getD b default :: _
      rw [homesFrom_full L1 L2 bs a (b + 1) (by simpa using h), List.getD_eq_getElem _ _ hb]

theorem homeArr_getD (homeA : Array Slot) : HomeArr homeA fun j => homeA.getD j default := by
  intro j s h
  show homeA.getD j default = s
  rw [Array.getD_eq_getD_getElem?, h]
  rfl

/-- **The caller's one test gives HomeIs.** -/
theorem homeIs_of_size (f : Face) (L1 L2 : List Slot) (h : (homes f L1 L2).size = f.slots) :
    HomeIs f 0 (fun n => L1.getD n default) (fun n => L2.getD n default)
      fun j => (homes f L1 L2).getD j default := by
  have hl : (homesFrom (fromKeys f) (L1.drop 0) (L2.drop 0)).length = (fromKeys f).length := by
    rw [List.drop_zero, List.drop_zero, fromKeys_length, ← h]
    simp [homes]
  have e1 := homesFrom_full L1 L2 (fromKeys f) 0 0 hl
  rw [List.drop_zero, List.drop_zero] at e1
  have e2 := homesFrom_hs (fun n => L1.getD n default) (fun n => L2.getD n default) (fromKeys f) 0 0
    f.slots (by rw [fromKeys_length]; omega) (by rw [fromKeys_length]; omega)
  rw [List.drop_zero, List.drop_zero] at e2
  intro j _
  rw [Nat.zero_add]
  unfold homes
  rw [e1, e2]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.ready_slots
#print axioms VerifiableInference.Desc.K3.KeyLaw.homeIs_of_size
