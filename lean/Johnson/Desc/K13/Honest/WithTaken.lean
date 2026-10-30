--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/WithTaken.lean: kind K13, the members' batching: A WITNESS WITH OTHER VALUES
AT THE MASK ENTRIES THAT THE BATCHING TAKES, and what stays as it was. Definitions; statements with
their proofs. No distribution and no scalar of the sumcheck stands in this file.

A witness of the kind's laws is a matrix and a value for every mask entry (`Wit`,
Johnson/Desc/K13/Law/Means.lean). Given a list of mask entries and a value for each number:
Main names:
  `maskWith mask fresh v`: the mask entries with the values v, by number, at the entries of the list
    fresh. `withTaken w fresh v`: the witness with these mask entries and the same matrix.
  `maskWith_off`: at an entry outside the list nothing turns. `maskWith_getD`, `maskAt_withTaken`:
    where the list's entries differ from each other, entry number j has the value v j.
  `maskWith_congr`: of v the values below the list's length are read, and no other.
  `maskWith_self`, `withTaken_own`: **at the entries' own values it is the witness itself.**
  `holds_withTaken`: **a row that names none of the listed entries keeps its truth.**
  `tabsOf_withTaken`: **the rows' tables read no mask entry.**

What is not claimed. That a list of entries that a verifier's ledger hands out has entries that
differ, or that no row on the pile names one: Johnson/Desc/K13/Honest/Fresh.lean. That "any values"
are values that a real oracle message can hold: a witness here has a value at every pair of numbers.
Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.MovesAtM3
import Johnson.Desc.K13.Law.Means

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K13.Law

/-! ## A witness with other values at the listed entries -/

section Family
variable {K : Type}

/-- The mask entries, with the value v j at the entry number j of the list. Where an entry stands
twice in the list its first number counts. -/
def maskWith (mask : Slot → K) : List Slot → (ℕ → K) → Slot → K
  | [], _, s => mask s
  | a :: l, v, s => if s = a then v 0 else maskWith mask l (fun j => v (j + 1)) s

/-- At an entry outside the list nothing turns. -/
theorem maskWith_off (mask : Slot → K) : ∀ (fresh : List Slot) (v : ℕ → K) (s : Slot),
    s ∉ fresh → maskWith mask fresh v s = mask s
  | [], _, _, _ => rfl
  | a :: l, v, s, h => by
    have hne : s ≠ a := fun e => h (by rw [e]; exact List.mem_cons_self)
    show (if s = a then v 0 else maskWith mask l (fun j => v (j + 1)) s) = mask s
    rw [if_neg hne, maskWith_off mask l _ s fun hs => h (List.mem_cons_of_mem _ hs)]

/-- A list's member by its number is in the list. -/
theorem getD_mem {α : Type} (d : α) : ∀ (l : List α) (j : ℕ), j < l.length → l.getD j d ∈ l
  | [], _, h => by simp only [List.length_nil] at h; omega
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: l, j + 1, h =>
    List.mem_cons_of_mem _ (getD_mem d l j (by simp only [List.length_cons] at h; omega))

/-- Where the list's entries differ from each other, entry number j has the value v j. -/
theorem maskWith_getD (mask : Slot → K) : ∀ (fresh : List Slot) (v : ℕ → K) (j : ℕ),
    fresh.Nodup → j < fresh.length → maskWith mask fresh v (fresh.getD j default) = v j
  | [], _, _, _, h => by simp only [List.length_nil] at h; omega
  | a :: l, v, 0, _, _ => by
    show (if a = a then v 0 else _) = v 0
    rw [if_pos rfl]
  | a :: l, v, j + 1, hn, h => by
    have hj : j < l.length := by simp only [List.length_cons] at h; omega
    have hne : l.getD j default ≠ a := fun e =>
      (List.nodup_cons.1 hn).1 (e ▸ getD_mem default l j hj)
    show (if l.getD j default = a then v 0
      else maskWith mask l (fun j => v (j + 1)) (l.getD j default)) = v (j + 1)
    rw [if_neg hne, maskWith_getD mask l _ j (List.nodup_cons.1 hn).2 hj]

/-- Of v the values below the list's length are read, and no other. -/
theorem maskWith_congr (mask : Slot → K) : ∀ (fresh : List Slot) (v v' : ℕ → K),
    (∀ j, j < fresh.length → v j = v' j) → maskWith mask fresh v = maskWith mask fresh v'
  | [], _, _, _ => rfl
  | a :: l, v, v', h => by
    funext s
    show (if s = a then v 0 else maskWith mask l (fun j => v (j + 1)) s) =
      if s = a then v' 0 else maskWith mask l (fun j => v' (j + 1)) s
    rw [h 0 (by simp only [List.length_cons]; omega),
      maskWith_congr mask l (fun j => v (j + 1)) (fun j => v' (j + 1)) fun j hj =>
        h (j + 1) (by simp only [List.length_cons]; omega)]

/-- At the entries' own values nothing turns. -/
theorem maskWith_self (mask : Slot → K) : ∀ fresh : List Slot,
    maskWith mask fresh (fun j => mask (fresh.getD j default)) = mask
  | [] => rfl
  | a :: l => by
    funext s
    show (if s = a then mask a else maskWith mask l (fun j => mask (l.getD j default)) s) = mask s
    rw [maskWith_self mask l]
    split
    · rename_i e
      rw [e]
    · rfl

variable {nR k : ℕ}

/-- The witness with the values v at the taken entries: the same matrix, the same other entries. -/
def withTaken (w : Wit K nR k) (fresh : List Slot) (v : ℕ → K) : Wit K nR k :=
  ⟨w.mat, maskWith w.mask fresh v⟩

/-- At that witness the taken entry number j has the value v j. -/
theorem maskAt_withTaken (w : Wit K nR k) (fresh : List Slot) (v : ℕ → K) (hn : fresh.Nodup)
    (j : ℕ) (hj : j < fresh.length) : maskAt (withTaken w fresh v) fresh j = v j :=
  maskWith_getD w.mask fresh v j hn hj

/-- **At the entries' own values it is the witness itself.** -/
theorem withTaken_own (w : Wit K nR k) (fresh : List Slot) (v : ℕ → K)
    (h : ∀ j, j < fresh.length → v j = maskAt w fresh j) : withTaken w fresh v = w := by
  have e : maskWith w.mask fresh v = w.mask := by
    rw [maskWith_congr w.mask fresh v (fun j => w.mask (fresh.getD j default)) h]
    exact maskWith_self w.mask fresh
  show (⟨w.mat, maskWith w.mask fresh v⟩ : Wit K nR k) = w
  rw [e]

end Family

/-! ## What stays -/

variable {K : Type} [Field K] (ρ : Reading K) {nR k : ℕ}

/-- **A row that names none of the taken entries keeps its truth.** -/
theorem holds_withTaken (w : Wit K nR k) (fresh : List Slot) (v : ℕ → K) (r : TensorRow)
    (hoff : ∀ m ∈ r.masks, m.1 ∉ fresh) : Holds ρ (withTaken w fresh v) r ↔ Holds ρ w r := by
  have e : formVal ρ (maskWith w.mask fresh v) r.masks = formVal ρ w.mask r.masks := by
    unfold formVal
    exact congrArg List.sum (List.map_congr_left fun t ht => by
      rw [maskWith_off w.mask fresh v t.1 (hoff t ht)])
  show Alg.mle (colOf w (weights ρ nR r.g)) _ + formVal ρ (maskWith w.mask fresh v) r.masks = _ ↔
    Alg.mle (colOf w (weights ρ nR r.g)) _ + formVal ρ w.mask r.masks = _
  rw [e]

/-- **The rows' tables read no mask entry.** -/
theorem tabsOf_withTaken (w : Wit K nR k) (fresh : List Slot) (v : ℕ → K) (pile : List TensorRow)
    (a : K) : tabsOf ρ (withTaken w fresh v) pile a = tabsOf ρ w pile a := rfl

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.maskWith_off
#print axioms VerifiableInference.Desc.K13.Honest.getD_mem
#print axioms VerifiableInference.Desc.K13.Honest.maskWith_getD
#print axioms VerifiableInference.Desc.K13.Honest.maskWith_congr
#print axioms VerifiableInference.Desc.K13.Honest.maskWith_self
#print axioms VerifiableInference.Desc.K13.Honest.maskAt_withTaken
#print axioms VerifiableInference.Desc.K13.Honest.withTaken_own
#print axioms VerifiableInference.Desc.K13.Honest.holds_withTaken
#print axioms VerifiableInference.Desc.K13.Honest.tabsOf_withTaken
