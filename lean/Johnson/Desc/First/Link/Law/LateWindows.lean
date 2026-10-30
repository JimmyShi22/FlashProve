-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LateWindows.lean: WHAT IS LATE BETWEEN TWO LEDGERS, A SLOT AT A TIME;
AND THE LATE SLOTS OF A RUN THAT LAYS WINDOWS. Theorems: tools for `TableOwes.hitems`
(LinkTable.lean) at the entries whose runs write the ledger (the layers' two runs, the merge's),
over Johnson/Desc/First/Batch/ReaderOf.lean's `lateOf` and WorldsMeet.lean.

What is said.
  `lateAt_lateOf`: **under slot j the list `lateOf F G` has what G holds, if j is below G's number
    of slots, free in F and filled in G; else nothing.** `late_in_window`: so a slot of a window
    that is free in F and laid in G with (shown 0, factor −1) is late with just that.
    `late_outside`, `late_free_behind`: a slot that is filled in F, or free in G, is not late.
    `value_meets_windows`: **a form has one worth in the laws' world at the windows and in the
    table's world at `lateOf F G`**, if each slot that it names lies in a window that is free in F
    and laid in G, or is filled in F.

Limits. Tools. That a run's windows are free in the ledger in front and laid behind is each kind's
to show. A slot that lies in no window and is free in the ledger in front is left out of
`value_meets_windows`: there the laws' world reads the ledger's defaults, and the table's may read
the slot late: a kind whose forms name such a slot cannot call the tool. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.WorldsMeet
import Johnson.Desc.First.Batch.ReaderOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K4Values (refWorld InWin LaidAt)
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {α : Type}

/-- A search by the first part in a list that a filter makes of the numbers below n. -/
theorem find_range {β : Type} (c : ℕ → Bool) (v : ℕ → β) (j : ℕ) : ∀ n : ℕ,
    ((List.range n).filterMap fun i => if c i then some (i, v i) else none).find?
        (fun x => x.1 == j) = if j < n ∧ c j = true then some (j, v j) else none
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filterMap_append, List.find?_append, find_range c v j n]
    by_cases h1 : j < n ∧ c j = true
    · rw [if_pos h1, if_pos ⟨Nat.lt_succ_of_lt h1.1, h1.2⟩]
      rfl
    · rw [if_neg h1]
      show (none : Option (ℕ × β)).or _ = _
      rw [Option.none_or]
      by_cases hc : c n = true
      · have e0 : ([n].filterMap fun i => if c i then some (i, v i) else none) = [(n, v n)] := by
          simp [hc]
        rw [e0, List.find?_cons, List.find?_nil]
        by_cases e : n = j
        · subst e
          rw [if_pos ⟨Nat.lt_succ_self n, hc⟩]
          simp
        · have e1 : (n == j) = false := beq_false_of_ne e
          have hne : ¬ (j < n + 1 ∧ c j = true) := by
            rintro ⟨h2, h3⟩
            exact h1 ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h2) fun h => e h.symm, h3⟩
          rw [if_neg hne]
          simp [e1]
      · have e0 : ([n].filterMap fun i => if c i then some (i, v i) else none) = [] := by
          simp [hc]
        have hne : ¬ (j < n + 1 ∧ c j = true) := by
          rintro ⟨h2, h3⟩
          by_cases e : j = n
          · subst e
            exact hc h3
          · exact h1 ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h2) e, h3⟩
        rw [e0, if_neg hne]
        rfl

/-- **What is late under slot j between two ledgers.** -/
theorem lateAt_lateOf (F G : Fork) (j : ℕ) :
    K9.lateAt (K9.lateOf F G) j =
      if j < G.ns ∧ (!(F.gotF.getD j false) && G.gotF.getD j false) = true
      then some (G.vp.getD j zeroE, G.mf.getD j zeroE) else none := by
  unfold K9.lateAt K9.lateOf
  rw [find_range (fun i => !(F.gotF.getD i false) && G.gotF.getD i false)
    (fun i => (G.vp.getD i zeroE, G.mf.getD i zeroE)) j G.ns]
  split <;> rfl

/-- A slot of a window that is free in front and laid behind is late with (shown 0, factor −1). -/
theorem late_in_window (F G : Fork) (w : ℕ × ℕ) (j : ℕ) (hj : InWin w j) (hl : LaidAt G w)
    (hn : j < G.ns) (hf : F.gotF.getD j false = false) (hg : G.gotF.getD j false = true) :
    K9.lateAt (K9.lateOf F G) j = some (zeroE, subE zeroE oneE) := by
  rw [lateAt_lateOf, if_pos ⟨hn, by rw [hf, hg]; rfl⟩, (hl j hj).1, (hl j hj).2]

/-- A slot that is filled in front is not late. -/
theorem late_outside (F G : Fork) (j : ℕ) (hf : F.gotF.getD j false = true) :
    K9.lateAt (K9.lateOf F G) j = none := by
  rw [lateAt_lateOf, if_neg]
  rintro ⟨_, h⟩
  rw [hf] at h
  exact nomatch h

/-- A slot that is free behind is not late. -/
theorem late_free_behind (F G : Fork) (j : ℕ) (hg : G.gotF.getD j false = false) :
    K9.lateAt (K9.lateOf F G) j = none := by
  rw [lateAt_lateOf, if_neg]
  rintro ⟨_, h⟩
  rw [hg, Bool.and_false] at h
  exact nomatch h

/-- **A form has one worth in the laws' world at the windows and in the table's world at what is
late between the two ledgers.** -/
theorem value_meets_windows (a : K9.Part) (G : Fork) (wins : List (ℕ × ℕ)) (y : Bound GQ)
    (q : α × Option Pub9) (hq : q.2 = some (pubOf a)) (f : Aff)
    (he : ∀ x ∈ f.ents.toList, (a.L.arrayOf[x.tree]?).isSome = true)
    (hs : ∀ x ∈ f.slots.toList,
      (∃ w ∈ wins, InWin w x.1 ∧ LaidAt G w ∧ x.1 < G.ns ∧ a.F.gotF.getD x.1 false = false ∧
        G.gotF.getD x.1 false = true) ∨
      ((¬ ∃ w ∈ wins, InWin w x.1) ∧ Filled a.F x.1)) :
    f.value Reading.gl (refWorld Reading.gl a.F wins (entUnit q y) y) =
      f.value Reading.gl (worldOwn a (K9.lateOf a.F G) y) := by
  refine value_meets a wins (K9.lateOf a.F G) y q hq f he (fun x hx hw => ?_) fun x hx hn => ?_
  · rcases hs x hx with ⟨w, _, h1, h2, h3, h4, h5⟩ | ⟨h, _⟩
    · exact late_in_window a.F G w x.1 h1 h2 h3 h4 h5
    · exact absurd hw h
  · rcases hs x hx with ⟨w, hw, h1, _⟩ | ⟨_, h⟩
    · exact absurd ⟨w, hw, h1⟩ hn
    · exact late_outside a.F G x.1 h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.find_range
#print axioms VerifiableInference.Desc.LinkJoin.lateAt_lateOf
#print axioms VerifiableInference.Desc.LinkJoin.late_in_window
#print axioms VerifiableInference.Desc.LinkJoin.late_outside
#print axioms VerifiableInference.Desc.LinkJoin.late_free_behind
#print axioms VerifiableInference.Desc.LinkJoin.value_meets_windows
