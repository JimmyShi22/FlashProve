-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsRuns2.lean: more laws for OnBytes/Tie/Pv/Keeps/KeepsRuns.lean: what a
success says of the calls that only test or read, at the layer of a link. Each leaves the whole
state as it was.

Limits: one direction: from a success.
-/
import OnBytes.Tie.Pv.Keeps.KeepsRuns
import OnBytes.Model.HeadHeard

namespace OnBytes.L5

open OnBytes OnBytes.Model

/-- A block under a link: it has run on the context, and the link's and the sub-proof's states are
as they were. -/
theorem runs_up2 {α : Type} {x : Blk α} {s : HasRuns.St LinkM} {a : α} {s' : HasRuns.St LinkM}
    (h : Runs (liftM x : LinkM α) s a s') :
    Runs x s.2.2 a s'.2.2 ∧ s'.1 = s.1 ∧ s'.2.1 = s.2.1 := by
  obtain ⟨h1, e1⟩ := runs_up h
  obtain ⟨h2, e2⟩ := runs_up h1
  exact ⟨h2, e1, e2⟩

/-- A state of a link by its three parts. -/
theorem st_ext {s s' : HasRuns.St LinkM} (e1 : s'.1 = s.1) (e2 : s'.2.1 = s.2.1)
    (e3 : s'.2.2 = s.2.2) : s' = s := Prod.ext e1 (Prod.ext e2 e3)

/-- A condition on values under a name, on a view: it was true, and the context is as it was. -/
theorem runs_testAs {n : String} {b : Bool} {c : Ctx} {u : Unit} {c' : Ctx}
    (h : Runs (testAs n b) c u c') (hd : c.ch.dry = false) : b = true ∧ c' = c := by
  have h' : (if (b || c.ch.dry) = true then (pure () : Blk Unit) else refuse n) c = .ok (u, c') := h
  rw [hd, Bool.or_false] at h'
  cases b with
  | true => cases h'; exact ⟨rfl, rfl⟩
  | false => cases h'

/-- A value that must be there, under a name. -/
theorem runs_getAs {α : Type} {n : String} {x : Option α} {c : Ctx} {a : α} {c' : Ctx}
    (h : Runs (Head.getAs n x) c a c') : x = some a ∧ c' = c := by
  cases x with
  | none => cases h
  | some y => cases h; exact ⟨rfl, rfl⟩

/-- Reading a value off the sub-proof's state. -/
theorem runs_ask {α : Type} {f : Fork → Option α} {t : HasRuns.St SubM} {a : α}
    {t' : HasRuns.St SubM} (h : Runs (SubM.ask f) t a t') : f t.1 = some a ∧ t' = t := by
  have h' : SubM.ask f t.1 t.2 = .ok ((a, t'.1), t'.2) := h
  unfold SubM.ask at h'
  cases e : f t.1 with
  | none => rw [e] at h'; cases h'
  | some y =>
    rw [e] at h'
    have k : (Except.ok ((y, t.1), t.2) : Except Failure ((α × Fork) × Ctx)) =
      .ok ((a, t'.1), t'.2) := h'
    cases t'
    cases k
    exact ⟨rfl, rfl⟩

theorem mustAs_L {n : String} {b : Bool} {s : HasRuns.St LinkM} {u : Unit} {s' : HasRuns.St LinkM}
    (h : Runs (liftM (mustAs n b) : LinkM Unit) s u s') : b = true ∧ s' = s := by
  obtain ⟨h1, e1, e2⟩ := runs_up2 h
  obtain ⟨hb, e3⟩ := runs_mustAs h1
  exact ⟨hb, st_ext e1 e2 e3⟩

theorem testAs_L {n : String} {b : Bool} {s : HasRuns.St LinkM} {u : Unit} {s' : HasRuns.St LinkM}
    (h : Runs (liftM (testAs n b) : LinkM Unit) s u s') (d : View s) : b = true ∧ s' = s := by
  obtain ⟨h1, e1, e2⟩ := runs_up2 h
  obtain ⟨hb, e3⟩ := runs_testAs h1 d
  exact ⟨hb, st_ext e1 e2 e3⟩

theorem getAs_L {α : Type} {n : String} {x : Option α} {s : HasRuns.St LinkM} {a : α}
    {s' : HasRuns.St LinkM} (h : Runs (liftM (Head.getAs n x) : LinkM α) s a s') :
    x = some a ∧ s' = s := by
  obtain ⟨h1, e1, e2⟩ := runs_up2 h
  obtain ⟨hb, e3⟩ := runs_getAs h1
  exact ⟨hb, st_ext e1 e2 e3⟩

/-- The sub-proof's state, read in a link. -/
theorem fork_L {s : HasRuns.St LinkM} {a : Fork} {s' : HasRuns.St LinkM}
    (h : Runs LinkM.fork s a s') : a = s.2.1 ∧ s' = s := by
  obtain ⟨h1, e1⟩ := runs_sub h
  obtain ⟨h2, e2⟩ := runs_ask h1
  exact ⟨(Option.some.inj h2).symm, Prod.ext e1 e2⟩

#print axioms runs_up2
#print axioms runs_testAs
#print axioms runs_getAs
#print axioms runs_ask
#print axioms mustAs_L
#print axioms testAs_L
#print axioms getAs_L
#print axioms fork_L

end OnBytes.L5
