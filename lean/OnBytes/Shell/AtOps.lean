-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtOps.lean: the driver `Ask.run` for all operations, with the state of the outside
world passed from step to step.

An action `x : EST ε σ α` is a plain function from a state to `ok a s'` or `error e s'` (Lean
4.29). `IO` is the case ε := `IO.Error`, σ := `IO.RealWorld`.
- `Run x s a s'`: started in the state s, x returns a without an exception and leaves the state s'.
- `Steps w evs s s'`: the three operations w gave the answers in evs one after another, from s to
  s'. Each is applied to the state that the one before it left.
- `Ask.run_iff`: for all operations w, the driver `q.run w` started in s returns a in s' exactly if
  there is a run of q (OnBytes/Shell/Ends.lean) that ends with a and whose answers w gave from s to
  s'. The theorem is about `Ask.run` itself, in the monad in which the program runs it.
- `steps_one`: from one state the operations w give the answers of at most one run of a program.
- `NoThrow x`: x throws in no state. `noThrow_run`: if no operation throws, the driver does not.
  `readIO_noThrow`, `outIO_noThrow`, `errIO_noThrow`: the program's three operations do not throw.

What is not claimed. Nothing about compiled code, Lean's run-time or the operating system: the
theorems are about the terms that Lean's kernel checks. Nothing about files: Lean's logic has no
file system. For proofs only; the program does not import this file.
-/
import OnBytes.Shell.Ops
import OnBytes.Shell.Ends

namespace OnBytes.Shell

variable {ε σ α β : Type}

/-- Started in the state s, x returns a without an exception and leaves the state s'. -/
def Run (x : EST ε σ α) (s : Void σ) (a : α) (s' : Void σ) : Prop := x s = EST.Out.ok a s'

/-- Two actions in a row return exactly if the second returns from where the first returned. -/
theorem run_bind {x : EST ε σ α} {f : α → EST ε σ β} {s s' : Void σ} {b : β} :
    Run (x >>= f) s b s' ↔ ∃ a s1, Run x s a s1 ∧ Run (f a) s1 b s' := by
  constructor
  · intro h
    have h2 : EST.bind x f s = EST.Out.ok b s' := h
    unfold EST.bind at h2
    split at h2
    · rename_i a s1 hx
      exact ⟨a, s1, hx, h2⟩
    · cases h2
  · rintro ⟨a, s1, h1, h2⟩
    show EST.bind x f s = EST.Out.ok b s'
    unfold EST.bind
    rw [show x s = EST.Out.ok a s1 from h1]
    exact h2

/-- The action that only returns a returns a and leaves the state as it was. -/
theorem run_pure {a b : α} {s s' : Void σ} :
    Run (pure a : EST ε σ α) s b s' ↔ a = b ∧ s = s' := by
  constructor
  · intro h
    have h2 : (EST.Out.ok a s : EST.Out ε σ α) = EST.Out.ok b s' := h
    cases h2
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A `tryCatch` returns exactly if its body returned, or the body threw and the handler, started
in the state that the body left, returned. -/
theorem run_try {x : EST ε σ α} {g : ε → EST ε σ α} {s s' : Void σ} {a : α} :
    Run (tryCatch x g) s a s' ↔
      Run x s a s' ∨ ∃ e s1, x s = EST.Out.error e s1 ∧ Run (g e) s1 a s' := by
  constructor
  · intro h
    have h2 : EST.tryCatch x g s = EST.Out.ok a s' := h
    unfold EST.tryCatch at h2
    split at h2
    · rename_i a0 s1 hx
      cases h2
      exact Or.inl hx
    · rename_i e s1 hx
      exact Or.inr ⟨e, s1, hx, h2⟩
  · intro h
    show EST.tryCatch x g s = EST.Out.ok a s'
    unfold EST.tryCatch
    rcases h with h | ⟨e, s1, h1, h2⟩
    · rw [show x s = EST.Out.ok a s' from h]
    · rw [h1]
      exact h2

/-- The action x throws in no state. -/
def NoThrow (x : EST ε σ α) : Prop := ∀ s e s', x s ≠ EST.Out.error e s'

/-- The action that only returns a does not throw. -/
theorem noThrow_pure (a : α) : NoThrow (pure a : EST ε σ α) := fun s e s' h => by
  have h2 : (EST.Out.ok a s : EST.Out ε σ α) = EST.Out.error e s' := h
  cases h2

/-- Two actions that do not throw, one after the other, do not throw. -/
theorem noThrow_bind {x : EST ε σ α} {f : α → EST ε σ β} (hx : NoThrow x)
    (hf : ∀ a, NoThrow (f a)) : NoThrow (x >>= f) := fun s e s' h => by
  have h2 : EST.bind x f s = EST.Out.error e s' := h
  unfold EST.bind at h2
  split at h2
  · rename_i a s1 h1
    exact hf a s1 e s' h2
  · rename_i e1 s1 h1
    exact hx s e1 s1 h1

/-- A `tryCatch` whose handler does not throw does not throw. -/
theorem noThrow_try {x : EST ε σ α} {g : ε → EST ε σ α} (hg : ∀ e, NoThrow (g e)) :
    NoThrow (tryCatch x g) := fun s e s' h => by
  have h2 : EST.tryCatch x g s = EST.Out.error e s' := h
  unfold EST.tryCatch at h2
  split at h2
  · cases h2
  · rename_i e1 s1 h1
    exact hg e1 s1 e s' h2

/-- An action that throws in no state returns in every state. -/
theorem run_of_noThrow {x : EST ε σ α} (hx : NoThrow x) (s : Void σ) : ∃ a s', Run x s a s' := by
  cases h : x s with
  | ok a s' => exact ⟨a, s', h⟩
  | error e s' => exact absurd h (hx s e s')

/-- The three operations gave these answers one after another, from s to s'. Each is applied to
the state that the one before it left. -/
def Steps (w : Ops (EST ε σ)) : List Event → Void σ → Void σ → Prop
  | [], s, s' => s = s'
  | .read p n got :: t, s, s' => ∃ s1, Run (w.read p n) s got s1 ∧ Steps w t s1 s'
  | .say l ok :: t, s, s' => ∃ s1, Run (w.out l) s ok s1 ∧ Steps w t s1 s'
  | .err x :: t, s, s' => ∃ s1, Run (w.err x) s () s1 ∧ Steps w t s1 s'

/-- For all operations w: the driver returns a exactly if the program has a run that ends with a
and whose answers w gave from s to s'. -/
theorem Ask.run_iff (w : Ops (EST ε σ)) (q : Ask α) : ∀ (s : Void σ) (a : α) (s' : Void σ),
    Run (q.run w) s a s' ↔ ∃ t, q.Ends t a ∧ Steps w t s s' := by
  induction q with
  | done a0 =>
    intro s a s'
    constructor
    · intro h
      obtain ⟨rfl, rfl⟩ := run_pure.1 h
      exact ⟨[], .done _, rfl⟩
    · rintro ⟨t, h1, h2⟩
      obtain ⟨rfl, rfl⟩ := ends_done h1
      exact run_pure.2 ⟨rfl, h2⟩
  | read p n next ih =>
    intro s a s'
    constructor
    · intro h
      obtain ⟨r, s1, h1, h2⟩ :=
        (run_bind (x := w.read p n) (f := fun r => (next r).run w)).1 h
      obtain ⟨t, h3, h4⟩ := (ih r s1 a s').1 h2
      exact ⟨.read p n r :: t, .read h3, s1, h1, h4⟩
    · rintro ⟨t, h1, h2⟩
      obtain ⟨got, t', rfl, h3⟩ := ends_read h1
      obtain ⟨s1, h4, h5⟩ := h2
      exact (run_bind (x := w.read p n) (f := fun r => (next r).run w)).2
        ⟨got, s1, h4, (ih got s1 a s').2 ⟨t', h3, h5⟩⟩
  | say l next ih =>
    intro s a s'
    constructor
    · intro h
      obtain ⟨r, s1, h1, h2⟩ := (run_bind (x := w.out l) (f := fun r => (next r).run w)).1 h
      obtain ⟨t, h3, h4⟩ := (ih r s1 a s').1 h2
      exact ⟨.say l r :: t, .say h3, s1, h1, h4⟩
    · rintro ⟨t, h1, h2⟩
      obtain ⟨ok, t', rfl, h3⟩ := ends_say h1
      obtain ⟨s1, h4, h5⟩ := h2
      exact (run_bind (x := w.out l) (f := fun r => (next r).run w)).2
        ⟨ok, s1, h4, (ih ok s1 a s').2 ⟨t', h3, h5⟩⟩
  | err x next ih =>
    intro s a s'
    constructor
    · intro h
      obtain ⟨u, s1, h1, h2⟩ := (run_bind (x := w.err x) (f := fun _ => next.run w)).1 h
      obtain ⟨t, h3, h4⟩ := (ih s1 a s').1 h2
      exact ⟨.err x :: t, .err h3, s1, h1, h4⟩
    · rintro ⟨t, h1, h2⟩
      obtain ⟨t', rfl, h3⟩ := ends_err h1
      obtain ⟨s1, h4, h5⟩ := h2
      exact (run_bind (x := w.err x) (f := fun _ => next.run w)).2
        ⟨(), s1, h4, (ih s1 a s').2 ⟨t', h3, h5⟩⟩

/-- From one state a program has at most one run: two runs whose answers the operations gave from
the same state are the same, and so are their results. -/
theorem steps_one (w : Ops (EST ε σ)) (q : Ask α) : ∀ (s s1 s2 : Void σ) (e1 e2 : List Event)
    (r1 r2 : α), q.Ends e1 r1 → Steps w e1 s s1 → q.Ends e2 r2 → Steps w e2 s s2 →
    e1 = e2 ∧ r1 = r2 := by
  induction q with
  | done a =>
    intro s s1 s2 e1 e2 r1 r2 h1 _ h2 _
    obtain ⟨rfl, rfl⟩ := ends_done h1
    obtain ⟨rfl, rfl⟩ := ends_done h2
    exact ⟨rfl, rfl⟩
  | read p n next ih =>
    intro s s1 s2 e1 e2 r1 r2 h1 t1 h2 t2
    obtain ⟨g1, u1, rfl, k1⟩ := ends_read h1
    obtain ⟨g2, u2, rfl, k2⟩ := ends_read h2
    obtain ⟨a1, x1, y1⟩ := t1
    obtain ⟨a2, x2, y2⟩ := t2
    have h3 : EST.Out.ok g1 a1 = (EST.Out.ok g2 a2 : EST.Out ε σ FileRead) := x1.symm.trans x2
    cases h3
    obtain ⟨rfl, rfl⟩ := ih g1 a1 s1 s2 u1 u2 r1 r2 k1 y1 k2 y2
    exact ⟨rfl, rfl⟩
  | say l next ih =>
    intro s s1 s2 e1 e2 r1 r2 h1 t1 h2 t2
    obtain ⟨g1, u1, rfl, k1⟩ := ends_say h1
    obtain ⟨g2, u2, rfl, k2⟩ := ends_say h2
    obtain ⟨a1, x1, y1⟩ := t1
    obtain ⟨a2, x2, y2⟩ := t2
    have h3 : EST.Out.ok g1 a1 = (EST.Out.ok g2 a2 : EST.Out ε σ Bool) := x1.symm.trans x2
    cases h3
    obtain ⟨rfl, rfl⟩ := ih g1 a1 s1 s2 u1 u2 r1 r2 k1 y1 k2 y2
    exact ⟨rfl, rfl⟩
  | err x next ih =>
    intro s s1 s2 e1 e2 r1 r2 h1 t1 h2 t2
    obtain ⟨u1, rfl, k1⟩ := ends_err h1
    obtain ⟨u2, rfl, k2⟩ := ends_err h2
    obtain ⟨a1, x1, y1⟩ := t1
    obtain ⟨a2, x2, y2⟩ := t2
    have h3 : EST.Out.ok () a1 = (EST.Out.ok () a2 : EST.Out ε σ Unit) := x1.symm.trans x2
    cases h3
    obtain ⟨rfl, rfl⟩ := ih a1 s1 s2 u1 u2 r1 r2 k1 y1 k2 y2
    exact ⟨rfl, rfl⟩

/-- Where no operation throws, the driver does not throw. -/
theorem noThrow_run {w : Ops (EST ε σ)} (h1 : ∀ p n, NoThrow (w.read p n))
    (h2 : ∀ l, NoThrow (w.out l)) (h3 : ∀ x, NoThrow (w.err x)) (q : Ask α) :
    NoThrow (q.run w) := by
  induction q with
  | done a => exact noThrow_pure a
  | read p n next ih =>
    exact noThrow_bind (x := w.read p n) (f := fun r => (next r).run w) (h1 p n) ih
  | say l next ih => exact noThrow_bind (x := w.out l) (f := fun r => (next r).run w) (h2 l) ih
  | err x next ih =>
    exact noThrow_bind (x := w.err x) (f := fun _ => next.run w) (h3 x) fun _ => ih

/-- A state in Lean's model of IO. -/
abbrev World : Type := Void IO.RealWorld

/-- A state exists, so a statement about all states is not vacuous. Lean's logic knows nothing more
about the type of states. -/
theorem world_nonempty : Nonempty World := inferInstance

/-- Reading a file throws in no state. -/
theorem readIO_noThrow (p : String) (n : Nat) : NoThrow (readIO p n) :=
  noThrow_try fun e => by
    cases e <;> first
      | exact noThrow_pure _
      | exact noThrow_try fun _ => noThrow_pure _

/-- Printing a line throws in no state. -/
theorem outIO_noThrow (l : String) : NoThrow (outIO l) := noThrow_try fun _ => noThrow_pure _

/-- Writing to standard error throws in no state. -/
theorem errIO_noThrow (x : String) : NoThrow (errIO x) := noThrow_try fun _ => noThrow_pure _

end OnBytes.Shell
