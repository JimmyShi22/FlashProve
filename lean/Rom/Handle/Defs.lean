-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Handle/Defs.lean: an oracle algorithm run under ANY rule for answering its queries. DEFINITIONS
ALONE, general in the family of oracles.

General definitions. This file states no goal of the release and proves nothing. The laws are in
Rom/Handle/Laws.lean.

An oracle algorithm (OComp, Rom/OComp.lean) is a tree of queries and draws. Rom/OComp.lean gives it
two meanings: the oracles fixed, or sampled lazily from a table. A proof of index privacy needs more
of them: a simulator answers some queries with fresh values that it does not yet write into the
table, remembers them, and writes them later. So here the rule is a parameter.

  Handler S σ      A rule with a state of type σ: to a state and a query, a law on (answer, next
                   state). It is the type of the field "answer" of a World (Rom/World.lean).
  OComp.interp h   The run of an algorithm under the rule h, from a state: a law on (output, last
                   state). The algorithm's own draws are uniform, as in runLazy.
  Mark S           Which queries are DEFERRED: a test on (oracle, point). It is a parameter, so one
                   oracle can be deferred in one program and plain in another, or at some points
                   only.

The rules.
  Handler.lazy          Lazy sampling from a table. interp of it is runLazy (interp_lazy).
  Handler.fixed f       Every query answered by the function f. No state.
  Handler.idle          Handler.fixed at an arbitrary function: for a dry run, in which only the
                        answers at deferred queries matter.
  Handler.defer mk h    A deferred query gets a FRESH UNIFORM answer, whatever its point is and
                        whatever h's state holds; (oracle, point, answer) is appended to a log, and
                        h's state is left alone. Every other query goes to h.
  Handler.replay mk h   A deferred query gets THE NEXT OF A LIST OF RECORDED ANSWERS, in the list's
                        order, never by its point; it is logged as under defer. Every other query
                        goes to h.

The log is a Trace (Rom/OSpec.lean): first query first, the newest entry LAST.
The recorded answers (the type Record) are a list of (oracle, answer), first answer first: a log
without its points (Trace.answers).

What replay does where the recorded answers do not fit. If the list is empty, or its first entry
belongs to another oracle than the one that is asked, the query gets a fresh uniform answer and the
state's flag "miss" is set, for good. In the second case the entry that did not fit is dropped. So a
replay is always a run with logged answers, and one can see afterwards whether it was fed by the
list alone (miss = false) and whether it has used it up (left = []).

  OComp.runDefer mk     interp of defer mk lazy: table and log.
  OComp.record mk       The dry run: interp of defer mk idle from the empty log; the output and the
                        recorded answers. No table.
  OComp.runReplay mk    interp of replay mk lazy, from a table, a log and recorded answers.
  Table.lay             Write a log into a table, in its order, each entry ONLY WHERE THE TABLE HAS
                        NO ENTRY. (It is what a release does in mode I: releaseAll, Rom/Defer.lean.)
  InStep mk R c c'      Two algorithms ask their deferred queries IN STEP: the same oracles in the
                        same order (the points may differ) as long as both get the same answers,
                        whatever their draws give and whatever their other queries are answered; and
                        their outputs are then related by R. It is the condition under which
                        answers recorded in a run of c can be replayed at c' (replay_of_inStep,
                        Rom/Handle/Laws.lean).
Terms: lean/GLOSSARY.md.

-/
import Rom.World

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {σ α β : Type}

/-- A rule for answering queries, with a state: to a state and a query, a law on (answer, next
state). -/
abbrev Handler (S : OSpec) (σ : Type) : Type :=
  σ → (o : S.ι) → S.Dom o → PMF (S.Rng o × σ)

/-- Which queries are deferred: a test on (oracle, point). -/
abbrev Mark (S : OSpec) : Type := (o : S.ι) → S.Dom o → Bool

/-- A list of answers, each with its oracle's name, first answer first. -/
abbrev Record (S : OSpec) : Type := List (Σ o : S.ι, S.Rng o)

/-- A log without its points. -/
def Trace.answers (l : Trace S) : Record S := l.map fun e => ⟨e.1, e.2.2⟩

/-- **The run of an algorithm under a rule h, from a state.** -/
def OComp.interp (h : Handler S σ) : OComp S α → σ → PMF (α × σ)
  | .pure a, s => PMF.pure (a, s)
  | .query o q k, s => (h s o q).bind fun p => (k p.1).interp h p.2
  | .sample n k, s => (unif (Fin (n + 1))).bind fun r => (k r).interp h s

/-- Write one entry where the table has none. -/
def Table.lay1 (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) : Table S :=
  match T o q with
  | none => T.set o q r
  | some _ => T

/-- **Write a log into a table**, in its order, each entry only where the table has no entry. -/
def Table.lay (T : Table S) : Trace S → Table S
  | [] => T
  | e :: l => Table.lay (T.lay1 e.1 e.2.1 e.2.2) l

/-- The state of a replay: the state of the rule for the other queries; the log; what is left of the
recorded answers; whether a deferred query has found no fitting answer. -/
structure RSt (S : OSpec) (σ : Type) where
  base : σ
  log : Trace S
  left : Record S
  miss : Bool

/-- The next of the recorded answers for the oracle o: the answer, what is left, and whether there
was none that fits. -/
def Record.next (o : S.ι) : Record S → PMF (S.Rng o × Record S × Bool)
  | [] => (unif (S.Rng o)).map fun r => (r, [], true)
  | a :: R =>
      if e : a.1 = o then PMF.pure (e ▸ a.2, R, false)
      else (unif (S.Rng o)).map fun r => (r, R, true)

namespace Handler

/-- Lazy sampling from a table. -/
def lazy : Handler S (Table S) := fun T o q => lazyAnswer T o q

/-- Every query answered by a function. -/
def fixed (f : Fam S) : Handler S Unit := fun _ o q => PMF.pure (f o q, ())

/-- Every query answered by an arbitrary fixed value. -/
def idle : Handler S Unit := fixed fun _ _ => Classical.arbitrary _

/-- **Deferred queries get fresh answers, which are logged; the others go to h.** -/
def defer (mk : Mark S) (h : Handler S σ) : Handler S (σ × Trace S) := fun s o q =>
  if mk o q then (unif (S.Rng o)).map fun r => (r, (s.1, s.2 ++ [⟨o, q, r⟩]))
  else (h s.1 o q).map fun p => (p.1, (p.2, s.2))

/-- **Deferred queries get the recorded answers, in their order, and are logged; the others go to
h.** -/
def replay (mk : Mark S) (h : Handler S σ) : Handler S (RSt S σ) := fun s o q =>
  if mk o q then (Record.next o s.left).map fun p =>
    (p.1, { s with log := s.log ++ [⟨o, q, p.1⟩], left := p.2.1, miss := s.miss || p.2.2 })
  else (h s.base o q).map fun p => (p.1, { s with base := p.2 })

end Handler

namespace OComp

/-- The run with a table and a log: deferred queries get fresh answers and are logged, the others
are sampled lazily. -/
def runDefer (mk : Mark S) (c : OComp S α) (T : Table S) (lg : Trace S) :
    PMF (α × Table S × Trace S) :=
  c.interp (Handler.defer mk Handler.lazy) (T, lg)

/-- The dry run: the output and the list of the fresh answers at the deferred queries. No table:
every other query gets an arbitrary fixed value. -/
def record (mk : Mark S) (c : OComp S α) : PMF (α × Record S) :=
  (c.interp (Handler.defer mk Handler.idle) ((), [])).map fun x => (x.1, x.2.2.answers)

/-- The run with a table, a log and recorded answers: deferred queries get these answers and are
logged, the others are sampled lazily. -/
def runReplay (mk : Mark S) (c : OComp S α) (T : Table S) (lg : Trace S) (R : Record S) :
    PMF (α × RSt S (Table S)) :=
  c.interp (Handler.replay mk Handler.lazy) ⟨T, lg, R, false⟩

end OComp

/-- **Two algorithms ask their deferred queries in step**, and their outputs are related by R. -/
inductive InStep (mk : Mark S) (R : α → β → Prop) : OComp S α → OComp S β → Prop
  | done {a : α} {b : β} : R a b → InStep mk R (.pure a) (.pure b)
  | drawL {n : ℕ} {k : Fin (n + 1) → OComp S α} {c' : OComp S β} :
      (∀ r, InStep mk R (k r) c') → InStep mk R (.sample n k) c'
  | drawR {n : ℕ} {c : OComp S α} {k' : Fin (n + 1) → OComp S β} :
      (∀ r, InStep mk R c (k' r)) → InStep mk R c (.sample n k')
  | plainL {o : S.ι} {q : S.Dom o} {k : S.Rng o → OComp S α} {c' : OComp S β} :
      mk o q = false → (∀ r, InStep mk R (k r) c') → InStep mk R (.query o q k) c'
  | plainR {o : S.ι} {q : S.Dom o} {c : OComp S α} {k' : S.Rng o → OComp S β} :
      mk o q = false → (∀ r, InStep mk R c (k' r)) → InStep mk R c (.query o q k')
  | both {o : S.ι} {q q' : S.Dom o} {k : S.Rng o → OComp S α} {k' : S.Rng o → OComp S β} :
      mk o q = true → mk o q' = true → (∀ r, InStep mk R (k r) (k' r)) →
      InStep mk R (.query o q k) (.query o q' k')

end Rom
