-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Follow.lean: an algorithm without coins, followed in a trace.

Definitions, statements with their proofs. Generic: any family of oracles.
An extractor of a compiled argument has no oracle. What it can do is follow an algorithm in a list
of queries and answers that it is handed: where the algorithm asks, look the answer up; if the list
does not hold the query, give up.

Main names:
  `OComp.follow tr c`: c followed in tr. It is some a if every query on the way is in tr and c ends
    with a; it is none if a query is missing, or if c tosses a coin.
  `runsIn_of_follow`: what is followed runs within the trace (`RunsIn`, Compile/Spec.lean).
  `follow_of_runsIn`: if no point has two answers in tr (`Trace.Fun tr`), what runs within the trace
    is what is followed.
  `follow_mono`: so what is followed in tr is followed to the same end in every such trace that has
    all entries of tr.

Limits: this file says nothing on where a trace comes from, and nothing on probabilities.
-/
import Compile.MerkleRom
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open Compile (RunsIn)

variable {S : OSpec} {α : Type}

open Classical in
/-- The answer of one entry at (o, q), if the entry is at that point. -/
def QA.at? (e : QA S) (o : S.ι) (q : S.Dom o) : Option (S.Rng o) :=
  if h : ∃ r : S.Rng o, e = ⟨o, q, r⟩ then some h.choose else none

theorem QA.at?_self (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    QA.at? (⟨o, q, r⟩ : QA S) o q = some r := by
  have h : ∃ r' : S.Rng o, (⟨o, q, r⟩ : QA S) = ⟨o, q, r'⟩ := ⟨r, rfl⟩
  unfold QA.at?
  rw [dif_pos h]
  have e := h.choose_spec
  have e2 : (q, r) = (q, h.choose) := eq_of_heq (Sigma.mk.inj_iff.1 e).2
  exact congrArg some (Prod.mk.inj e2).2.symm

theorem QA.eq_of_at? {e : QA S} {o : S.ι} {q : S.Dom o} {r : S.Rng o} (h : QA.at? e o q = some r) :
    e = ⟨o, q, r⟩ := by
  unfold QA.at? at h
  split_ifs at h with hx
  obtain rfl := Option.some.inj h
  exact hx.choose_spec

/-- The answer that a trace has at a point: that of its first entry there. (Equality of points is
decided classically.) -/
def Trace.ans (tr : Trace S) (o : S.ι) (q : S.Dom o) : Option (S.Rng o) :=
  tr.findSome? fun e => QA.at? e o q

/-- No point has two answers. -/
def Trace.Fun (tr : Trace S) : Prop :=
  ∀ (o : S.ι) (q : S.Dom o) (r r' : S.Rng o),
    (⟨o, q, r⟩ : QA S) ∈ tr → (⟨o, q, r'⟩ : QA S) ∈ tr → r = r'

/-- Every answer is that of the function f (so `Trace.Fun tr`). -/
def Trace.Of (f : Fam S) (tr : Trace S) : Prop :=
  ∀ (o : S.ι) (q : S.Dom o) (r : S.Rng o), (⟨o, q, r⟩ : QA S) ∈ tr → r = f o q

theorem Trace.Of.fun {f : Fam S} {tr : Trace S} (h : Trace.Of f tr) : Trace.Fun tr :=
  fun o q r r' h1 h2 => (h o q r h1).trans (h o q r' h2).symm

theorem Trace.Of.append {f : Fam S} {tr tr' : Trace S} (h : Trace.Of f tr) (h' : Trace.Of f tr') :
    Trace.Of f (tr ++ tr') :=
  fun o q r hm => (List.mem_append.1 hm).elim (h o q r) (h' o q r)

theorem Trace.mem_of_ans {tr : Trace S} {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (h : Trace.ans tr o q = some r) : (⟨o, q, r⟩ : QA S) ∈ tr := by
  obtain ⟨e, he, h2⟩ := List.exists_of_findSome?_eq_some h
  rw [← QA.eq_of_at? h2]
  exact he

theorem Trace.ans_of_mem {tr : Trace S} (hf : Trace.Fun tr) {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (h : (⟨o, q, r⟩ : QA S) ∈ tr) : Trace.ans tr o q = some r := by
  cases hx : Trace.ans tr o q with
  | none =>
    have := List.findSome?_eq_none_iff.1 hx _ h
    rw [QA.at?_self] at this
    cases this
  | some r' => rw [hf o q r r' h (Trace.mem_of_ans hx)]

/-- The algorithm, followed in the trace. -/
def OComp.follow (tr : Trace S) : OComp S α → Option α
  | .pure a => some a
  | .query o q k => (Trace.ans tr o q).bind fun r => (k r).follow tr
  | .sample _ _ => none

theorem runsIn_of_follow {tr : Trace S} :
    ∀ {c : OComp S α} {a : α}, c.follow tr = some a → RunsIn tr c a
  | .pure _, _, h => by
      obtain rfl := Option.some.inj h
      exact RunsIn.pure _
  | .query o q k, a, h => by
      obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.1 h
      exact RunsIn.query o q k r a (Trace.mem_of_ans hr) (runsIn_of_follow h2)
  | .sample _ _, _, h => by cases h

theorem follow_of_runsIn {tr : Trace S} (hf : Trace.Fun tr) {c : OComp S α}
    {a : α} (h : RunsIn tr c a) : c.follow tr = some a := by
  induction h with
  | pure a => rfl
  | query o q k r a hm _ ih =>
    show (Trace.ans tr o q).bind (fun r => (k r).follow tr) = some a
    rw [Trace.ans_of_mem hf hm]
    exact ih

theorem follow_mono {tr tr' : Trace S} (hs : tr ⊆ tr') (hf : Trace.Fun tr') {c : OComp S α}
    {a : α} (h : c.follow tr = some a) : c.follow tr' = some a :=
  follow_of_runsIn hf ((runsIn_of_follow h).mono hs)

end Rom
