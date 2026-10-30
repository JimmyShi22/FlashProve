-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hash/MerklePure.lean: Merkle trees as pure combinatorics.

  Part 1  trees of any binary shape: `Shape`, `Shape.Pos`, perfect trees
  Part 2  events, occurrence, and the hash event E_M (`Events.HashEvent`), relative to a given
          notion of "occurs at"
  Part 3  the extractor that reads a tree off a list of hash queries (`OraclePair.preimage`)
  Part 4  outside the hash event, under the hypotheses of their statements: extraction is stable,
          and openings agree with extraction, for leaf inputs
          (`preimage_stable`, `preimage_of_opensIn`)

There is no probability in this file, and no random oracle. A trace is a list of events of an
arbitrary type E, of which only a few projections are used. The file imports Mathlib only.

Notes.
1. "Occurs at" is a parameter: the field `occ` of `Events`. Two conditions are put on it: the answer
   of a Merkle query occurs at it (`Events.answer_mem_occ`), and so do both halves of the input of a
   node query (`OraclePair.occurs_left`, `occurs_right`). Other occurrences (root fields of
   Fiat-Shamir queries, announcements, the final output) are for the user of the file to put into
   `occ`.
2. Traces here may list a repeated query again. In E_M only an entry that is not in the trace before
   counts.
3. Nothing forbids that one event is a leaf query and a node query at once, or that two pairs of
   oracles share events.
4. Padding of an oracle to a power of two is not treated.

Notation: `D`: a type, the digests; `Ev : Events E D`: what the hash event looks at in an event of a
trace; `X`: a type, the inputs of queries to the leaf oracle; `V : OraclePair Ev X`: a pair of
Merkle oracles in a trace.

Limits: this file does not define Commit, Check or roles, and does not prove the two lemmas of Part
4 for roles.

The step of reading the leaves of a Merkle tree off the list of an algorithm's random-oracle
queries, without rewinding, is public: Paul Valiant, "Incrementally Verifiable Computation or Proofs
of Knowledge Imply Time/Space Efficiency", TCC 2008 (LNCS 4948, pages 1-18); Eli Ben-Sasson,
Alessandro Chiesa and Nicholas Spooner, "Interactive Oracle Proofs", ePrint 2016/116, state it as a
procedure ("Valiant's extractor"). This library assumes no result of these papers: it proves its own
form of the step.
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace Merkle

/-! ## Part 1. Shapes and positions -/

/-- The shape of a finite binary tree in which every inner vertex has two children. -/
inductive Shape : Type
  | leaf : Shape
  | node : Shape → Shape → Shape
  deriving DecidableEq, Repr

namespace Shape

/-- The leaves of a tree of the given shape. A leaf is named by the path to it from the root. -/
inductive Pos : Shape → Type
  | here : Pos leaf
  | left {l r : Shape} : Pos l → Pos (node l r)
  | right {l r : Shape} : Pos r → Pos (node l r)
  deriving DecidableEq







/-- The perfect binary tree of depth d. -/
def perfect : ℕ → Shape
  | 0 => leaf
  | d + 1 => node (perfect d) (perfect d)



end Shape

open Shape (Pos)

/-! ## Part 2. Events, occurrence, the hash event -/

/-- What the hash event looks at in an event of a trace. The type E of events is arbitrary:
besides queries to Merkle oracles it may hold queries to other oracles, announcements, outputs.
* answer e = some c says that e is a query to some Merkle oracle (of any tree, leaf or node) with
  the answer c.
* occ e lists the digests that occur at e. The answer of a Merkle query occurs at it. What else
  occurs (the halves of the input of a node query, root fields of other queries, announced digests)
  is for the user to say; the pairs of oracles below require the halves.
An event must not say more about a query than oracle, input and answer. If it also held who asked,
or when, a repeated query would be a different event from its first occurrence, and it would count
as new in the hash event below. -/
structure Events (E D : Type) where
  /-- the answer, if the event is a query to a Merkle oracle -/
  answer : E → Option D
  /-- the digests that occur at the event -/
  occ : E → List D
  answer_mem_occ : ∀ {e : E} {c : D}, answer e = some c → c ∈ occ e

namespace Events

variable {E D : Type} (Ev : Events E D)

/-- The digest c occurs at the event e. -/
def Occurs (e : E) (c : D) : Prop := c ∈ Ev.occ e

/-- The digest c occurs at some event of the trace. -/
def OccursIn (tr : List E) (c : D) : Prop := ∃ e ∈ tr, Ev.Occurs e c

/-- All digests that occur at events of the trace, with repetitions. -/
def occAll (tr : List E) : List D := tr.flatMap Ev.occ

/-- The hash event E_M: the answer of some new Merkle query occurs at an earlier event.
"New" means that the same event is not in the trace before. For traces that do not list a repeated
query a second time the clause always holds (`hashEvent_iff_of_fresh`). The clause is there for
traces that list every query, repeated or not: a repeated query gets its old answer, so nothing
random happens there. That the event is the same as in the trace without the repetitions is not
proved in this file. -/
def HashEvent (tr : List E) : Prop :=
  ∃ (pre : List E) (e : E) (post : List E) (c : D),
    tr = pre ++ e :: post ∧ e ∉ pre ∧ Ev.answer e = some c ∧ Ev.OccursIn pre c

variable {Ev}

theorem occurs_answer {e : E} {c : D} (h : Ev.answer e = some c) : Ev.Occurs e c :=
  Ev.answer_mem_occ h

theorem mem_occAll {tr : List E} {c : D} : c ∈ Ev.occAll tr ↔ Ev.OccursIn tr c := by
  simp only [occAll, List.mem_flatMap, OccursIn, Occurs]

theorem OccursIn.mono {tr tr' : List E} {c : D} (h : Ev.OccursIn tr c) (hs : tr ⊆ tr') :
    Ev.OccursIn tr' c := by
  obtain ⟨e, he, ho⟩ := h
  exact ⟨e, hs he, ho⟩

/-- The length of occAll is the sum of the lengths of occ e over the events e of the trace. -/
theorem length_occAll (tr : List E) :
    (Ev.occAll tr).length = (tr.map fun e => (Ev.occ e).length).sum := by
  simp only [occAll, List.length_flatMap]

/-- If at most k digests occur at each event, at most k · (length of the trace) digests occur in the
trace. -/
theorem length_occAll_le {k : ℕ} (hk : ∀ e, (Ev.occ e).length ≤ k) (tr : List E) :
    (Ev.occAll tr).length ≤ k * tr.length := by
  induction tr with
  | nil => simp [occAll]
  | cons e tr ih =>
      have h := hk e
      simp only [occAll, List.flatMap_cons, List.length_append,
        List.length_cons, Nat.mul_succ] at ih ⊢
      omega

theorem not_hashEvent_nil : ¬ Ev.HashEvent [] := by
  rintro ⟨pre, e, post, c, h, -⟩
  simp at h

/-- The hash event of a prefix is a hash event of the whole trace. -/
theorem HashEvent.of_prefix {tr' tr : List E} (hp : tr' <+: tr) (h : Ev.HashEvent tr') :
    Ev.HashEvent tr := by
  obtain ⟨suf, rfl⟩ := hp
  obtain ⟨pre, e, post, c, rfl, hne, ha, ho⟩ := h
  exact ⟨pre, e, post ++ suf, c, by simp, hne, ha, ho⟩

/-- The hash event, one step at a time. It happens in tr followed by e if and only if it happens in
tr, or e is a new Merkle query whose answer is among the digests that occur in tr. This is the form
in which the event is counted: when the answer of a new query is uniform, the second case has
probability (number of different digests in occAll tr) / |D|, which is at most (length of occAll
tr) / |D|. -/
theorem hashEvent_concat_iff {tr : List E} {e : E} :
    Ev.HashEvent (tr ++ [e]) ↔
    Ev.HashEvent tr ∨ (e ∉ tr ∧ ∃ c, Ev.answer e = some c ∧ c ∈ Ev.occAll tr) := by
  constructor
  · rintro ⟨pre, e0, post, c, h, hne, ha, ho⟩
    rcases List.eq_nil_or_concat' post with rfl | ⟨post', x, rfl⟩
    · obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      obtain rfl := h1
      obtain rfl : e = e0 := by simpa using h2
      exact Or.inr ⟨hne, c, ha, mem_occAll.2 ho⟩
    · have h' : tr ++ [e] = (pre ++ e0 :: post') ++ [x] := by simpa using h
      obtain ⟨h1, -⟩ := List.append_inj' h' rfl
      exact Or.inl ⟨pre, e0, post', c, h1, hne, ha, ho⟩
  · rintro (h | ⟨hne, c, ha, ho⟩)
    · exact h.of_prefix (List.prefix_append _ _)
    · exact ⟨tr, e, [], c, rfl, hne, ha, mem_occAll.1 ho⟩

/-- For a trace in which no Merkle query is listed twice the hash event says: there are indices
v' < v such that the event at v is a Merkle query whose answer occurs at the event at v'. -/
theorem hashEvent_iff_of_fresh {tr : List E}
    (hfresh : ∀ (v : ℕ) (hv : v < tr.length), (Ev.answer tr[v]).isSome → tr[v] ∉ tr.take v) :
    Ev.HashEvent tr ↔ ∃ (v' v : ℕ) (_ : v' < v) (hv : v < tr.length) (c : D),
      Ev.answer tr[v] = some c ∧ Ev.Occurs (tr[v']'(by omega)) c := by
  constructor
  · rintro ⟨pre, e, post, c, rfl, -, ha, e', he', ho⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he'
    refine ⟨i, pre.length, hi, by simp, c, ?_, ?_⟩
    · simpa using ha
    · rw [List.getElem_append_left hi]; exact ho
  · rintro ⟨v', v, hlt, hv, c, ha, ho⟩
    refine ⟨tr.take v, tr[v], tr.drop (v + 1), c, ?_,
      hfresh v hv (by rw [ha]; rfl), ha, tr[v'], ?_, ho⟩
    · rw [List.getElem_cons_drop, List.take_append_drop]
    · exact List.mem_iff_getElem.2 ⟨v', by rw [List.length_take]; omega, by rw [List.getElem_take]⟩

/-- `hashEvent_iff_of_fresh` for a trace without any repetition. -/
theorem hashEvent_iff_of_nodup {tr : List E} (hnd : tr.Nodup) :
    Ev.HashEvent tr ↔ ∃ (v' v : ℕ) (_ : v' < v) (hv : v < tr.length) (c : D),
      Ev.answer tr[v] = some c ∧ Ev.Occurs (tr[v']'(by omega)) c := by
  refine hashEvent_iff_of_fresh fun v hv _ hmem => ?_
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 hmem
  rw [List.getElem_take] at hie
  have hi' : i < v := by
    rw [List.length_take] at hi; omega
  have := (hnd.getElem_inj_iff).1 hie
  omega

/-- Outside the hash event, a Merkle query of the trace whose answer occurs in a prefix of the trace
is in that prefix. -/
theorem mem_prefix_of_answer {tr' tr : List E} (h : ¬ Ev.HashEvent tr) (hp : tr' <+: tr) {c : D}
    (ho : Ev.OccursIn tr' c) {e : E} (he : e ∈ tr) (ha : Ev.answer e = some c) : e ∈ tr' := by
  by_contra hn
  obtain ⟨suf, rfl⟩ := hp
  have hs : e ∈ suf := (List.mem_append.1 he).resolve_left hn
  obtain ⟨as, bs, rfl, has⟩ := List.eq_append_cons_of_mem hs
  exact h
    ⟨tr' ++ as, e, bs, c, by simp, by simp [hn, has], ha, ho.mono (List.subset_append_left _ _)⟩

/-- Outside the hash event, no two Merkle queries of the trace have the same answer. -/
theorem eq_of_answer_eq {tr : List E} (h : ¬ Ev.HashEvent tr) {e e' : E} {c : D} (he : e ∈ tr)
    (he' : e' ∈ tr) (ha : Ev.answer e = some c) (ha' : Ev.answer e' = some c) : e = e' := by
  by_contra hne
  obtain ⟨as, bs, rfl, has⟩ := List.eq_append_cons_of_mem he
  have hp : as ++ [e] <+: as ++ e :: bs := ⟨bs, by simp⟩
  have hm : e' ∈ as ++ [e] := mem_prefix_of_answer h hp ⟨e, by simp, occurs_answer ha⟩ he' ha'
  have hm' : e' ∈ as := by
    rcases List.mem_append.1 hm with h1 | h1
    · exact h1
    · exact absurd (List.mem_singleton.1 h1).symm hne
  exact h ⟨as, e, bs, c, rfl, has, ha, e', hm', occurs_answer ha'⟩

end Events

/-! ## Part 3. The extractor -/

section FirstPre

variable {E Q D : Type} [DecidableEq D]

/-- The input of the event e, if e is, in the given view, a query with the answer c. -/
def hit (view : E → Option (Q × D)) (c : D) (e : E) : Option Q :=
  (view e).bind fun qa => if qa.2 = c then some qa.1 else none

/-- The first query with the answer c. A view says which events are queries to the oracle in
question, and with which input and answer. -/
def firstPre (view : E → Option (Q × D)) (tr : List E) (c : D) : Option Q :=
  tr.findSome? (hit view c)

variable {view : E → Option (Q × D)}

theorem hit_eq_some_iff {c : D} {e : E} {q : Q} : hit view c e = some q ↔ view e = some (q, c) := by
  unfold hit
  cases view e with
  | none => simp
  | some qa =>
    obtain ⟨q', c'⟩ := qa
    by_cases hc : c' = c
    · subst hc; simp
    · simp [hc]

theorem exists_of_firstPre {tr : List E} {c : D} {q : Q} (h : firstPre view tr c = some q) :
    ∃ e ∈ tr, view e = some (q, c) := by
  obtain ⟨e, he, hh⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨e, he, hit_eq_some_iff.1 hh⟩

theorem firstPre_eq_none_iff {tr : List E} {c : D} :
    firstPre view tr c = none ↔ ∀ e ∈ tr, ∀ q, view e ≠ some (q, c) := by
  rw [firstPre, List.findSome?_eq_none_iff]
  constructor
  · intro h e he q hq
    have := h e he
    rw [hit_eq_some_iff.2 hq] at this
    exact Option.some_ne_none _ this
  · intro h e he
    by_contra hn
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hn
    exact h e he q (hit_eq_some_iff.1 hq)

theorem firstPre_append (tr tr' : List E) (c : D) :
    firstPre view (tr ++ tr') c = (firstPre view tr c).or (firstPre view tr' c) := by
  simp only [firstPre, List.findSome?_append]

/-- What has been found stays found when the trace is extended. -/
theorem firstPre_mono {tr' tr : List E} (hp : tr' <+: tr) {c : D}
    {q : Q} (h : firstPre view tr' c = some q) :
    firstPre view tr c = some q := by
  obtain ⟨suf, rfl⟩ := hp
  rw [firstPre_append, h, Option.some_or]

variable {Ev : Events E D}

/-- Under `hview` (the queries of the view are Merkle queries in the sense of Ev, with the same
answers), outside the hash event, any query of the trace with the answer c is the first one. -/
theorem firstPre_eq_of_mem (hview : ∀ e q c, view e = some (q, c) → Ev.answer e = some c)
    {tr : List E} (h : ¬ Ev.HashEvent tr) {e : E} {q : Q} {c : D} (he : e ∈ tr)
    (hq : view e = some (q, c)) :
    firstPre view tr c = some q := by
  cases hf : firstPre view tr c with
  | none => exact absurd hq (firstPre_eq_none_iff.1 hf e he q)
  | some q' =>
    obtain ⟨e', he', hq'⟩ := exists_of_firstPre hf
    obtain rfl := Events.eq_of_answer_eq h he he' (hview _ _ _ hq) (hview _ _ _ hq')
    rw [hq] at hq'
    rw [(Prod.mk.inj (Option.some.inj hq')).1]

/-- Under `hview`, outside the hash event, once c occurs in a prefix, the prefix and the whole trace
have the same first query with the answer c, or both have none. -/
theorem firstPre_stable (hview : ∀ e q c, view e = some (q, c) → Ev.answer e = some c)
    {tr' tr : List E} (h : ¬ Ev.HashEvent tr) (hp : tr' <+: tr) {c : D} (ho : Ev.OccursIn tr' c) :
    firstPre view tr' c = firstPre view tr c := by
  cases hf : firstPre view tr' c with
  | some q => exact (firstPre_mono hp hf).symm
  | none =>
    cases hf' : firstPre view tr c with
    | none => rfl
    | some q =>
      obtain ⟨e, he, hq⟩ := exists_of_firstPre hf'
      exact absurd hq
        (firstPre_eq_none_iff.1 hf e (Events.mem_prefix_of_answer h hp ho he (hview _ _ _ hq)) q)

end FirstPre

/-- A pair of Merkle oracles in a trace: which events are queries to the leaf oracle and which to
the node oracle of the pair, with input and answer. Both kinds are Merkle queries in the sense of
Ev, and both halves of the input of a node query occur at it. Several pairs may share one Ev. -/
structure OraclePair {E D : Type} (Ev : Events E D) (X : Type) where
  /-- input and answer, if the event is a query to the leaf oracle -/
  leaf : E → Option (X × D)
  /-- input and answer, if the event is a query to the node oracle -/
  node : E → Option ((D × D) × D)
  answer_of_leaf : ∀ (e : E) (x : X) (c : D), leaf e = some (x, c) → Ev.answer e = some c
  answer_of_node : ∀ (e : E) (q : D × D) (c : D), node e = some (q, c) → Ev.answer e = some c
  occurs_left : ∀ (e : E) (q : D × D) (c : D), node e = some (q, c) → Ev.Occurs e q.1
  occurs_right : ∀ (e : E) (q : D × D) (c : D), node e = some (q, c) → Ev.Occurs e q.2

namespace OraclePair

variable {E D X : Type} {Ev : Events E D} (V : OraclePair Ev X)

section Defs

variable [DecidableEq D]

/-- The extractor, before decoding: it returns leaf inputs, and nothing in this file decodes them.
Vertices are labelled from the root downwards. The root has the label c.
If an inner vertex has a label and the trace has a query to the node oracle with
that answer, the two halves of the first such query are the labels of its children; otherwise
nothing below it has a label. The result at the leaf p is the input of the first query to the leaf
oracle whose answer is the label of p, if p has a label and there is such a query. -/
def preimage (tr : List E) : {t : Shape} → t.Pos → D → Option X
  | _, .here, c => firstPre V.leaf tr c
  | _, .left p, c => (firstPre V.node tr c).bind fun q => preimage tr p q.1
  | _, .right p, c => (firstPre V.node tr c).bind fun q => preimage tr p q.2

/-- The label of the leaf p in the labelling of the extractor (preimage), if it gets one. -/
def leafLabel (tr : List E) : {t : Shape} → t.Pos → D → Option D
  | _, .here, c => some c
  | _, .left p, c => (firstPre V.node tr c).bind fun q => leafLabel tr p q.1
  | _, .right p, c => (firstPre V.node tr c).bind fun q => leafLabel tr p q.2

theorem preimage_eq_bind_leafLabel (tr : List E) : ∀ {t : Shape} (p : t.Pos) (c : D),
    V.preimage tr p c = (V.leafLabel tr p c).bind (firstPre V.leaf tr)
  | _, .here, _ => rfl
  | _, .left p, c => by
      simp only [preimage, leafLabel, Option.bind_assoc, preimage_eq_bind_leafLabel tr p]
  | _, .right p, c => by
      simp only [preimage, leafLabel, Option.bind_assoc, preimage_eq_bind_leafLabel tr p]

end Defs

/-- The leaf input x opens the position p under the digest c within the trace: there are siblings
with which the check (the usual verification of a Merkle path; not defined in this file; one such
check: `runCheck`, Compile/Batch/Verifier.lean) accepts, and all
queries of that check are events of the trace, with the answers that the check uses. -/
def OpensIn (tr : List E) : {t : Shape} → t.Pos → X → D → Prop
  | _, .here, x, c => ∃ e ∈ tr, V.leaf e = some (x, c)
  | _, .left p, x, c => ∃ q : D × D, (∃ e ∈ tr, V.node e = some (q, c)) ∧ OpensIn tr p x q.1
  | _, .right p, x, c => ∃ q : D × D, (∃ e ∈ tr, V.node e = some (q, c)) ∧ OpensIn tr p x q.2

theorem OpensIn.mono {tr tr' : List E} (hs : tr ⊆ tr') : ∀ {t : Shape} {p : t.Pos} {x : X} {c : D},
    V.OpensIn tr p x c → V.OpensIn tr' p x c
  | _, .here, _, _, h => by
      obtain ⟨e, he, h⟩ := h
      exact ⟨e, hs he, h⟩
  | _, .left _, _, _, h => by
      obtain ⟨q, ⟨e, he, h⟩, ho⟩ := h
      exact ⟨q, ⟨e, hs he, h⟩, OpensIn.mono hs ho⟩
  | _, .right _, _, _, h => by
      obtain ⟨q, ⟨e, he, h⟩, ho⟩ := h
      exact ⟨q, ⟨e, hs he, h⟩, OpensIn.mono hs ho⟩

end OraclePair

/-! ## Part 4. Under the hypotheses below: extraction is stable; openings agree with extraction -/

namespace OraclePair

variable {E D X : Type} {Ev : Events E D} (V : OraclePair Ev X) [DecidableEq D]

/-- What the extractor finds at a leaf opens that leaf within the trace. No assumption on the
trace. -/
theorem opensIn_of_preimage {tr : List E} : ∀ {t : Shape} {p : t.Pos} {c : D} {x : X},
    V.preimage tr p c = some x → V.OpensIn tr p x c
  | _, .here, _, _, h => exists_of_firstPre h
  | _, .left _, _, _, h => by
      obtain ⟨q, hq, hx⟩ := Option.bind_eq_some_iff.1 h
      exact ⟨q, exists_of_firstPre hq, opensIn_of_preimage hx⟩
  | _, .right _, _, _, h => by
      obtain ⟨q, hq, hx⟩ := Option.bind_eq_some_iff.1 h
      exact ⟨q, exists_of_firstPre hq, opensIn_of_preimage hx⟩

/-- Extraction only grows. What the extractor finds at a leaf in a prefix of a trace, it finds in
the whole trace. No assumption on the trace. -/
theorem preimage_mono {tr' tr : List E} (hp : tr' <+: tr) :
    ∀ {t : Shape} {p : t.Pos} {c : D} {x : X},
      V.preimage tr' p c = some x → V.preimage tr p c = some x
  | _, .here, _, _, h => firstPre_mono hp h
  | _, .left _, _, _, h => by
      obtain ⟨q, hq, hx⟩ := Option.bind_eq_some_iff.1 h
      exact Option.bind_eq_some_iff.2 ⟨q, firstPre_mono hp hq, preimage_mono hp hx⟩
  | _, .right _, _, _, h => by
      obtain ⟨q, hq, hx⟩ := Option.bind_eq_some_iff.1 h
      exact Option.bind_eq_some_iff.2 ⟨q, firstPre_mono hp hq, preimage_mono hp hx⟩

/-- Extraction is stable (for leaf inputs). Outside the hash event, for every digest c and every
prefix of the trace in which c occurs, the extractor finds under c the same in the prefix as in the
whole trace: the same leaves have a value, and the values are the same. -/
theorem preimage_stable {tr' tr : List E} (h : ¬ Ev.HashEvent tr) (hp : tr' <+: tr) :
    ∀ {t : Shape} (p : t.Pos) {c : D}, Ev.OccursIn tr' c → V.preimage tr' p c = V.preimage tr p c
  | _, .here, _, ho => firstPre_stable V.answer_of_leaf h hp ho
  | _, .left p, c, ho => by
      simp only [preimage, ← firstPre_stable V.answer_of_node h hp ho]
      cases hf : firstPre V.node tr' c with
      | none => rfl
      | some q =>
        obtain ⟨e, he, hq⟩ := exists_of_firstPre hf
        exact preimage_stable h hp p ⟨e, he, V.occurs_left e q c hq⟩
  | _, .right p, c, ho => by
      simp only [preimage, ← firstPre_stable V.answer_of_node h hp ho]
      cases hf : firstPre V.node tr' c with
      | none => rfl
      | some q =>
        obtain ⟨e, he, hq⟩ := exists_of_firstPre hf
        exact preimage_stable h hp p ⟨e, he, V.occurs_right e q c hq⟩

/-- `preimage_stable` for the labels of the leaves. -/
theorem leafLabel_stable {tr' tr : List E} (h : ¬ Ev.HashEvent tr) (hp : tr' <+: tr) :
    ∀ {t : Shape} (p : t.Pos) {c : D}, Ev.OccursIn tr' c → V.leafLabel tr' p c = V.leafLabel tr p c
  | _, .here, _, _ => rfl
  | _, .left p, c, ho => by
      simp only [leafLabel, ← firstPre_stable V.answer_of_node h hp ho]
      cases hf : firstPre V.node tr' c with
      | none => rfl
      | some q =>
        obtain ⟨e, he, hq⟩ := exists_of_firstPre hf
        exact leafLabel_stable h hp p ⟨e, he, V.occurs_left e q c hq⟩
  | _, .right p, c, ho => by
      simp only [leafLabel, ← firstPre_stable V.answer_of_node h hp ho]
      cases hf : firstPre V.node tr' c with
      | none => rfl
      | some q =>
        obtain ⟨e, he, hq⟩ := exists_of_firstPre hf
        exact leafLabel_stable h hp p ⟨e, he, V.occurs_right e q c hq⟩

/-- Every label of a leaf in the labelling of the extractor (preimage) occurs in the trace, if the
label of the root does. -/
theorem occursIn_of_leafLabel {tr : List E} : ∀ {t : Shape} (p : t.Pos) {c c' : D},
    Ev.OccursIn tr c → V.leafLabel tr p c = some c' → Ev.OccursIn tr c'
  | _, .here, _, _, ho, h => by cases Option.some.inj h; exact ho
  | _, .left p, _, _, _, h => by
      obtain ⟨q, hq, hx⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨e, he, hq'⟩ := exists_of_firstPre hq
      exact occursIn_of_leafLabel p ⟨e, he, V.occurs_left e q _ hq'⟩ hx
  | _, .right p, _, _, _, h => by
      obtain ⟨q, hq, hx⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨e, he, hq'⟩ := exists_of_firstPre hq
      exact occursIn_of_leafLabel p ⟨e, he, V.occurs_right e q _ hq'⟩ hx

/-- Openings agree with extraction (for leaf inputs). Outside the hash event, if x opens the
position p under c within the trace, the extractor finds x at p under c. -/
theorem preimage_of_opensIn {tr : List E} (h : ¬ Ev.HashEvent tr) :
    ∀ {t : Shape} {p : t.Pos} {x : X} {c : D}, V.OpensIn tr p x c → V.preimage tr p c = some x
  | _, .here, _, _, ho => by
      obtain ⟨e, he, hq⟩ := ho
      exact firstPre_eq_of_mem V.answer_of_leaf h he hq
  | _, .left _, _, _, ho => by
      obtain ⟨q, ⟨e, he, hq⟩, ho'⟩ := ho
      exact Option.bind_eq_some_iff.2
        ⟨q, firstPre_eq_of_mem V.answer_of_node h he hq, preimage_of_opensIn h ho'⟩
  | _, .right _, _, _, ho => by
      obtain ⟨q, ⟨e, he, hq⟩, ho'⟩ := ho
      exact Option.bind_eq_some_iff.2
        ⟨q, firstPre_eq_of_mem V.answer_of_node h he hq, preimage_of_opensIn h ho'⟩

/-- Outside the hash event, "the extractor finds x" and "x opens within the trace" are the same. -/
theorem preimage_eq_some_iff
    {tr : List E} (h : ¬ Ev.HashEvent tr) {t : Shape} {p : t.Pos} {x : X} {c : D} :
    V.preimage tr p c = some x ↔ V.OpensIn tr p x c :=
  ⟨V.opensIn_of_preimage, V.preimage_of_opensIn h⟩

/-- Binding within a trace. Two leaf inputs that open one position under one digest within a trace
are equal, or the hash event has happened. -/
theorem eq_of_opensIn {tr : List E} (h : ¬ Ev.HashEvent tr) {t : Shape} {p : t.Pos} {x x' : X}
    {c : D} (ho : V.OpensIn tr p x c) (ho' : V.OpensIn tr p x' c) : x = x' :=
  Option.some.inj ((V.preimage_of_opensIn h ho).symm.trans (V.preimage_of_opensIn h ho'))

end OraclePair

end Merkle
