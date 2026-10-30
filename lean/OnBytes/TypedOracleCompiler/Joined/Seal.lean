-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Seal.lean: what a seal binds.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The chains of one file are joined by seals: the value in which one chain ends is a field of the
first query of the next. In the compiled scheme with batches
(OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean) such a value is a link value: the tail of the answer of a
Fiat-Shamir query, or the answer of the query to g (the slot value). The first chain's seal is the
slot value; it enters the request tree, whose root stands in the first query (F4) of the shared
chain. The shared chain's seal is the link value of its
last query; the first query (F3) of the last chain holds it, and the slot value beside it.

This file says what soundness gets from that: outside the two hash events `EF` and `EM`
(OnBytes/TypedOracleCompiler/Compile/Batch/Events.lean) a seal names all queries of the chain that it closes. No
new event and no new term of the bound comes in: both events are counted in `hashEvents`
(OnBytes/TypedOracleCompiler/Compile/Batch/Hash.lean: for an algorithm with at most t queries, probability at most
2 t² / 2^lam).

Main names:
  `link_names`, `slot_names`: outside `EF` two queries of the trace with the same link value, or two
    queries to g with the same answer, are the same query.
  `link_ne_slot`: outside `EF` no link value of a Fiat-Shamir query is an answer of g.
  `Leads t tr q₀ l v`: l is a chain of Fiat-Shamir queries of the trace, the newest first, from its
    oldest query q₀ to the link value v; each query but q₀ holds the link value of the one before as
    its one chain field.
  `Leads.unique`: outside `EF` the link value v names q₀ and l.
  `slot_of_root`: outside `EM` a request root and a leaf's number name the slot value.
  `Three`, `Three.unique`: three chains joined by the two seals: the last link value names all
    three, and the query to g.
  `Three.unique_shared`: the shared chain's seal and the slot's number name the first two.

Limits: statements on one trace; nothing on probability here. `Leads` does not ask that a query is
well formed, nor that rounds are numbered in order. A seal does not name the salt of the slot, which
stands behind the slot value in the input of the request tree's leaf: the view of that leaf is the
slot value alone. Nothing is said of roots or openings of trees over prover messages.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Rooted

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile (Tag posOf)
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## One seal -/

/-- Outside `EF` a link value names its Fiat-Shamir query. -/
theorem link_names {tr : Trace (typedOracleFamily lam K L)} (hF : ¬ EF tr) {t : Tag} {q q' : FbIn lam L t}
    {a a' : FsAns lam K} (h : fbE t q a ∈ tr) (h' : fbE t q' a' ∈ tr) (e : link a = link a') :
    q = q' ∧ a = a' :=
  fbE_inj (Merkle.Events.eq_of_answer_eq hF h h' (evF_answer_fbE t q a)
    (by rw [e]; exact evF_answer_fbE t q' a'))

/-- Outside `EF` a slot value names its query to g. -/
theorem slot_names {tr : Trace (typedOracleFamily lam K L)} (hF : ¬ EF tr) {t : Tag} {q q' : JoiningRoundQuery lam L t}
    {c : Dig lam} (h : gE t q c ∈ tr) (h' : gE t q' c ∈ tr) : q = q' :=
  (gE_inj (Merkle.Events.eq_of_answer_eq hF h h' (evF_answer_gE t q c)
    (evF_answer_gE t q' c))).1

/-- Outside `EF` no link value of a Fiat-Shamir query is an answer of g. -/
theorem link_ne_slot {tr : Trace (typedOracleFamily lam K L)} (hF : ¬ EF tr) {t t' : Tag} {q : FbIn lam L t}
    {a : FsAns lam K} {q' : JoiningRoundQuery lam L t'} {c : Dig lam} (h : fbE t q a ∈ tr)
    (h' : gE t' q' c ∈ tr) : link a ≠ List.ofFn c := fun e => by
  have h1 := Merkle.Events.eq_of_answer_eq hF h h' (evF_answer_fbE t q a)
    (by rw [e]; exact evF_answer_gE t' q' c)
  cases (Sigma.mk.inj h1).1

/-! ## One chain -/

/-- A chain of Fiat-Shamir queries of the trace, the newest first, from its oldest query q₀ to the
link value v. Each query but q₀ holds the link value of the one before as its one chain field. -/
inductive Leads (t : Tag) (tr : Trace (typedOracleFamily lam K L)) (q₀ : FbIn lam L t) :
    List (FbIn lam L t × FsAns lam K) → Bits → Prop
  | first {a : FsAns lam K} {v : Bits} (h : fbE t q₀ a ∈ tr) (hv : link a = v) :
      Leads t tr q₀ [(q₀, a)] v
  | next {l : List (FbIn lam L t × FsAns lam K)} {u v : Bits} {q : FbIn lam L t}
      {a : FsAns lam K} (hl : Leads t tr q₀ l u) (h : fbE t q a ∈ tr) (hc : chainFields q = [u])
      (hv : link a = v) : Leads t tr q₀ ((q, a) :: l) v

/-- every query of the chain is an entry of the trace -/
theorem Leads.mem {t : Tag} {tr : Trace (typedOracleFamily lam K L)} {q₀ : FbIn lam L t}
    {l : List (FbIn lam L t × FsAns lam K)} {v : Bits} (h : Leads t tr q₀ l v) :
    ∀ p ∈ l, fbE t p.1 p.2 ∈ tr := by
  induction h with
  | first h _ => intro p hp; cases List.mem_singleton.1 hp; exact h
  | next _ h _ _ ih =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h
    · exact ih p hp

/-- Outside `EF` a link value names the chain that ends in it, if the oldest query is known as such:
it does not hold exactly one chain field. So it is with (F1) and (F4), which hold none, and with
(F3), which holds two. -/
theorem Leads.unique {t : Tag} {tr : Trace (typedOracleFamily lam K L)} (hF : ¬ EF tr) {q₀ q₀' : FbIn lam L t}
    (h0 : (chainFields q₀).length ≠ 1) (h0' : (chainFields q₀').length ≠ 1)
    {l : List (FbIn lam L t × FsAns lam K)} {v : Bits} (h : Leads t tr q₀ l v) :
    ∀ {l' : List (FbIn lam L t × FsAns lam K)}, Leads t tr q₀' l' v → q₀ = q₀' ∧ l = l' := by
  induction h with
  | first h hv =>
    intro l' h'
    cases h' with
    | first h2 hv2 =>
      obtain ⟨rfl, rfl⟩ := link_names hF h h2 (hv.trans hv2.symm)
      exact ⟨rfl, rfl⟩
    | next _ h2 hc2 hv2 =>
      obtain ⟨rfl, rfl⟩ := link_names hF h h2 (hv.trans hv2.symm)
      exact absurd (by rw [hc2]; rfl) h0
  | next _ h hc hv ih =>
    intro l' h'
    cases h' with
    | first h2 hv2 =>
      obtain ⟨rfl, rfl⟩ := link_names hF h h2 (hv.trans hv2.symm)
      exact absurd (by rw [hc]; rfl) h0'
    | next hl2 h2 hc2 hv2 =>
      obtain ⟨rfl, rfl⟩ := link_names hF h h2 (hv.trans hv2.symm)
      obtain rfl := (List.cons.inj (hc.symm.trans hc2)).1
      obtain ⟨e1, e2⟩ := ih hl2
      exact ⟨e1, by rw [e2]⟩

/-! ## The request tree -/

/-- Outside `EM` a request root and the number of a leaf name the slot value: the first lam bits of
the input of that leaf's query. -/
theorem slot_of_root {tr : Trace (typedOracleFamily lam K L)} (hM : ¬ EM tr) {d j : ℕ} {rt : Dig lam}
    {c c' : Bits} (h : (pairR lam K L).OpensIn tr (posOf d j) c rt)
    (h' : (pairR lam K L).OpensIn tr (posOf d j) c' rt) : c = c' :=
  (pairR lam K L).eq_of_opensIn hM h h'

/-! ## Three chains -/

/-- Three chains of one trace, joined by two seals. The first chain l₁ ends in the chain field of
the query qg to g, whose answer c is the slot value (the first seal). The slot value stands at
leaf j of the request tree of depth d under the root in the oldest query (F4) of the shared chain
l₂. That chain ends in ρ0 (the second seal). The oldest query (F3) of the last chain l₃ holds ρ0
and c; l₃ ends in v. -/
structure Three (t : Tag) (tr : Trace (typedOracleFamily lam K L)) (d j : ℕ) (q₁ : FbIn lam L t)
    (l₁ : List (FbIn lam L t × FsAns lam K)) (qg : JoiningRoundQuery lam L t) (c : Dig lam) (q₂ : FbIn lam L t)
    (l₂ : List (FbIn lam L t × FsAns lam K)) (ρ0 : Bits) (q₃ : FbIn lam L t)
    (l₃ : List (FbIn lam L t × FsAns lam K)) (v : Bits) : Prop where
  /-- the oldest query of the first chain holds no chain field -/
  start₁ : chainFields q₁ = []
  one : Leads t tr q₁ l₁ qg.ρ
  seal₁ : gE t qg c ∈ tr
  /-- the oldest query of the shared chain is (F4), with a request root of lam bits -/
  start₂ : ∃ cms rt, q₂.head = .f4 cms (List.ofFn rt) ∧
    (pairR lam K L).OpensIn tr (posOf d j) (List.ofFn c) rt
  two : Leads t tr q₂ l₂ ρ0
  /-- the oldest query of the last chain is (F3): it holds both seals -/
  start₃ : q₃.head = .f3 ρ0 (List.ofFn c)
  three : Leads t tr q₃ l₃ v

theorem chainFields_f4 {t : Tag} {q : FbIn lam L t} {cms : List (Dig lam)} {r : Bits}
    (h : q.head = .f4 cms r) : chainFields q = [] := by
  unfold chainFields; rw [h]

theorem chainFields_f3 {t : Tag} {q : FbIn lam L t} {ρ0 c : Bits} (h : q.head = .f3 ρ0 c) :
    chainFields q = [ρ0, c] := by
  unfold chainFields; rw [h]

/-- Outside `EF` the shared chain's seal ρ0 and, outside `EM`, the slot's number name the shared
chain, the slot value, the query to g and the first chain. -/
theorem Three.unique_shared {t : Tag} {tr : Trace (typedOracleFamily lam K L)} (hM : ¬ EM tr) (hF : ¬ EF tr)
    {d j : ℕ} {q₁ q₁' q₂ q₂' q₃ q₃' : FbIn lam L t}
    {l₁ l₁' l₂ l₂' l₃ l₃' : List (FbIn lam L t × FsAns lam K)} {qg qg' : JoiningRoundQuery lam L t}
    {c c' : Dig lam} {ρ0 v v' : Bits} (h : Three t tr d j q₁ l₁ qg c q₂ l₂ ρ0 q₃ l₃ v)
    (h' : Three t tr d j q₁' l₁' qg' c' q₂' l₂' ρ0 q₃' l₃' v') :
    q₂ = q₂' ∧ l₂ = l₂' ∧ c = c' ∧ qg = qg' ∧ q₁ = q₁' ∧ l₁ = l₁' := by
  obtain ⟨cms, rt, e, ho⟩ := h.start₂
  obtain ⟨cms', rt', e', ho'⟩ := h'.start₂
  obtain ⟨rfl, rfl⟩ := Leads.unique hF (by rw [chainFields_f4 e]; decide)
    (by rw [chainFields_f4 e']; decide) h.two h'.two
  have e2 : rt = rt' := by
    have h3 := e.symm.trans e'
    injection h3 with _ h4
    exact List.ofFn_injective h4
  subst e2
  obtain rfl : c = c' := List.ofFn_injective (slot_of_root hM ho ho')
  obtain rfl := slot_names hF h.seal₁ h'.seal₁
  obtain ⟨rfl, rfl⟩ := Leads.unique hF (by rw [h.start₁]; decide) (by rw [h'.start₁]; decide)
    h.one h'.one
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Outside `EF` the link value in which the last chain ends names all three chains, both seals and
the query to g. -/
theorem Three.unique {t : Tag} {tr : Trace (typedOracleFamily lam K L)} (hF : ¬ EF tr) {d j d' j' : ℕ}
    {q₁ q₁' q₂ q₂' q₃ q₃' : FbIn lam L t}
    {l₁ l₁' l₂ l₂' l₃ l₃' : List (FbIn lam L t × FsAns lam K)} {qg qg' : JoiningRoundQuery lam L t}
    {c c' : Dig lam} {ρ0 ρ0' v : Bits} (h : Three t tr d j q₁ l₁ qg c q₂ l₂ ρ0 q₃ l₃ v)
    (h' : Three t tr d' j' q₁' l₁' qg' c' q₂' l₂' ρ0' q₃' l₃' v) :
    q₃ = q₃' ∧ l₃ = l₃' ∧ ρ0 = ρ0' ∧ q₂ = q₂' ∧ l₂ = l₂' ∧ c = c' ∧ qg = qg' ∧ q₁ = q₁' ∧
      l₁ = l₁' := by
  obtain ⟨rfl, rfl⟩ := Leads.unique hF (by rw [chainFields_f3 h.start₃]; simp)
    (by rw [chainFields_f3 h'.start₃]; simp) h.three h'.three
  have h3 := h.start₃.symm.trans h'.start₃
  injection h3 with h4 h5
  subst h4
  obtain rfl : c = c' := List.ofFn_injective h5
  obtain ⟨cms, rt, e, -⟩ := h.start₂
  obtain ⟨cms', rt', e', -⟩ := h'.start₂
  obtain ⟨rfl, rfl⟩ := Leads.unique hF (by rw [chainFields_f4 e]; decide)
    (by rw [chainFields_f4 e']; decide) h.two h'.two
  obtain rfl := slot_names hF h.seal₁ h'.seal₁
  obtain ⟨rfl, rfl⟩ := Leads.unique hF (by rw [h.start₁]; decide) (by rw [h'.start₁]; decide)
    h.one h'.one
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end TypedOracleCompiler.Joined
