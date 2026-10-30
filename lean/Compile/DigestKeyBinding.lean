-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DigestKeyBinding.lean: index binding passes from a scheme A to the scheme `A.digestKey enc`
(ZKCP/DigestKey.lean), in which the verifier's key is the digest of A's, if the coding `enc` is one
to one, at the price of (tC + tP + 2)² / 2^λ. tC, tP, λ, ε: see the head of
Compile/DigestKeyArg.lean.

  `HasIndexBindingWith.digestKey`   if A has index binding with the extractor E and the bound ε,
        and the coding of keys is one to one, then `A.digestKey enc` has index binding with the
        extractor `E.digestKey enc` and the bound ε tC tP + (tC + tP + 2)² / 2^λ
  `HasIndexBindingWith.of_verifyDigestKey`   the same for every scheme with that verifier, given
        some key of A: index binding reads no other part of a scheme
  `Pr_two_keys_one_digest_le`   if the coding is one to one, an algorithm with at most t queries
        outputs two different keys that both have codes and have the same digest with probability
        at most (t + 2)² / 2^λ
  `Pr_two_verifiers_one_digest_le`   the same bound for one digest with, for each of two
        verifiers, an instance and a proof that it accepts, where the two proofs bring keys with
        different codes
  `AnswerRepeats`, `Pr_answerRepeats_le`   the event that is counted, and a bound on its probability

How. Below, "new" is said of `A.digestKey enc` and "old" of A. Fix the hash function. If the new
verifier accepts a key k and a proof under the digest d, then either k is `firstKey` of d and the
committer's query log, and the old game (`bindingExp`, ZKCP/Defs.lean), played by the committer that
looks k up in its own log, ends as the new one does; or the event `AnswerRepeats` has happened in
the log of these steps: the committer; one query at d written as a bit string; the prover; the query
at the code of k. The event: an entry that is not among the earlier ones has as its answer a digest
that is the answer of an earlier entry, or that an earlier query spells, or that its own query
spells. After n entries it has probability at most (2 n + 1) / 2^λ (`pr_repeatsAt_le`);
`pr_stepEvent_le` (Rom/OneCount.lean) adds these up to t² / 2^λ. The query at the spelling of d is
made in this analysis alone; `A.digestKey enc` adds no such query.

The strings that `enc` gives need not differ from the strings that A's verifier queries: the
adversary in the new game and the one in the old game may query any string. The bound is not tight.
Limits: Compile/DigestKeyArg.lean.
-/
import ZKCP.DigestKey
import ZKCP.HonestKey
import Rom.Bridge
import Rom.OneCount
import Compile.HashEvents

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ}

/-! ## 1. The event at a query -/

namespace DigestKey

section Step
open Rom Prob

/-- A digest written as a bit string. -/
def spelling (d : Digest lam) : Str := List.ofFn d

theorem spelling_injective : Function.Injective (spelling (lam := lam)) := List.ofFn_injective

/-- The query of a log entry. -/
def queryOf (e : QA (rom lam)) : Str := e.2.1

/-- The answer of a log entry. -/
def answerOf (e : QA (rom lam)) : Digest lam := e.2.2

/-- The event at one entry e that comes after the entries `pre`: e is not among them, and its answer
is spelled by its own query, or is the answer of an earlier entry, or is spelled by an earlier
query. -/
def RepeatsAt (pre : Rom.Trace (rom lam)) (e : QA (rom lam)) : Prop :=
  e ∉ pre ∧ (queryOf e = spelling (answerOf e) ∨
    ∃ e' ∈ pre, answerOf e' = answerOf e ∨ queryOf e' = spelling (answerOf e))

theorem pr_repeatsAt_le (pre : Rom.Trace (rom lam)) (o : (rom lam).ι) (q : (rom lam).Dom o) :
    pr (unif ((rom lam).Rng o)) {r | RepeatsAt pre ⟨o, q, r⟩}
      ≤ ((2 * pre.length + 1 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  have hc : (Fintype.card (Digest lam) : ℝ≥0∞) = 2 ^ lam := by simp
  have h1 := Compile.pr_unif_mem_le (C := Digest lam) spelling spelling_injective [(q : Str)]
  have h2 := Compile.pr_unif_mem_le (C := Digest lam) id Function.injective_id (pre.map answerOf)
  have h3 := Compile.pr_unif_mem_le (C := Digest lam) spelling spelling_injective (pre.map queryOf)
  rw [hc] at h1 h2 h3
  rw [List.length_map] at h2 h3
  have hsub : {r : Digest lam | RepeatsAt pre ⟨o, q, r⟩} ⊆ {c | spelling c ∈ [(q : Str)]} ∪
      ({c | id c ∈ pre.map answerOf} ∪ {c | spelling c ∈ pre.map queryOf}) := by
    rintro r ⟨-, h | ⟨e', he', h | h⟩⟩
    · exact Or.inl (List.mem_singleton.2 h.symm)
    · exact Or.inr (Or.inl (List.mem_map.2 ⟨e', he', h⟩))
    · exact Or.inr (Or.inr (List.mem_map.2 ⟨e', he', h⟩))
  refine le_trans (pr_mono _ hsub) (le_trans (pr_union_le _ _ _)
    (le_trans (add_le_add h1 (le_trans (pr_union_le _ _ _) (add_le_add h2 h3))) (le_of_eq ?_)))
  rw [← ENNReal.add_div, ← ENNReal.add_div, List.length_singleton]
  congr 1
  push_cast
  ring

theorem sum_odd_eq_sq (t : ℕ) : ∑ v ∈ Finset.range t, (2 * v + 1) = t ^ 2 := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Two different entries of a log with the same answer: the event has happened. -/
theorem stepEvent_of_two {tr : Rom.Trace (rom lam)} {e1 e2 : QA (rom lam)} (h1 : e1 ∈ tr)
    (h2 : e2 ∈ tr) (hne : e1 ≠ e2) (ha : answerOf e1 = answerOf e2) :
    StepEvent RepeatsAt tr := by
  obtain ⟨as, bs, rfl, hn⟩ := List.eq_append_cons_of_mem h1
  by_cases h : e2 ∈ as
  · exact ⟨as, e1, bs, rfl, hn, Or.inr ⟨e2, h, Or.inl ha.symm⟩⟩
  · have h2' : e2 ∈ bs := by
      rcases List.mem_append.1 h2 with h3 | h3
      · exact absurd h3 h
      · rcases List.mem_cons.1 h3 with h4 | h4
        · exact absurd h4.symm hne
        · exact h4
    obtain ⟨as', bs', rfl, hn'⟩ := List.eq_append_cons_of_mem h2'
    refine ⟨as ++ e1 :: as', e2, bs', by simp, ?_, Or.inr ⟨e1, by simp, Or.inl ha⟩⟩
    simp only [List.mem_append, List.mem_cons, not_or]
    exact ⟨h, fun h5 => hne h5.symm, hn'⟩

/-- An entry e that is not in `trC` and comes after an entry a whose query spells the answer of e:
the event has happened. -/
theorem stepEvent_of_late {trC rest : Rom.Trace (rom lam)} {a e : QA (rom lam)} (he : e ∈ rest)
    (hn : e ∉ trC) (ha : queryOf a = spelling (answerOf e)) :
    StepEvent RepeatsAt (trC ++ a :: rest) := by
  by_cases hea : e = a
  · subst hea
    exact ⟨trC, e, rest, rfl, hn, Or.inl ha⟩
  · obtain ⟨as, bs, rfl, hn'⟩ := List.eq_append_cons_of_mem he
    refine ⟨trC ++ a :: as, e, bs, by simp, ?_, Or.inr ⟨a, by simp, Or.inr ha⟩⟩
    simp only [List.mem_append, List.mem_cons, not_or]
    exact ⟨hn, hea, hn'⟩

/-- A log entry of ZKCP/Defs.lean as one of Rom/OSpec.lean (`QA`). -/
def toQA (e : Str × Digest lam) : QA (rom lam) := ⟨(), e.1, e.2⟩

theorem toQA_injective : Function.Injective (toQA (lam := lam)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simpa [toQA] using h

theorem trTo_eq (tr : ZKCP.Trace lam) : trTo tr = tr.map toQA := rfl

end Step

end DigestKey

open DigestKey

/-- The event on a query log: at some entry that is not among the earlier ones the answer is a
digest that is the answer of an earlier entry, or that an earlier query spells, or that the entry's
own query spells. -/
def AnswerRepeats (log : Trace lam) : Prop := Rom.StepEvent RepeatsAt (Rom.trTo log)

/-- An algorithm with at most t queries causes the event with probability at most t² / 2^λ. -/
theorem Pr_answerRepeats_le {α : Type} (c : OComp lam α) (t : ℕ) (h : c.QueryBound t) :
    Pr c.withTrace (fun _ => {o | AnswerRepeats o.2}) ≤ ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  have e : Pr c.withTrace (fun _ => {o | AnswerRepeats o.2})
      = Rom.Pr (Rom.toRom c).withTrace (fun _ => {o | Rom.StepEvent RepeatsAt o.2}) := by
    have e1 := Rom.Pr_toRom c.withTrace (fun _ => {o : α × Trace lam | AnswerRepeats o.2})
    rw [Rom.toRom_withTrace, Rom.Pr_bind_pure] at e1
    rw [← e1]
    refine congrArg _ (funext fun _ => Set.ext fun o => ?_)
    show Rom.StepEvent RepeatsAt (Rom.trTo (Rom.trOf o.2)) ↔ Rom.StepEvent RepeatsAt o.2
    rw [Rom.trTo_trOf]
  rw [e, Rom.Pr_eq_law]
  refine le_trans (Rom.pr_stepEvent_le RepeatsAt (fun n => ((2 * n + 1 : ℕ) : ℝ≥0∞) / 2 ^ lam)
    (fun _ _ he hs => hs.1 he) (fun pre o q _ => pr_repeatsAt_le pre o q) _ t
    ((Rom.queryBound_toRom c t).2 h)) (le_of_eq ?_)
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, sum_odd_eq_sq]

theorem AnswerRepeats.append {log : Trace lam} (h : AnswerRepeats log) (more : Trace lam) :
    AnswerRepeats (log ++ more) := by
  unfold AnswerRepeats
  rw [trTo_eq, List.map_append]
  exact Rom.StepEvent.append h _

/-- Two different entries of a log with the same answer: the event has happened. -/
theorem answerRepeats_of_two {log : Trace lam} {e1 e2 : Str × Digest lam} (h1 : e1 ∈ log)
    (h2 : e2 ∈ log) (hne : e1 ≠ e2) (ha : e1.2 = e2.2) : AnswerRepeats log := by
  unfold AnswerRepeats
  rw [trTo_eq]
  exact stepEvent_of_two (List.mem_map_of_mem h1) (List.mem_map_of_mem h2)
    (fun h => hne (toQA_injective h)) ha

/-- The queries at two bit strings, one after the other. -/
def DigestKey.askTwo (p : Str × Str) : OComp lam Unit :=
  .query p.1 fun _ => .query p.2 fun _ => .pure ()

theorem DigestKey.queryBound_askTwo (p : Str × Str) : (askTwo (lam := lam) p).QueryBound 2 :=
  fun _ _ => trivial

/-- Under one hash function: the probability that an algorithm outputs two different bit strings
with the same hash value is at most the probability that the event happens in its query log followed
by the queries at these two strings. -/
theorem DigestKey.prob_two_strings_le (f : Oracle lam) (c : OComp lam (Str × Str)) :
    prob (c.run f) {p | p.1 ≠ p.2 ∧ f p.1 = f p.2}
      ≤ prob ((c.bind askTwo).withTrace.run f) {o | AnswerRepeats o.2} := by
  rw [OComp.withTrace_bind, run_bind, prob_bind, ← OComp.run_withTrace_fst f c, prob_map,
    prob_eq_expect]
  refine expect_mono _ fun o => ?_
  split
  · rename_i ho
    obtain ⟨hne, h3⟩ := ho
    show 1 ≤ prob (PMF.pure ((), o.2 ++ [(o.1.1, f o.1.1), (o.1.2, f o.1.2)]))
      {o | AnswerRepeats o.2}
    rw [prob_pure, if_pos]
    show AnswerRepeats (o.2 ++ [(o.1.1, f o.1.1), (o.1.2, f o.1.2)])
    exact answerRepeats_of_two (e1 := (o.1.1, f o.1.1)) (e2 := (o.1.2, f o.1.2)) (by simp)
      (by simp) (fun h => hne (congrArg Prod.fst h)) h3
  · exact zero_le _

/-! ## 2. The key as a digest -/

section Key
variable {I X X' W PP IVK IVK' ISK Pf Pf' : Type}

namespace DigestKey

/-- The query at a key's code, if it has one. -/
def askCode (enc : IVK → Option Str) (k : IVK) : OComp lam Unit :=
  match enc k with
  | some s => .query s fun _ => .pure ()
  | none => .pure ()

theorem queryBound_askCode (enc : IVK → Option Str) (k : IVK) :
    (askCode (lam := lam) enc k).QueryBound 1 := by
  unfold askCode
  cases enc k with
  | none => trivial
  | some s => exact fun _ => trivial

theorem askCode_of_some {enc : IVK → Option Str} {k : IVK} {s : Str} (hs : enc k = some s) :
    askCode (lam := lam) enc k = .query s fun _ => .pure () := by
  unfold askCode
  rw [hs]

/-- If the coding is one to one, a log has the code of k with the answer d, and k is not the first
key of d in it, then the event has happened in that log. -/
theorem answerRepeats_of_mem {enc : IVK → Option Str} (hinj : CodeIsOneToOne enc)
    {log : Trace lam} {d : Digest lam} {k : IVK} {s : Str} (hs : enc k = some s)
    (hm : (s, d) ∈ log) (hk : firstKey enc d log ≠ some k) : AnswerRepeats log := by
  cases hfk : firstKey enc d log with
  | none =>
    have h0 := List.findSome?_eq_none_iff.1 hfk (s, d) hm
    rw [if_pos rfl, keyOfCode_enc hinj hs] at h0
    cases h0
  | some k1 =>
    obtain ⟨e1, he1, hf1⟩ := List.exists_of_findSome?_eq_some hfk
    by_cases hd : e1.2 = d
    · rw [if_pos hd] at hf1
      have hne : e1 ≠ (s, d) := by
        rintro rfl
        rw [keyOfCode_enc hinj hs] at hf1
        exact hk (hfk.trans hf1.symm)
      exact answerRepeats_of_two he1 hm hne hd
    · rw [if_neg hd] at hf1
      cases hf1

/-- If the coding is one to one, the code of k has the answer d, and k is not the first key of d in
the log `trC`, then the event has happened in `trC`, a query at the spelling of d, `trP` and the
query at the code of k. -/
theorem answerRepeats_of_hit {enc : IVK → Option Str} (hinj : CodeIsOneToOne enc)
    (trC trP : Trace lam) (d r0 : Digest lam) {k : IVK} {s : Str} (hs : enc k = some s)
    (hk : firstKey enc d trC ≠ some k) :
    AnswerRepeats (trC ++ (spelling d, r0) :: (trP ++ [(s, d)])) := by
  by_cases hm : (s, d) ∈ trC
  · exact (answerRepeats_of_mem hinj hs hm hk).append _
  · unfold AnswerRepeats
    rw [trTo_eq, List.map_append, List.map_cons, List.map_append]
    exact stepEvent_of_late (e := toQA (s, d))
      (List.mem_append_right _ (List.mem_singleton.2 rfl))
      (fun h => hm ((List.mem_map_of_injective toQA_injective).1 h)) rfl

/-- A bound by a sum of two probabilities passes through a common first step. -/
theorem prob_run_bind_le_add {α β β₁ β₂ : Type} (f : Oracle lam) (c : OComp lam α)
    {g : α → OComp lam β} {g₁ : α → OComp lam β₁} {g₂ : α → OComp lam β₂}
    (E : Set β) (E₁ : Set β₁) (E₂ : Set β₂)
    (h : ∀ a, prob ((g a).run f) E ≤ prob ((g₁ a).run f) E₁ + prob ((g₂ a).run f) E₂) :
    prob ((c.bind g).run f) E ≤ prob ((c.bind g₁).run f) E₁ + prob ((c.bind g₂).run f) E₂ := by
  rw [run_bind, run_bind, run_bind, prob_bind, prob_bind, prob_bind, ← expect_add]
  exact expect_mono _ h

/-- The committer, the query at the spelling of its digest, the prover, and the query at the code of
the key that the prover brings, as one algorithm. -/
def committerProverAndKeyCodeQueryRun {St : Type} (enc : IVK → Option Str) (Ct : OComp lam (Digest lam × St))
    (Pt : St → OComp lam (X × (IVK × Pf))) : OComp lam Unit :=
  Ct.bind fun a => .query (spelling a.1) fun _ => (Pt a.2).bind fun b => askCode enc b.2.1

theorem queryBound_committerProverAndKeyCodeQueryRun {St : Type} (enc : IVK → Option Str) {Ct : OComp lam (Digest lam × St)}
    {Pt : St → OComp lam (X × (IVK × Pf))} {tC tP : ℕ} (hC : Ct.QueryBound tC)
    (hP : ∀ st, (Pt st).QueryBound tP) : (committerProverAndKeyCodeQueryRun enc Ct Pt).QueryBound (tC + tP + 2) := by
  have hg : ∀ a : Digest lam × St, (OComp.query (spelling a.1) fun _ =>
      (Pt a.2).bind fun b => askCode enc b.2.1 : OComp lam Unit).QueryBound (tP + 1 + 1) :=
    fun a _ => OComp.QueryBound.bind _ 1 (fun b => queryBound_askCode enc b.2.1) (Pt a.2) tP
      (hP a.2)
  exact OComp.QueryBound.mono _ _ _ (by omega) (OComp.QueryBound.bind _ (tP + 1 + 1) hg Ct tC hC)

theorem withTrace_joined {St : Type} (enc : IVK → Option Str) (Ct : OComp lam (Digest lam × St))
    (Pt : St → OComp lam (X × (IVK × Pf))) :
    (committerProverAndKeyCodeQueryRun enc Ct Pt).withTrace = Ct.withTrace.bind fun o => .query (spelling o.1.1) fun r =>
      (Pt o.1.2).withTrace.bind fun o' => (askCode enc o'.1.2.1).withTrace.bind fun c =>
        .pure ((), o.2 ++ (spelling o.1.1, r) :: (o'.2 ++ c.2)) := by
  unfold committerProverAndKeyCodeQueryRun
  rw [OComp.withTrace_bind]
  refine congrArg _ (funext fun o => ?_)
  show (OComp.query (spelling o.1.1) fun r =>
      (((Pt o.1.2).bind fun b => askCode enc b.2.1).withTrace.bind fun out =>
        .pure (out.1, (spelling o.1.1, r) :: out.2)).bind fun b => .pure (b.1, o.2 ++ b.2)) = _
  refine congrArg _ (funext fun r => ?_)
  rw [OComp.withTrace_bind]
  simp only [OComp.bind_bind]
  rfl

end DigestKey

/-- If A has index binding with the extractor E and the bound ε, and the coding is one to one, then
every scheme whose verifier is `verifyDigestKey A.V enc` has index binding with the extractor
`E.digestKey enc` and the bound ε tC tP + (tC + tP + 2)² / 2^λ. k0 is any key of A. It is used in
A's game where the committer's log holds no key of its digest. There an acceptance by the new
verifier is the counted event, so nothing depends on what A's game does at k0; whatever it does is
inside ε. -/
theorem HasIndexBindingWith.of_verifyDigestKey {R : IndexedRelation I X W PP}
    {A : Arg lam I X W IVK ISK Pf} {E : Extractor lam I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : HasIndexBindingWith R A E ε) {enc : IVK → Option Str} (hinj : CodeIsOneToOne enc)
    (k0 : IVK) {ISK' : Type} (A' : Arg lam I X W (Digest lam) ISK' (IVK × Pf))
    (hA' : A'.V = verifyDigestKey A.V enc) :
    HasIndexBindingWith R A' (E.digestKey enc)
      fun tC tP => ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  intro tC tP St Ct Pt hC hP
  refine le_trans (Pr_le_add _
      (bindingExp A E (Ct.withTrace.mapO fun o => ((firstKey enc o.1.1 o.2).getD k0, o.1.2))
        fun st => (Pt st).mapO fun o => (o.1, o.2.2))
      (committerProverAndKeyCodeQueryRun enc Ct Pt).withTrace _ (bindingBad R) {o | AnswerRepeats o.2} fun f => ?_)
    (add_le_add
      (h tC tP St _ _ (OComp.QueryBound.mapO _ _ tC (OComp.QueryBound.withTrace Ct tC hC))
        fun st => OComp.QueryBound.mapO _ _ tP (hP st))
      (Pr_answerRepeats_le _ _ (queryBound_committerProverAndKeyCodeQueryRun enc hC hP)))
  show prob ((Ct.withTrace.bind fun o => (Pt o.1.2).withTrace.bind fun o' =>
        (A'.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
        .pure (⟨b, (firstKey enc o.1.1 o.2).bind fun k => E.Ei k o.2, o'.1.1,
          E.Ew o'.1.2.1 o.2 o'.1.1 o'.1.2.2 o'.2⟩ : BindingOutcome I X W)).run f) (bindingBad R)
    ≤ prob (((Ct.withTrace.mapO fun o =>
          ((firstKey enc o.1.1 o.2).getD k0, o.1.2)).withTrace.bind fun o =>
        ((Pt o.1.2).mapO fun o => (o.1, o.2.2)).withTrace.bind fun o' =>
        (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
        .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
          E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)).run f) (bindingBad R)
      + prob ((committerProverAndKeyCodeQueryRun enc Ct Pt).withTrace.run f) {o | AnswerRepeats o.2}
  rw [OComp.withTrace_mapO, OComp.withTrace_withTrace, OComp.mapO_bind, OComp.mapO_bind,
    withTrace_joined, hA']
  refine prob_run_bind_le_add f _ _ _ _ fun o => ?_
  simp only [OComp.withTrace_mapO, OComp.mapO_bind]
  show _ ≤ _ + prob (((Pt o.1.2).withTrace.bind fun o' =>
      (askCode enc o'.1.2.1).withTrace.bind fun c =>
        .pure ((), o.2 ++ (spelling o.1.1, f (spelling o.1.1)) :: (o'.2 ++ c.2))).run f)
    {o | AnswerRepeats o.2}
  refine prob_run_bind_le_add f _ _ _ _ fun o' => ?_
  have zero : ∀ (i : Option I) (x : X) (w : W),
      prob (((OComp.pure false : OComp lam Bool).bind fun b =>
        .pure (⟨b, i, x, w⟩ : BindingOutcome I X W)).run f) (bindingBad R) = 0 := by
    intro i x w
    show prob (PMF.pure _) _ = 0
    rw [prob_pure, if_neg]
    rintro ⟨ha, -⟩
    exact Bool.noConfusion ha
  cases hs : enc o'.1.2.1 with
  | none =>
    rw [verifyDigestKey_of_none A.V o.1.1 o'.1.1 o'.1.2 hs, zero]
    exact zero_le _
  | some s =>
    have e : ∀ K : Bool → OComp lam (BindingOutcome I X W),
        ((verifyDigestKey A.V enc o.1.1 o'.1.1 o'.1.2).bind K).run f
          = ((if f s = o.1.1 then A.V o'.1.2.1 o'.1.1 o'.1.2.2 else .pure false).bind K).run f := by
      intro K
      unfold verifyDigestKey
      rw [hs]
      rfl
    rw [e]
    by_cases hd : f s = o.1.1
    · rw [if_pos hd]
      by_cases hk : firstKey enc o.1.1 o.2 = some o'.1.2.1
      · refine le_trans (le_of_eq ?_) le_self_add
        simp only [hk, Option.getD_some, Option.bind_some]
      · refine le_trans (prob_le_one _ _) (le_trans (le_of_eq ?_) le_add_self)
        rw [askCode_of_some hs]
        show 1 = prob (PMF.pure ((), o.2 ++ (spelling o.1.1, f (spelling o.1.1)) ::
          (o'.2 ++ [(s, f s)]))) {o | AnswerRepeats o.2}
        rw [prob_pure, if_pos]
        show AnswerRepeats (o.2 ++ (spelling o.1.1, f (spelling o.1.1)) :: (o'.2 ++ [(s, f s)]))
        rw [hd]
        exact answerRepeats_of_hit hinj o.2 o'.2 o.1.1 _ hs hk
    · rw [if_neg hd, zero]
      exact zero_le _

/-- Index binding passes to the scheme in which the verifier's key is the digest of A's, if the
coding is one to one: with the extractor `E.digestKey enc` and the bound of A plus
(tC + tP + 2)² / 2^λ. -/
theorem HasIndexBindingWith.digestKey {R : IndexedRelation I X W PP}
    {A : Arg lam I X W IVK ISK Pf} {E : Extractor lam I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : HasIndexBindingWith R A E ε) {enc : IVK → Option Str} (hinj : CodeIsOneToOne enc) :
    HasIndexBindingWith R (A.digestKey enc) (E.digestKey enc)
      fun tC tP => ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  intro tC tP St Ct Pt hC hP
  obtain ⟨⟨-, st⟩⟩ := Ct.nonempty
  obtain ⟨⟨-, k0, -⟩⟩ := (Pt st).nonempty
  exact h.of_verifyDigestKey hinj k0 (A.digestKey enc) rfl tC tP St Ct Pt hC hP

namespace DigestKey

/-- The codes of two keys; the empty string for a key without a code. -/
def codesOf (enc : IVK → Option Str) (enc' : IVK' → Option Str) (p : IVK × IVK') : Str × Str :=
  ((enc p.1).getD [], (enc' p.2).getD [])

/-- An algorithm that outputs two keys, followed by the queries at their codes. -/
def thenAskCodes (enc : IVK → Option Str) (enc' : IVK' → Option Str) (c : OComp lam (IVK × IVK')) :
    OComp lam Unit :=
  (c.mapO (codesOf enc enc')).bind askTwo

theorem queryBound_thenAskCodes (enc : IVK → Option Str) (enc' : IVK' → Option Str)
    (c : OComp lam (IVK × IVK')) (t : ℕ) (hc : c.QueryBound t) :
    (thenAskCodes enc enc' c).QueryBound (t + 2) :=
  OComp.QueryBound.bind askTwo 2 queryBound_askTwo _ t (OComp.QueryBound.mapO _ c t hc)

/-- Under one hash function: the probability that an algorithm outputs a key of each of two codings,
with codes that differ and have the same hash value, is at most the probability that the event
happens in its query log followed by the queries at the two codes. -/
theorem prob_two_codes_le (f : Oracle lam) (enc : IVK → Option Str) (enc' : IVK' → Option Str)
    (c : OComp lam (IVK × IVK')) :
    prob (c.run f) {p | ∃ s s', enc p.1 = some s ∧ enc' p.2 = some s' ∧ s ≠ s' ∧ f s = f s'}
      ≤ prob ((thenAskCodes enc enc' c).withTrace.run f) {o | AnswerRepeats o.2} := by
  refine le_trans ?_ (prob_two_strings_le f (c.mapO (codesOf enc enc')))
  rw [OComp.run_mapO, prob_map]
  refine prob_mono _ ?_
  rintro p ⟨s, s', h1, h2, hne, h3⟩
  show (enc p.1).getD [] ≠ (enc' p.2).getD [] ∧ f ((enc p.1).getD []) = f ((enc' p.2).getD [])
  rw [h1, h2]
  exact ⟨hne, h3⟩

end DigestKey

/-- If the coding is one to one, an algorithm with at most t queries outputs two different keys that
both have codes and have the same digest with probability at most (t + 2)² / 2^λ. (All keys without
a code have the digest of zeros.) The two digests are computed after the algorithm has stopped. -/
theorem Pr_two_keys_one_digest_le {enc : IVK → Option Str} (hinj : CodeIsOneToOne enc)
    (c : OComp lam (IVK × IVK)) (t : ℕ) (hc : c.QueryBound t) :
    Pr (c.bind fun p => (keyDigest enc p.1).bind fun d₁ => (keyDigest enc p.2).bind fun d₂ =>
        .pure (p, d₁, d₂))
      (fun _ => {o | o.1.1 ≠ o.1.2 ∧ enc o.1.1 ≠ none ∧ enc o.1.2 ≠ none ∧ o.2.1 = o.2.2})
      ≤ (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  classical
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_)
    (Pr_answerRepeats_le _ _ (queryBound_thenAskCodes enc enc c t hc))
  refine le_trans ?_ (prob_two_codes_le f enc enc c)
  show prob ((c.bind fun p => (keyDigest enc p.1).bind fun d₁ => (keyDigest enc p.2).bind fun d₂ =>
      .pure (p, d₁, d₂)).run f) _ ≤ _
  rw [run_bind, prob_bind, prob_eq_expect]
  refine expect_mono _ fun p => ?_
  rw [run_bind, run_keyDigest, PMF.pure_bind, run_bind, run_keyDigest, PMF.pure_bind]
  show prob (PMF.pure (p, digestUnder f enc p.1, digestUnder f enc p.2)) _ ≤ _
  rw [prob_pure]
  split
  · rename_i ho
    obtain ⟨hne, c1, c2, hd⟩ := ho
    have hd' : digestUnder f enc p.1 = digestUnder f enc p.2 := hd
    cases h1 : enc p.1 with
    | none => exact absurd h1 c1
    | some s₁ =>
      cases h2 : enc p.2 with
      | none => exact absurd h2 c2
      | some s₂ =>
        rw [digestUnder_of_some f h1, digestUnder_of_some f h2] at hd'
        rw [if_pos ⟨s₁, s₂, h1, h2, fun h4 => hne (hinj _ _ s₁ h1 (h4 ▸ h2)), hd'⟩]
  · exact zero_le _

/-- Under a hash function that does not give the digest at the code of the key that the proof
brings, the verifier rejects. -/
theorem run_verifyDigestKey_of_ne (V : IVK → X → Pf → OComp lam Bool) {enc : IVK → Option Str}
    (f : Oracle lam) (digest : Digest lam) (x : X) (proof : IVK × Pf)
    (h : ∀ s, enc proof.1 = some s → f s ≠ digest) :
    (verifyDigestKey V enc digest x proof).run f = PMF.pure false := by
  cases hs : enc proof.1 with
  | none =>
    rw [verifyDigestKey_of_none V digest x proof hs]
    rfl
  | some s =>
    rw [run_verifyDigestKey V f digest x proof hs, if_neg (h s hs)]
    rfl

namespace DigestKey

theorem prob_bind_eq_zero {α β : Type} (p : PMF α) (g : α → PMF β) (E : Set β)
    (h : ∀ a, prob (g a) E = 0) : prob (p.bind g) E = 0 := by
  rw [prob_bind, expect_congr p h, expect_const]

/-- An inequality under each hash function gives the inequality of the probabilities. -/
theorem Pr_le_of_forall {α β : Type} (a : OComp lam α) (b : OComp lam β) (A : Set α) (B : Set β)
    (h : ∀ f, prob (a.run f) A ≤ prob (b.run f) B) : Pr a (fun _ => A) ≤ Pr b (fun _ => B) :=
  MeasureTheory.lintegral_mono h

/-- If the second step reaches the event E with probability 0 wherever the first step's output lies
outside T, then E has at most the probability that the first step's output lies in T. -/
theorem prob_bind_le_of_forall {α β : Type} (f : Oracle lam) (c : OComp lam α)
    (g : α → OComp lam β) (E : Set β) (T : Set α) (h : ∀ a, a ∉ T → prob ((g a).run f) E = 0) :
    prob ((c.bind g).run f) E ≤ prob (c.run f) T := by
  classical
  rw [run_bind, prob_bind, prob_eq_expect]
  refine expect_mono _ fun a => ?_
  by_cases ha : a ∈ T
  · rw [if_pos ha]
    exact prob_le_one _ _
  · rw [if_neg ha, h a ha]

section TwoBits
variable {γ : Type} (f : Oracle lam) (p q : OComp lam Bool) (out : Bool → Bool → γ) (E : Set γ)

/-- Two algorithms that output a bit, one after the other: an event that holds for no pair of bits
has probability 0. -/
theorem prob_two_bits_eq_zero (h : ∀ b b', out b b' ∉ E) :
    prob ((p.bind fun b => q.bind fun b' => .pure (out b b')).run f) E = 0 := by
  rw [run_bind]
  refine prob_bind_eq_zero _ _ _ fun b => ?_
  rw [run_bind]
  refine prob_bind_eq_zero _ _ _ fun b' => ?_
  show prob (PMF.pure (out b b')) E = 0
  rw [prob_pure, if_neg (h b b')]

/-- The same if the first bit is 0 under f, for an event that asks that it be 1. -/
theorem prob_two_bits_eq_zero_left (hp : p.run f = PMF.pure false) (h : ∀ b', out false b' ∉ E) :
    prob ((p.bind fun b => q.bind fun b' => .pure (out b b')).run f) E = 0 := by
  rw [run_bind, hp, PMF.pure_bind, run_bind]
  refine prob_bind_eq_zero _ _ _ fun b' => ?_
  show prob (PMF.pure (out false b')) E = 0
  rw [prob_pure, if_neg (h b')]

/-- The same if the second bit is 0 under f. -/
theorem prob_two_bits_eq_zero_right (hq : q.run f = PMF.pure false) (h : ∀ b, out b false ∉ E) :
    prob ((p.bind fun b => q.bind fun b' => .pure (out b b')).run f) E = 0 := by
  rw [run_bind]
  refine prob_bind_eq_zero _ _ _ fun b => ?_
  rw [run_bind, hq, PMF.pure_bind]
  show prob (PMF.pure (out b false)) E = 0
  rw [prob_pure, if_neg (h b)]

end TwoBits

/-- Under one hash function, at one output o of the algorithm: unless the two keys have different
codes with the same hash value, it does not happen that both verifiers accept and the codes differ.
-/
theorem prob_both_accept_eq_zero (V : IVK → X → Pf → OComp lam Bool)
    (V' : IVK' → X' → Pf' → OComp lam Bool) (enc : IVK → Option Str) (enc' : IVK' → Option Str)
    (f : Oracle lam) (o : Digest lam × (X × (IVK × Pf)) × (X' × (IVK' × Pf')))
    (hn : ¬ ∃ s s', enc o.2.1.2.1 = some s ∧ enc' o.2.2.2.1 = some s' ∧ s ≠ s' ∧ f s = f s') :
    prob (((verifyDigestKey V enc o.1 o.2.1.1 o.2.1.2).bind fun b =>
        (verifyDigestKey V' enc' o.1 o.2.2.1 o.2.2.2).bind fun b' => .pure (o, b, b')).run f)
      {r | r.2.1 = true ∧ r.2.2 = true ∧ enc r.1.2.1.2.1 ≠ enc' r.1.2.2.2.1} = 0 := by
  by_cases heq : enc o.2.1.2.1 = enc' o.2.2.2.1
  · exact prob_two_bits_eq_zero f _ _ (fun b b' => (o, b, b')) _ fun _ _ h => h.2.2 heq
  · by_cases a1 : ∀ s, enc o.2.1.2.1 = some s → f s ≠ o.1
    · exact prob_two_bits_eq_zero_left f _ _ (fun b b' => (o, b, b')) _
        (run_verifyDigestKey_of_ne V f o.1 o.2.1.1 o.2.1.2 a1) fun _ h => Bool.noConfusion h.1
    · have a2 : ∀ s', enc' o.2.2.2.1 = some s' → f s' ≠ o.1 := by
        intro s' h2 h4
        refine a1 fun s h1 h3 => hn ⟨s, s', h1, h2, ?_, h3.trans h4.symm⟩
        rintro rfl
        exact heq (h1.trans h2.symm)
      exact prob_two_bits_eq_zero_right f _ _ (fun b b' => (o, b, b')) _
        (run_verifyDigestKey_of_ne V' f o.1 o.2.2.1 o.2.2.2 a2) fun _ h => Bool.noConfusion h.2.1

end DigestKey

/-- One digest and two keys with different codes, be it under two verifiers with two codings. An
algorithm with at most t queries outputs a digest and, for each of the two verifiers, an
instance and a proof. With probability at most (t + 2)² / 2^λ both verifiers accept under that
digest while the keys that the two proofs bring have different codes. So, if the two codings share
no bit string, both verifiers accept under that digest with at most that probability; a string that
both codings give serves both. -/
theorem Pr_two_verifiers_one_digest_le (V : IVK → X → Pf → OComp lam Bool)
    (V' : IVK' → X' → Pf' → OComp lam Bool) (enc : IVK → Option Str) (enc' : IVK' → Option Str)
    (c : OComp lam (Digest lam × (X × (IVK × Pf)) × (X' × (IVK' × Pf')))) (t : ℕ)
    (hc : c.QueryBound t) :
    Pr (c.bind fun o => (verifyDigestKey V enc o.1 o.2.1.1 o.2.1.2).bind fun b =>
        (verifyDigestKey V' enc' o.1 o.2.2.1 o.2.2.2).bind fun b' => .pure (o, b, b'))
      (fun _ => {r | r.2.1 = true ∧ r.2.2 = true ∧ enc r.1.2.1.2.1 ≠ enc' r.1.2.2.2.1})
      ≤ (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  have hb := queryBound_thenAskCodes enc enc' (c.mapO fun o => (o.2.1.2.1, o.2.2.2.1)) t
    (OComp.QueryBound.mapO _ c t hc)
  refine le_trans (Pr_le_of_forall _ _ _ _ fun f => ?_) (Pr_answerRepeats_le _ _ hb)
  have h2 := prob_two_codes_le f enc enc' (c.mapO fun o => (o.2.1.2.1, o.2.2.2.1))
  rw [OComp.run_mapO, prob_map] at h2
  exact le_trans (prob_bind_le_of_forall f c _ _ _ fun o hn =>
    prob_both_accept_eq_zero V V' enc enc' f o hn) h2

end Key

end ZKCP
