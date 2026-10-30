-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/ManyOfOne.lean: from index binding for one proof to many proofs, for a V without coins.
(not all hypotheses are named here: see `sessionAugmentedAt_of_binding`)

The bound for N proofs is ε(tC, tP + N · tV): no factor N in front of it.

Index binding for many sessions (ZKCP/Optional.lean: multiBindingExp, HasSessionAugmentedBinding): a
single run lets the dishonest prover hand in several instances with their proofs, (x_j, π_j), at
once; it wins if it kept within N of them and V passes one whose instance is outside the language of
the one index that was extracted.

Main names:
  `sessionAugmentedAt_of_binding`   if A has index binding with the extractor E and the bound ε
    (`HasIndexBinding`), V makes at most tV queries and draws no coin, then A has the
    property at the same index extractor E.Ei (the statement is written out) with the bound
    ε tC (tP + N · tV): N enters through the queries of N runs of V alone
  `sessionAugmented_of_binding`   the same in the form of ZKCP/Optional.lean, with the extractor
    under ∃

How: A cheating prover for one proof runs the cheating prover for many, runs V itself on the first N
pairs (N · tV queries), and outputs the first pair that V accepted and whose instance is not in the
language of the extracted index, which the reduction's committer has passed to it in its state. V
uses no coins: so for every oracle its verdict in the experiment is the verdict that the prover has
seen. The test "not in the language" is a case distinction of the mathematics, not a computation:
the definition's adversaries are arbitrary trees and are bounded in their queries alone.

Limits: The prover for many proofs outputs one list and learns no verdict in between (as in
ZKCP/Optional.lean: multiBindingExp). Nothing for a V with coins. The witness half of
`bindingBad` is not used. x₀, π₀: any instance and any proof, put out where no pair qualifies; they
occur in no statement's conclusion.

After ZKCP/Defs.lean and index binding for many sessions of ZKCP/Optional.lean; the
reduction is not in these two files.
-/
import ZKCP.KeyTag
import ZKCP.Optional
import ZKCP.Main

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-! ## Tools on computations -/

namespace OComp
variable {α β : Type}

theorem withTrace_bind (c : OComp lam α) (g : α → OComp lam β) :
    (c.bind g).withTrace =
      c.withTrace.bind fun a => (g a.1).withTrace.bind fun b => .pure (b.1, a.2 ++ b.2) := by
  induction c with
  | pure a =>
      show (g a).withTrace = (g a).withTrace.bind fun b => .pure (b.1, [] ++ b.2)
      exact (bind_pure_right _).symm
  | query q k ih =>
      show OComp.query q
          (fun r => ((k r).bind g).withTrace.bind fun out => .pure (out.1, (q, r) :: out.2)) =
        OComp.query q fun r =>
          ((k r).withTrace.bind fun out => .pure (out.1, (q, r) :: out.2)).bind fun a =>
            (g a.1).withTrace.bind fun b => .pure (b.1, a.2 ++ b.2)
      refine congrArg _ (funext fun r => ?_)
      rw [ih r, bind_bind, bind_bind]
      refine congrArg _ (funext fun a => ?_)
      rw [bind_bind]
      rfl
  | sample n k ih =>
      show OComp.sample n (fun r => ((k r).bind g).withTrace) =
        OComp.sample n fun r =>
          (k r).withTrace.bind fun a => (g a.1).withTrace.bind fun b => .pure (b.1, a.2 ++ b.2)
      exact congrArg _ (funext ih)

/-- the trace of an algorithm that outputs its own trace is that trace -/
theorem withTrace_withTrace (c : OComp lam α) :
    c.withTrace.withTrace = c.withTrace.mapO fun o => (o, o.2) := by
  induction c with
  | pure a => rfl
  | query q k ih =>
      show OComp.query q (fun r =>
          ((k r).withTrace.bind fun out => .pure (out.1, (q, r) :: out.2)).withTrace.bind
            fun out => .pure (out.1, (q, r) :: out.2)) =
        OComp.query q fun r =>
          ((k r).withTrace.bind fun out => .pure (out.1, (q, r) :: out.2)).mapO fun o => (o, o.2)
      refine congrArg _ (funext fun r => ?_)
      rw [withTrace_bind, ih r, mapO_bind, bind_bind, bind_mapO]
      refine congrArg _ (funext fun a => ?_)
      show OComp.pure _ = OComp.pure _
      simp
  | sample n k ih =>
      show OComp.sample n (fun r => (k r).withTrace.withTrace) =
        OComp.sample n fun r => (k r).withTrace.mapO fun o => (o, o.2)
      exact congrArg _ (funext ih)

theorem QueryBound.mono : ∀ (c : OComp lam α) (s t : ℕ), s ≤ t → c.QueryBound s → c.QueryBound t
  | .pure _, _, _, _, _ => trivial
  | .query _ _, 0, _, _, h => h.elim
  | .query _ _, _ + 1, 0, hst, _ => absurd hst (Nat.not_succ_le_zero _)
  | .query _ k, s + 1, t + 1, hst, h => fun r => QueryBound.mono (k r) s t (Nat.le_of_succ_le_succ hst) (h r)
  | .sample _ k, s, t, hst, h => fun r => QueryBound.mono (k r) s t hst (h r)

theorem QueryBound.bind (g : α → OComp lam β) (t : ℕ) (hg : ∀ a, (g a).QueryBound t) :
    ∀ (c : OComp lam α) (s : ℕ), c.QueryBound s → (c.bind g).QueryBound (s + t)
  | .pure a, s, _ => QueryBound.mono (g a) t (s + t) (Nat.le_add_left _ _) (hg a)
  | .query _ _, 0, h => h.elim
  | .query _ k, s + 1, h => by
      rw [Nat.succ_add]
      exact fun r => QueryBound.bind g t hg (k r) s (h r)
  | .sample _ k, s, h => fun r => QueryBound.bind g t hg (k r) s (h r)

theorem QueryBound.withTrace :
    ∀ (c : OComp lam α) (t : ℕ), c.QueryBound t → c.withTrace.QueryBound t
  | .pure _, _, _ => trivial
  | .query _ _, 0, h => h.elim
  | .query _ k, t + 1, h => fun r => QueryBound.mapO _ _ t (QueryBound.withTrace (k r) t (h r))
  | .sample _ k, t, h => fun r => QueryBound.withTrace (k r) t (h r)

theorem run_withTrace_fst (f : Oracle lam) (c : OComp lam α) :
    (c.withTrace.run f).map Prod.fst = c.run f := by
  induction c with
  | pure a => exact PMF.pure_map _ _
  | query q k ih =>
      show (((k (f q)).withTrace.bind fun out => .pure (out.1, (q, f q) :: out.2)).run
          f).map Prod.fst = (k (f q)).run f
      rw [← ih (f q), run_bind, PMF.map_bind]
      show _ = ((k (f q)).withTrace.run f).bind (PMF.pure ∘ Prod.fst)
      refine congrArg _ (funext fun a => ?_)
      exact PMF.pure_map _ _
  | sample n k ih =>
      show ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).withTrace.run f).map Prod.fst =
        (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).run f
      rw [PMF.map_bind]
      exact congrArg _ (funext ih)

/-- without coins the output is a function of the oracle -/
theorem DrawsNoCoin.run (f : Oracle lam) :
    ∀ c : OComp lam α, c.DrawsNoCoin → ∃ a, c.run f = PMF.pure a
  | .pure a, _ => ⟨a, rfl⟩
  | .query q k, h => DrawsNoCoin.run f (k (f q)) (h (f q))
  | .sample _ _, h => h.elim

end OComp

theorem prob_pure_le_of_support {β γ : Type} {o : β} {E : Set β} {q : PMF γ}
    {E' : Set γ} (h : o ∈ E → ∀ c ∈ q.support, c ∈ E') :
    prob (PMF.pure o) E ≤ prob q E' := by
  classical
  rw [prob_pure]
  by_cases ho : o ∈ E
  · rw [if_pos ho]
    refine le_of_eq ?_
    exact ((PMF.toOuterMeasure_apply_eq_one_iff q E').2 (h ho)).symm
  · rw [if_neg ho]
    exact zero_le _

/-! ## The reduction -/

namespace ManyOfOne
variable (A : Arg lam I X W IVK ISK Pf)

/-- V on every pair; the output is the list of V's bits, each with its pair -/
def runAll (ivk : IVK) : List (X × Pf) → OComp lam (List (Bool × (X × Pf)))
  | [] => .pure []
  | e :: rest =>
    (A.V ivk e.1 e.2).bind fun b => (runAll ivk rest).bind fun bs => .pure ((b, e) :: bs)

theorem queryBound_runAll {tV : ℕ} (hq : ∀ v x π, (A.V v x π).QueryBound tV) (ivk : IVK) :
    ∀ l : List (X × Pf), (runAll A ivk l).QueryBound (l.length * tV)
  | [] => trivial
  | e :: rest => by
      have h := OComp.QueryBound.bind
        (fun b => (runAll A ivk rest).bind fun bs => .pure ((b, e) :: bs)) (rest.length * tV + 0)
        (fun b =>
          OComp.QueryBound.bind (fun bs => OComp.pure ((b, e) :: bs)) 0 (fun _ => trivial)
            _ _ (queryBound_runAll hq ivk rest))
        _ _ (hq ivk e.1 e.2)
      refine OComp.QueryBound.mono _ _ _ (le_of_eq ?_) h
      rw [List.length_cons, Nat.succ_mul]
      omega

theorem run_runAll (f : Oracle lam) (val : IVK → X → Pf → Bool)
    (hval : ∀ v x π, (A.V v x π).run f = PMF.pure (val v x π)) (ivk : IVK) :
    ∀ l : List (X × Pf), (runAll A ivk l).run f = PMF.pure (l.map fun e => (val ivk e.1 e.2, e))
  | [] => rfl
  | e :: rest => by
      show ((A.V ivk e.1 e.2).bind fun b =>
          (runAll A ivk rest).bind fun bs => .pure ((b, e) :: bs)).run f = _
      rw [run_bind, hval, PMF.pure_bind, run_bind, run_runAll f val hval ivk rest, PMF.pure_bind]
      rfl

theorem run_verifyAll (f : Oracle lam) (val : IVK → X → Pf → Bool)
    (hval : ∀ v x π, (A.V v x π).run f = PMF.pure (val v x π)) (ivk : IVK) :
    ∀ l : List (X × Pf),
      (verifyAll A ivk l).run f = PMF.pure (l.map fun e => (val ivk e.1 e.2, e.1))
  | [] => rfl
  | (x, π) :: rest => by
      show ((A.V ivk x π).bind fun b =>
          (verifyAll A ivk rest).bind fun bs => .pure ((b, x) :: bs)).run f = _
      rw [run_bind, hval, PMF.pure_bind, run_bind, run_verifyAll f val hval ivk rest, PMF.pure_bind]
      rfl

end ManyOfOne

open ManyOfOne in
/-- From one proof to many, without a factor in front. If A has index binding ε for the extractor E,
and V makes at most tV queries and uses no coins, then for all tC, tP, N, every committer with at
most tC queries and every prover with at most tP queries: Pr[ at most N pairs were output and V
accepts one whose instance is not in L(i*) ] ≤ ε(tC, tP + N · tV), with i* from `E.Ei`. (x₀, π₀: any
instance and any proof.) -/
theorem sessionAugmentedAt_of_binding {R : IndexedRelation I X W PP}
    {A : Arg lam I X W IVK ISK Pf} {E : Extractor lam I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞}
    (hb : HasIndexBindingWith R A E ε) {tV : ℕ} (hq : ∀ v x π, (A.V v x π).QueryBound tV)
    (hn : ∀ v x π, (A.V v x π).DrawsNoCoin) (x₀ : X) (π₀ : Pf) :
    ∀ (tC tP N : ℕ) (St : Type) (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (List (X × Pf))),
      Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
      Pr (multiBindingExp A E.Ei Ct Pt)
          (fun _ => {o | o.2.length ≤ N ∧ ∃ bx ∈ o.2, bx.1 = true ∧ bx.2 ∉ R.L o.1}) ≤
        ε tC (tP + N * tV) := by
  classical
  intro tC tP N St Ct Pt hC hP
  -- the pair that the prover for one proof outputs
  let pick : Option I → List (Bool × (X × Pf)) → X × Pf := fun i rs =>
    ((rs.find? fun e => e.1 && decide (e.2.1 ∉ R.L i)).map Prod.snd).getD (x₀, π₀)
  let hh : (IVK × St) × Trace lam → IVK × (St × IVK × Option I) := fun o =>
    (o.1.1, (o.1.2, o.1.1, E.Ei o.1.1 o.2))
  let Ct' : OComp lam (IVK × (St × IVK × Option I)) := Ct.withTrace.mapO hh
  let Y : IVK → Option I → List (X × Pf) → OComp lam (X × Pf) := fun v i l =>
    (runAll A v (l.take N)).mapO (pick i)
  let Pt' : St × IVK × Option I → OComp lam (X × Pf) := fun s =>
    (Pt s.1).bind fun l => Y s.2.1 s.2.2 l
  have hC' : Ct'.QueryBound tC := OComp.QueryBound.mapO _ _ _ (OComp.QueryBound.withTrace _ _ hC)
  have hP' : ∀ s, (Pt' s).QueryBound (tP + N * tV) := fun s =>
    OComp.QueryBound.bind _ _
      (fun l =>
        OComp.QueryBound.mapO _ _ _
          (OComp.QueryBound.mono _ _ _ (Nat.mul_le_mul_right _ (List.length_take_le N l))
            (queryBound_runAll A hq s.2.1 (l.take N))))
      _ _ (hP s.1)
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_) (hb tC (tP + N * tV) _ Ct' Pt' hC' hP')
  -- the oracle is fixed: V's verdicts are a function
  choose val hval using fun v x π => OComp.DrawsNoCoin.run f (A.V v x π) (hn v x π)
  show prob ((Ct.withTrace.bind fun o =>
        (Pt o.1.2).bind fun l =>
          (verifyAll A o.1.1 l).bind fun bs => .pure (E.Ei o.1.1 o.2, bs)).run f) _ ≤
    prob ((Ct'.withTrace.bind fun a =>
        (Pt' a.1.2).withTrace.bind fun b =>
          (A.V a.1.1 b.1.1 b.1.2).bind fun c =>
            .pure (⟨c, E.Ei a.1.1 a.2, b.1.1,
                E.Ew a.1.1 a.2 b.1.1 b.1.2 b.2⟩ : BindingOutcome I X W)).run f) (bindingBad R)
  have eC : Ct'.withTrace = Ct.withTrace.mapO fun o => (hh o, o.2) := by
    show (Ct.withTrace.mapO hh).withTrace = _
    rw [OComp.withTrace_mapO, OComp.withTrace_withTrace]
    exact OComp.bind_bind _ _ _
  rw [eC, OComp.mapO_bind, run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun o => ?_
  show prob (((Pt o.1.2).bind fun l =>
        (verifyAll A o.1.1 l).bind fun bs => .pure (E.Ei o.1.1 o.2, bs)).run f) _ ≤
    prob ((((Pt o.1.2).bind fun l => Y o.1.1 (E.Ei o.1.1 o.2) l).withTrace.bind fun b =>
        (A.V o.1.1 b.1.1 b.1.2).bind fun c =>
          .pure (⟨c, E.Ei o.1.1 o.2, b.1.1,
              E.Ew o.1.1 o.2 b.1.1 b.1.2 b.2⟩ : BindingOutcome I X W)).run f) (bindingBad R)
  rw [OComp.withTrace_bind, OComp.bind_bind, run_bind, run_bind,
    ← OComp.run_withTrace_fst f (Pt o.1.2), PMF.bind_map, prob_bind, prob_bind]
  refine expect_mono _ fun a => ?_
  show prob (((verifyAll A o.1.1 a.1).bind fun bs => .pure (E.Ei o.1.1 o.2, bs)).run f) _ ≤ _
  rw [run_bind, run_verifyAll A f val hval, PMF.pure_bind]
  refine prob_pure_le_of_support fun hbad c hc => ?_
  obtain ⟨hlen, bx, hbx, htrue, hnot⟩ := hbad
  -- what the prover for one proof outputs
  have hl : a.1.take N = a.1 := List.take_of_length_le (by simpa using hlen)
  have hY : (Y o.1.1 (E.Ei o.1.1 o.2) a.1).run f =
      PMF.pure (pick (E.Ei o.1.1 o.2) (a.1.map fun e => (val o.1.1 e.1 e.2, e))) := by
    show ((runAll A o.1.1 (a.1.take N)).mapO (pick (E.Ei o.1.1 o.2))).run f = _
    rw [OComp.run_mapO, run_runAll A f val hval, hl, PMF.pure_map]
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hbx
  have hpick : val o.1.1 (pick (E.Ei o.1.1 o.2) (a.1.map fun e => (val o.1.1 e.1 e.2, e))).1
          (pick (E.Ei o.1.1 o.2) (a.1.map fun e => (val o.1.1 e.1 e.2, e))).2 = true ∧
      (pick (E.Ei o.1.1 o.2) (a.1.map fun e => (val o.1.1 e.1 e.2, e))).1 ∉
        R.L (E.Ei o.1.1 o.2) := by
    show val o.1.1
          ((((a.1.map fun e => (val o.1.1 e.1 e.2, e)).find? fun e =>
                e.1 && decide (e.2.1 ∉ R.L (E.Ei o.1.1 o.2))).map Prod.snd).getD (x₀, π₀)).1
          ((((a.1.map fun e => (val o.1.1 e.1 e.2, e)).find? fun e =>
                e.1 && decide (e.2.1 ∉ R.L (E.Ei o.1.1 o.2))).map Prod.snd).getD (x₀, π₀)).2 =
        true ∧
      ((((a.1.map fun e => (val o.1.1 e.1 e.2, e)).find? fun e =>
              e.1 && decide (e.2.1 ∉ R.L (E.Ei o.1.1 o.2))).map Prod.snd).getD (x₀, π₀)).1 ∉
        R.L (E.Ei o.1.1 o.2)
    cases hf : (a.1.map fun e => (val o.1.1 e.1 e.2, e)).find? fun e =>
        e.1 && decide (e.2.1 ∉ R.L (E.Ei o.1.1 o.2)) with
    | none =>
        have h0 := List.find?_eq_none.1 hf (val o.1.1 e.1 e.2, e) (List.mem_map.2 ⟨e, he, rfl⟩)
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h0
        exact absurd hnot (h0 htrue)
    | some r =>
        have h1 := List.find?_some hf
        obtain ⟨e', -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hf)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        exact h1
  -- the support of the experiment for one proof
  simp only [OComp.bind_bind, run_bind, PMF.mem_support_bind_iff] at hc
  obtain ⟨b, hb1, hc⟩ := hc
  have hb2 : b.1 = pick (E.Ei o.1.1 o.2) (a.1.map fun e => (val o.1.1 e.1 e.2, e)) := by
    have h3 : b.1 ∈ (((Y o.1.1 (E.Ei o.1.1 o.2) a.1).withTrace.run f).map Prod.fst).support :=
      (PMF.mem_support_map_iff _ _ _).2 ⟨b, hb1, rfl⟩
    rw [OComp.run_withTrace_fst, hY, PMF.support_pure] at h3
    exact h3
  obtain ⟨a1, ha1, c0, hc0, hc⟩ := hc
  have ea1 : a1 = (b.1, a.2 ++ b.2) := (PMF.mem_support_pure_iff _ _).1 ha1
  subst ea1
  rw [hval, PMF.support_pure] at hc0
  have ec0 : c0 = val o.1.1 b.1.1 b.1.2 := hc0
  have ec : c = ⟨c0, E.Ei o.1.1 o.2, b.1.1, E.Ew o.1.1 o.2 b.1.1 b.1.2 (a.2 ++ b.2)⟩ :=
    (PMF.mem_support_pure_iff _ _).1 hc
  rw [ec, ec0, hb2]
  exact ⟨hpick.1, Or.inl hpick.2⟩

/-- `sessionAugmentedAt_of_binding`, under the same hypotheses, in the form
`HasSessionAugmentedBinding` of ZKCP/Optional.lean. -/
theorem sessionAugmented_of_binding {R : IndexedRelation I X W PP}
    {A : Arg lam I X W IVK ISK Pf} {E : Extractor lam I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞}
    (hb : HasIndexBindingWith R A E ε) {tV : ℕ} (hq : ∀ v x π, (A.V v x π).QueryBound tV)
    (hn : ∀ v x π, (A.V v x π).DrawsNoCoin) (x₀ : X) (π₀ : Pf) :
    HasSessionAugmentedBinding R A fun tC tP N => ε tC (tP + N * tV) :=
  ⟨E.Ei, sessionAugmentedAt_of_binding hb hq hn x₀ π₀⟩

end ZKCP
