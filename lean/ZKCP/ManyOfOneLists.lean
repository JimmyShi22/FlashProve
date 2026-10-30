-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/ManyOfOneLists.lean: from a bound for one proof to a bound for a list of proofs.

`ManyOfOneLists.many_of_one`, under the hypotheses of its statement: a committer outputs a key, a
prover outputs an element, and a test with at most tV queries, whose result under each hash function
is one value, decides on the key and the element. If the game with one element has the bound ε tC tP
for all adversaries (a committer with at most tC queries, a prover with at most tP), the game in
which the prover outputs a list has the bound ε tC (tP + N · tV) for the event "at most N elements,
and one of them passes the test and is not good". `Good` is any property of the key, of a value
computed from the key and the committer's query log, and of the element. N enters through the
queries of N runs of the test alone.
It is ZKCP/ManyOfOne.lean's step in a form that names no scheme: the test is any family of
algorithms, and the event may read the hash function.
The prover outputs one list and is told no decision in between. Nothing for a test whose result
depends on its own random choices.
-/
import ZKCP.ManyOfOne
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP
namespace ManyOfOneLists

variable {lam : ℕ}

/-- Runs the test T on every element of a list and returns the bits paired with the elements. -/
def runList {K Aa : Type} (T : K → Aa → OComp lam Bool) (k : K) :
    List Aa → OComp lam (List (Bool × Aa))
  | [] => .pure []
  | e :: rest => (T k e).bind fun b => (runList T k rest).bind fun bs => .pure ((b, e) :: bs)

/-- If T makes at most tV queries on every input, `runList` on a list makes at most tV queries for
each element. -/
theorem queryBound_runList {K Aa : Type} (T : K → Aa → OComp lam Bool) {tV : ℕ}
    (hq : ∀ k a, (T k a).QueryBound tV) (k : K) :
    ∀ l : List Aa, (runList T k l).QueryBound (l.length * tV)
  | [] => trivial
  | e :: rest => by
      have h := OComp.QueryBound.bind
        (fun b => (runList T k rest).bind fun bs => .pure ((b, e) :: bs)) (rest.length * tV + 0)
        (fun b =>
          OComp.QueryBound.bind (fun bs => OComp.pure ((b, e) :: bs)) 0 (fun _ => trivial)
            _ _ (queryBound_runList T hq k rest))
        _ _ (hq k e)
      refine OComp.QueryBound.mono _ _ _ (le_of_eq ?_) h
      rw [List.length_cons, Nat.succ_mul]
      omega

/-- If under f the result of T is the single value `val`, the result of `runList` under f is the
list of these values, paired with the elements. -/
theorem run_runList {K Aa : Type} (T : K → Aa → OComp lam Bool) (f : Oracle lam)
    (val : K → Aa → Bool) (hval : ∀ k a, (T k a).run f = PMF.pure (val k a)) (k : K) :
    ∀ l : List Aa, (runList T k l).run f = PMF.pure (l.map fun e => (val k e, e))
  | [] => rfl
  | e :: rest => by
      show ((T k e).bind fun b => (runList T k rest).bind fun bs => .pure ((b, e) :: bs)).run f = _
      rw [run_bind, hval, PMF.pure_bind, run_bind, run_runList T f val hval k rest, PMF.pure_bind]
      rfl

open Classical in
/-- The first element whose bit is true and for which g is false; a0 if there is none. This is a
classical case distinction, not a computation: the game's adversaries are arbitrary trees (`OComp`,
ZKCP/Defs.lean), bounded only in their queries. -/
def pick {Aa : Type} (g : Aa → Prop) (a0 : Aa) (rs : List (Bool × Aa)) : Aa :=
  ((rs.find? fun e => e.1 && decide (¬ g e.2)).map Prod.snd).getD a0

/-- If some element of the list has bit true and is not good, `pick` returns such an element. -/
theorem pick_spec {Aa : Type} (p : Aa → Bool) (g : Aa → Prop) (a0 : Aa) (l : List Aa) {a : Aa}
    (ha : a ∈ l) (hp : p a = true) (hg : ¬ g a) :
    p (pick g a0 (l.map fun e => (p e, e))) = true ∧ ¬ g (pick g a0 (l.map fun e => (p e, e))) := by
  unfold pick
  generalize hf : List.find? _ (l.map fun e => (p e, e)) = o
  cases o with
  | none =>
      have h0 := List.find?_eq_none.1 hf (p a, a) (List.mem_map.2 ⟨a, ha, rfl⟩)
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h0
      exact absurd hg (h0 hp)
  | some r =>
      have h1 := List.find?_some hf
      obtain ⟨e', -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hf)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact h1

/-- From one proof to many. The game: the committer outputs a key and a state; `cm` is any function
of the key and the committer's query log; the prover, from the state, outputs an element; `Good` is
any property of the key, `cm`'s value and the element. Suppose that the bit φ f k a is the output
under f of a test T k a with at most tV queries, and that the game with one element has the bound
ε tC tP for all adversaries (a committer with at most tC queries, a prover with at most tP). Then
the game in which the prover outputs a list, with the same two bounds on queries, has the bound
ε tC (tP + N · tV) for the event "at most N elements, and some element has bit true and is not good"
(with one element: it has bit true and is not good).
Proof idea: a prover for one element runs the prover for many, runs T itself on the first N elements
and outputs the first one with bit true that is not good, or `a0` (any given element) if there is
none. The committer passes the value of `cm` to it in its state. -/
theorem many_of_one {K Aa C : Type} (T : K → Aa → OComp lam Bool) (φ : Oracle lam → K → Aa → Bool)
    (hT : ∀ f k a, (T k a).run f = PMF.pure (φ f k a)) {tV : ℕ} (hq : ∀ k a, (T k a).QueryBound tV)
    (cm : K → Trace lam → C) (Good : K → C → Aa → Prop) (a0 : Aa) (ε : ℕ → ℕ → ℝ≥0∞)
    (h1 : ∀ (tC tP : ℕ) (St : Type) (Ct : OComp lam (K × St)) (Pv : St → OComp lam Aa),
      Ct.QueryBound tC → (∀ s, (Pv s).QueryBound tP) →
      Pr (Ct.withTrace.bind fun o => (Pv o.1.2).bind fun a => .pure (o.1.1, cm o.1.1 o.2, a))
          (fun f => {o | φ f o.1 o.2.2 = true ∧ ¬ Good o.1 o.2.1 o.2.2}) ≤ ε tC tP)
    (tC tP N : ℕ) (St : Type) (Ct : OComp lam (K × St)) (Pl : St → OComp lam (List Aa))
    (hC : Ct.QueryBound tC) (hP : ∀ s, (Pl s).QueryBound tP) :
    Pr (Ct.withTrace.bind fun o => (Pl o.1.2).bind fun l => .pure (o.1.1, cm o.1.1 o.2, l))
        (fun f => {o | o.2.2.length ≤ N ∧ ∃ a ∈ o.2.2, φ f o.1 a = true ∧ ¬ Good o.1 o.2.1 a}) ≤
      ε tC (tP + N * tV) := by
  let hh : (K × St) × Trace lam → K × (St × K × C) := fun o => (o.1.1, (o.1.2, o.1.1, cm o.1.1 o.2))
  let Ct' : OComp lam (K × (St × K × C)) := Ct.withTrace.mapO hh
  let Pv' : St × K × C → OComp lam Aa := fun s =>
    (Pl s.1).bind fun l => (runList T s.2.1 (l.take N)).mapO (pick (Good s.2.1 s.2.2) a0)
  have hC' : Ct'.QueryBound tC := OComp.QueryBound.mapO _ _ _ (OComp.QueryBound.withTrace _ _ hC)
  have hP' : ∀ s, (Pv' s).QueryBound (tP + N * tV) := fun s =>
    OComp.QueryBound.bind _ _
      (fun l =>
        OComp.QueryBound.mapO _ _ _
          (OComp.QueryBound.mono _ _ _ (Nat.mul_le_mul_right _ (List.length_take_le N l))
            (queryBound_runList T hq s.2.1 (l.take N))))
      _ _ (hP s.1)
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_) (h1 tC (tP + N * tV) _ Ct' Pv' hC' hP')
  show prob
      ((Ct.withTrace.bind fun o => (Pl o.1.2).bind fun l => .pure (o.1.1, cm o.1.1 o.2, l)).run f)
      {o | o.2.2.length ≤ N ∧ ∃ a ∈ o.2.2, φ f o.1 a = true ∧ ¬ Good o.1 o.2.1 a} ≤
    prob
      ((Ct'.withTrace.bind fun o => (Pv' o.1.2).bind fun a => .pure (o.1.1, cm o.1.1 o.2, a)).run f)
      {o | φ f o.1 o.2.2 = true ∧ ¬ Good o.1 o.2.1 o.2.2}
  have eC : Ct'.withTrace = Ct.withTrace.mapO fun o => (hh o, o.2) := by
    show (Ct.withTrace.mapO hh).withTrace = _
    rw [OComp.withTrace_mapO, OComp.withTrace_withTrace]
    exact OComp.bind_bind _ _ _
  rw [eC, OComp.mapO_bind, run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun o => ?_
  show prob (((Pl o.1.2).bind fun l => .pure (o.1.1, cm o.1.1 o.2, l)).run f) _ ≤
    prob ((((Pl o.1.2).bind fun l =>
          (runList T o.1.1 (l.take N)).mapO (pick (Good o.1.1 (cm o.1.1 o.2)) a0)).bind
        fun a => .pure (o.1.1, cm o.1.1 o.2, a)).run f) _
  rw [OComp.bind_bind, run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun l => ?_
  show prob (PMF.pure (o.1.1, cm o.1.1 o.2, l)) _ ≤
    prob ((((runList T o.1.1 (l.take N)).mapO (pick (Good o.1.1 (cm o.1.1 o.2)) a0)).bind
        fun a => .pure (o.1.1, cm o.1.1 o.2, a)).run f) _
  rw [run_bind, OComp.run_mapO, run_runList T f (φ f) (hT f), PMF.pure_map, PMF.pure_bind]
  show prob (PMF.pure _) _ ≤ prob (PMF.pure _) _
  rw [prob_pure, prob_pure]
  by_cases hbad : (o.1.1, cm o.1.1 o.2, l) ∈
    {o : K × C × List Aa | o.2.2.length ≤ N ∧ ∃ a ∈ o.2.2, φ f o.1 a = true ∧ ¬ Good o.1 o.2.1 a}
  · rw [if_pos hbad, if_pos]
    obtain ⟨hlen, a, ha, htrue, hnot⟩ := hbad
    have hl : l.take N = l := List.take_of_length_le hlen
    rw [hl]
    exact pick_spec (φ f o.1.1) (Good o.1.1 (cm o.1.1 o.2)) a0 l ha htrue hnot
  · rw [if_neg hbad]
    exact zero_le _

end ManyOfOneLists
end ZKCP
