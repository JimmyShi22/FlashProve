-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Guard.lean: a part of the join whose checker refuses where two strings of its own log
have one answer; and that a part has what the join asks of every part if that guarded part has it.

Why. A part made with a compiler (`Part`, OnBytes/Slice/JoinThree.lean) owes the clause `fit`: under
EVERY oracle a yes of its checker gives a yes of the compiled verifier under the family read out of
that oracle. A checker whose reader opens one hash tree twice, or meets one vertex on two paths,
need not meet that clause as it stands: under an oracle that answers two of the checker's own
strings alike the reader and the compiled verifier can part. Such oracles are rare. This file pays
for them once, over the one oracle alone, so that neither `Part.OK` nor the join turns, and no
further event is needed for it in the join.

Main definitions.
 `PartO.guard s` the part s with a checker that runs s's checker, looks at the log of that run, and
     refuses if two strings in it have one answer. All other fields are s's.
 `PartO.ownLog s g x` the log of s's checker on x under g.
Main theorems.
 `PartO.guard_det` the guarded checker's value; `guard_noCoin`, `guard_queryBound`: no coins, and as
     many queries as the checker.
 `PartO.lose_sub` s's event lies in the guarded part's event or in "two strings of the checker's own
     log have one answer".
 `PartO.pr_ownClash` the latter has probability at most (t + tR)^2 / 2^lam, for a maker with at most
     t queries and a checker without coins with at most tR.
 `PartO.ok_of_guard` if the guarded part has `PartO.OK`, then s has it with that much more in its
     bound.
Tools, for any family of oracles, on an algorithm that also puts out its own log:
`noCoin_withTrace`, `det_withTrace_fst`, `det_withTrace_query`, `det_withTrace_bind` (the log of one
algorithm and then another), `det_withTrace_ans` (every entry holds the oracle's answer).

What is not claimed. That any guarded part has `PartO.OK`: none is given. A guarded `Part` is
written for the compiler under OnBytes/TypedOracleCompiler/ alone (OnBytes/TypedOracleCompiler/Slice/PartGuard.lean), not for `Part`
of JoinThree.lean. The guard looks at the CHECKER's own log alone: a clash between a string of the
checker and a string of the maker is not its matter. Nor is a clash with a string that a compiled
verifier asks and the checker does not. The guarded checker is no program and is run by nobody: it
stands in the proof alone; the part in the conclusion has s's own checker. The test in it is not
computable as written (it is decided classically). The bound says nothing once it reaches 1.

-/
import OnBytes.Slice.PartO

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open scoped ENNReal

/-! ## An algorithm that also puts out its own log -/

section
variable {S : OSpec} {α : Type}

/-- An algorithm without coins that also puts out its own log has no coins. -/
theorem noCoin_withTrace (c : OComp S α) (h : c.NoCoin) : c.withTrace.NoCoin := by
  induction c with
  | pure a => trivial
  | query o q k ih => exact fun r => OComp.NoCoin.bind (ih r (h r)) fun _ => trivial
  | sample n k _ => exact h.elim

/-- Its value is the algorithm's value. -/
theorem det_withTrace_fst (g : Fam S) (c : OComp S α) : (c.withTrace.det g).1 = c.det g := by
  induction c with
  | pure a => rfl
  | query o q k ih =>
    show (((k (g o q)).withTrace.bind fun out =>
      OComp.pure (out.1, ⟨o, q, g o q⟩ :: out.2)).det g).1 = (k (g o q)).det g
    rw [OComp.det_bind]
    exact ih _
  | sample n k ih => exact ih _

/-- At a query: the entry in front of the log of what follows. -/
theorem det_withTrace_query (g : Fam S) (o : S.ι) (q : S.Dom o) (k : S.Rng o → OComp S α) :
    (OComp.query o q k).withTrace.det g =
      (((k (g o q)).withTrace.det g).1, ⟨o, q, g o q⟩ :: ((k (g o q)).withTrace.det g).2) := by
  show (((k (g o q)).withTrace.bind fun out =>
    OComp.pure (out.1, ⟨o, q, g o q⟩ :: out.2)).det g) = _
  rw [OComp.det_bind]
  rfl

/-- The log of one algorithm and then another on its value is the first's log and then the
second's. -/
theorem det_withTrace_bind {β : Type} (g : Fam S) (c : OComp S α) (k : α → OComp S β) :
    ((c.bind k).withTrace.det g).2 =
      (c.withTrace.det g).2 ++ ((k (c.det g)).withTrace.det g).2 := by
  induction c with
  | pure a => rfl
  | query o q f ih =>
    show ((OComp.query o q fun r => (f r).bind k).withTrace.det g).2 = _
    rw [det_withTrace_query, det_withTrace_query]
    exact congrArg (List.cons _) (ih _)
  | sample n f ih => exact ih _

/-- Every entry of the log holds the oracle's own answer. -/
theorem det_withTrace_ans (g : Fam S) (c : OComp S α) :
    ∀ e ∈ (c.withTrace.det g).2, e.2.2 = g e.1 e.2.1 := by
  induction c with
  | pure a => exact fun e he => absurd he (List.not_mem_nil)
  | query o q f ih =>
    intro e he
    rw [det_withTrace_query] at he
    rcases List.mem_cons.1 he with rfl | h
    · rfl
    · exact ih _ e h
  | sample n f ih => exact ih _

end

variable {lam : ℕ} {γ Sg : Type}

namespace PartO
variable (s : PartO lam γ Sg)

open Classical in
/-- **The part whose checker refuses where two strings of its own log have one answer.** All other
fields are the part's own. -/
noncomputable def guard : PartO lam γ Sg :=
  { s with chk := fun x => (s.chk x).withTrace.bind fun o =>
      OComp.pure (if NoClash o.2 then o.1 else none) }

/-- The log of the part's checker on x under g. -/
noncomputable def ownLog (g : Fam (rom lam)) (x : γ) : Trace (rom lam) :=
  ((s.chk x).withTrace.det g).2

open Classical in
/-- Its value: the checker's, if no two strings of the checker's log have one answer. -/
theorem guard_det (g : Fam (rom lam)) (x : γ) :
    (s.guard.chk x).det g = if NoClash (s.ownLog g x) then (s.chk x).det g else none := by
  show (((s.chk x).withTrace.bind fun o =>
    OComp.pure (if NoClash o.2 then o.1 else none)).det g) = _
  rw [OComp.det_bind, ← det_withTrace_fst g (s.chk x)]
  rfl

/-- It has no coins if the checker has none. -/
theorem guard_noCoin (h : ∀ x, (s.chk x).NoCoin) (x : γ) : (s.guard.chk x).NoCoin :=
  OComp.NoCoin.bind (noCoin_withTrace _ (h x)) fun _ => trivial

/-- It asks as many strings as the checker. -/
theorem guard_queryBound (tR : ℕ) (hq : ∀ x, (s.chk x).QueryBound tR) (x : γ) :
    (s.guard.chk x).QueryBound tR :=
  OComp.QueryBound.bind (t := 0) (queryBound_withTrace _ tR (hq x)) fun _ => trivial

/-- The part's event lies in the guarded part's event or in "two strings of the checker's own log
have one answer". -/
theorem lose_sub (g : Fam (rom lam)) :
    s.lose g ⊆ s.guard.lose g ∪ {x | ¬ NoClash (s.ownLog g x.1)} := by
  rintro x ⟨o, ho, hL⟩
  by_cases hc : NoClash (s.ownLog g x.1)
  · refine Or.inl ⟨o, ?_, hL⟩
    rw [guard_det, if_pos hc]
    exact ho
  · exact Or.inr hc

/-- **Two strings of the checker's own log have one answer with probability at most (t + tR)^2 /
2^lam**, for a maker with at most t queries and a checker without coins with at most tR. -/
theorem pr_ownClash (hn : ∀ x, (s.chk x).NoCoin) (tR : ℕ) (hq : ∀ x, (s.chk x).QueryBound tR)
    (A : OComp (rom lam) γ) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (fun g => {x | ¬ NoClash (s.ownLog g x.1)}) ≤
      (((t + tR) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  have h1 := Pr_twoExp_det A (fun x => (s.chk x).withTrace) (fun x => noCoin_withTrace _ (hn x))
    {z | ¬ NoClash z.2.2}
  have h2 := clash_maker A s.chk t tR hA hq
  rw [twoExp_withTrace, Rom.Pr_bind_pure] at h2
  refine le_trans (le_of_eq h1.symm) (le_trans (Rom.Pr_mono _ fun _ z hz => ?_) h2)
  exact fun hc => hz (hc.of_subset fun e he => List.mem_append_right _ he)

/-- **A part has `PartO.OK` if its guarded part has it**, with (t + tR)^2 / 2^lam more in the
bound. -/
theorem ok_of_guard (hn : ∀ x, (s.chk x).NoCoin) (tR : ℕ) (hq : ∀ x, (s.chk x).QueryBound tR)
    (h : s.guard.OK) :
    ({ s with bound := fun t => s.bound t + (((t + tR) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam } :
      PartO lam γ Sg).OK where
  rare := fun A t hA =>
    le_trans (Rom.Pr_mono _ fun g => s.lose_sub g)
      (le_trans (Pr_union_le _ _ _ (h.meas A))
        (add_le_add (h.rare A t hA) (s.pr_ownClash hn tR hq A t hA)))
  meas := fun A => s.meas_of_noCoin hn A

end PartO

end OnBytes.Slice
