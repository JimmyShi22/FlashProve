-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/AtSet.lean: a bound for all values of the random oracle at finitely many strings gives
the bound for the random oracle; in two steps, the strings of the second may depend on the values at
the first.

Why. The bounds of OnBytes/Slice/PartO.lean and JoinId.lean are for parts that are fixed before the
oracle is drawn. A checker of OnBytes/Slice/OneWorldChain.lean, and the code of typed queries
beneath it, hold digests as constants. A verifier that hashes by the oracle asks for them. The
digest of the public files is asked at a string that is fixed beforehand. The digest of a chain's
parameter bytes is not: these bytes hold the digest of the public files (the library's
`Fmt.paramsBytes`), so its string is fixed only once that value is. Two chains may have the same
parameter bytes, and so one string.

How. The oracle's values at finitely many fixed strings are independent of its values elsewhere. So
if an average is at most b with every table of values put at these strings, it is at most b
(`lintegral_le_of_over`, by induction from the library's `Rom.lintegral_U_resample`). Under the
oracle with a table put over it an algorithm runs as the algorithm runs that answers its own queries
at these strings by the table, without asking (`pinOn`), under an oracle that is uniform everywhere.
Of that run the bounds speak, at the parts that hold the table's values. In the hypothesis of that
step the table is at hand: so a second set of strings may be a function of it.

Main definitions.
 `over S T g`: the oracle g with the values of the table T put at the strings of the finite set S.
 `pinOn S T c`: the algorithm c with its queries at strings of S answered by T, without asking.
 `offSet S σ`, `offBoth S w`: a log, and an outcome with its two logs, without the entries at
     strings of S.
Main theorems.
 `over_over`, `pinOn_pinOn`: two tables, one over the other, are one table on the union of the two
     sets; at a string of both the first step's value stands.
 `lintegral_le_of_over`: see above.
 `runEager_pinOn`, `det_pinOn`, `withTrace_pinOn`, `twoExp_pinOn`: under every oracle g the
     algorithm that answers by the table runs as the algorithm does under `over S T g`; its log
     lacks the entries at strings of S.
 `queryBound_pinOn`, `noCoin_pinOn`: it asks no more, and tosses no coin if the algorithm tosses
     none.
 `Pr_twoExp_le_of_pinned`: for "a committer, then a prover" (OnBytes/Slice/OneWorld.lean: `twoExp`):
     a bound for every table, at the event under the oracle with the table put over it, is a bound
     for those that ask.
 `Pr_twoExp_le_of_pinned₂`: the same in two steps: S₀ is fixed; S₁ is a function of the table at S₀.

What is asked. For each outcome, the oracles under which it lies in the event are a measurable set:
that passes from one step to the next (`measurableSet_over`), and makes the bound one on a true
average. For an event that says where the value of an algorithm lies: `measurableSet_det`. The event
does not get lost when the entries at the strings are left out of both logs: the run that answers by
the table has no such entries.

A table is a function on all strings; `over` and `pinOn` use only its values on S. So no string
stands twice, and a checker looks its value up.

What is not claimed. A string that the maker chooses is not covered, nor one that depends on the
oracle otherwise than through the first step's values. "For every table" is more than is needed (the
proof is on an average); no use is made of that. It is not shown that any event of the join meets
the two conditions. No bound is proved here: b is a variable. Nothing on any protocol, checker,
program or hash function.

-/
import OnBytes.Slice.OneMaker

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open scoped ENNReal

variable {lam : ℕ} {α β δ : Type}

/-! ## The oracle with a table put over it -/

/-- The oracle g with the values of the table T put at the strings of S. -/
noncomputable def over (S : Finset (List Bool)) (T : List Bool → Dig lam) (g : Fam (rom lam)) :
    Fam (rom lam) :=
  fun _ s => if s ∈ S then T s else g () s

/-- At a string of S, `over S T g` has the table's value. -/
theorem over_mem {S : Finset (List Bool)} (T : List Bool → Dig lam) (g : Fam (rom lam))
    {s : List Bool} (h : s ∈ S) : over S T g () s = T s := if_pos h

/-- At another string, `over S T g` has g's value. -/
theorem over_not_mem {S : Finset (List Bool)} (T : List Bool → Dig lam) (g : Fam (rom lam))
    {s : List Bool} (h : s ∉ S) : over S T g () s = g () s := if_neg h

/-- Putting a table over the oracle is a measurable map. -/
theorem measurable_over (S : Finset (List Bool)) (T : List Bool → Dig lam) :
    Measurable (over (lam := lam) S T) := by
  refine measurable_pi_iff.2 fun o => measurable_pi_iff.2 fun s => ?_
  by_cases hs : s ∈ S
  · have e : (fun g : Fam (rom lam) => over S T g o s) = fun _ => T s :=
      funext fun g => if_pos hs
    rw [e]
    exact measurable_const
  · have e : (fun g : Fam (rom lam) => over S T g o s) = fun g => g () s :=
      funext fun g => if_neg hs
    rw [e]
    exact (measurable_pi_apply s).comp (measurable_pi_apply ())

/-- One more string: the library's `Fam.set` behind a table is a table. -/
theorem set_over (S : Finset (List Bool)) (T : List Bool → Dig lam) (g : Fam (rom lam))
    (s : List Bool) (r : Dig lam) :
    (over S T g).set () s r = over (insert s S) (fun x => if x = s then r else T x) g := by
  funext o s'
  cases o
  by_cases h : s' = s
  · subst h
    rw [Fam.set_self, over_mem _ _ (Finset.mem_insert_self _ _)]
    exact (if_pos rfl).symm
  · refine (Fam.set_of_ne_point (over S T g) () (q := s) (q' := s') h r).trans ?_
    by_cases hs : s' ∈ S
    · rw [over_mem _ _ hs, over_mem _ _ (Finset.mem_insert_of_mem hs)]
      exact (if_neg h).symm
    · rw [over_not_mem _ _ hs,
        over_not_mem _ _ (fun hh => (Finset.mem_insert.1 hh).elim h hs)]

/-- Two tables, one over the other, are one table on the union: at a string of both sets the outer
one's value stands. -/
theorem over_over (S₀ S₁ : Finset (List Bool)) (T₀ T₁ : List Bool → Dig lam)
    (g : Fam (rom lam)) :
    over S₀ T₀ (over S₁ T₁ g) = over (S₀ ∪ S₁) (fun s => if s ∈ S₀ then T₀ s else T₁ s) g := by
  funext o s
  cases o
  by_cases h0 : s ∈ S₀
  · rw [over_mem _ _ h0, over_mem _ _ (Finset.mem_union_left _ h0)]
    exact (if_pos h0).symm
  · rw [over_not_mem _ _ h0]
    by_cases h1 : s ∈ S₁
    · rw [over_mem _ _ h1, over_mem _ _ (Finset.mem_union_right _ h1)]
      exact (if_neg h0).symm
    · rw [over_not_mem _ _ h1,
        over_not_mem _ _ (fun hh => (Finset.mem_union.1 hh).elim h0 h1)]

/-- The empty table changes nothing. -/
theorem over_empty (T : List Bool → Dig lam) (g : Fam (rom lam)) : over ∅ T g = g := by
  funext o s
  cases o
  exact over_not_mem _ _ (Finset.notMem_empty s)

/-- **The average of a measurable quantity is at most b, if it is so with every table put at the
strings of S.** The oracle's values at finitely many fixed strings are independent of the rest. -/
theorem lintegral_le_of_over (S : Finset (List Bool)) :
    ∀ (F : Fam (rom lam) → ℝ≥0∞), Measurable F → ∀ b : ℝ≥0∞,
      (∀ T, ∫⁻ g, F (over S T g) ∂(U (rom lam)) ≤ b) → ∫⁻ g, F g ∂(U (rom lam)) ≤ b := by
  induction S using Finset.induction_on with
  | empty =>
    intro F _ b h
    have h0 := h fun _ => fun _ => false
    simpa only [over_empty] using h0
  | insert s S' _ ih =>
    intro F hF b h
    have hset : ∀ r : Dig lam, Measurable fun g : Fam (rom lam) => g.set () s r := fun r => by
      have e : (fun g : Fam (rom lam) => g.set () s r) =
          fun g => over (insert s ∅) (fun x => if x = s then r else r) g :=
        funext fun g => by rw [← set_over, over_empty]
      rw [e]
      exact measurable_over _ _
    rw [lintegral_U_resample () s hF]
    unfold Prob.expect
    calc ∑' r, PMF.uniformOfFintype ((rom lam).Rng ()) r *
          ∫⁻ f, F (f.set () s r) ∂(U (rom lam))
        ≤ ∑' r, PMF.uniformOfFintype ((rom lam).Rng ()) r * b :=
          ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl
            (ih (fun g => F (g.set () s r)) (hF.comp (hset r)) b fun T => by
              simp only [set_over]
              exact h _)
      _ = b := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ## The algorithm that answers by the table -/

/-- The algorithm that answers its own queries at the strings of S by the table, without asking. -/
noncomputable def pinOn (S : Finset (List Bool)) (T : List Bool → Dig lam) :
    OComp (rom lam) α → OComp (rom lam) α
  | .pure a => .pure a
  | .query () s k => if s ∈ S then pinOn S T (k (T s)) else .query () s fun r => pinOn S T (k r)
  | .sample n k => .sample n fun r => pinOn S T (k r)

/-- `pinOn` at a query at a string of S. -/
theorem pinOn_query_mem {S : Finset (List Bool)} (T : List Bool → Dig lam) {s : List Bool}
    (h : s ∈ S) (k : Dig lam → OComp (rom lam) α) :
    pinOn S T (OComp.query (S := rom lam) () s k) = pinOn S T (k (T s)) := by
  simp only [pinOn]
  exact if_pos h

/-- `pinOn` at a query at another string. -/
theorem pinOn_query_not_mem {S : Finset (List Bool)} (T : List Bool → Dig lam) {s : List Bool}
    (h : s ∉ S) (k : Dig lam → OComp (rom lam) α) :
    pinOn S T (OComp.query (S := rom lam) () s k) =
      OComp.query (S := rom lam) () s fun r => pinOn S T (k r) := by
  simp only [pinOn]
  exact if_neg h

/-- Answering by two tables, one after the other, is answering by one table on the union: at a
string of both sets the inner one's value stands. -/
theorem pinOn_pinOn (S₀ S₁ : Finset (List Bool)) (T₀ T₁ : List Bool → Dig lam)
    (c : OComp (rom lam) α) :
    pinOn S₁ T₁ (pinOn S₀ T₀ c) =
      pinOn (S₀ ∪ S₁) (fun s => if s ∈ S₀ then T₀ s else T₁ s) c := by
  induction c with
  | pure a => rfl
  | query o s k ih =>
    cases o
    have key : ∀ (s' : List Bool) (k' : Dig lam → OComp (rom lam) α),
        (∀ r, pinOn S₁ T₁ (pinOn S₀ T₀ (k' r)) =
          pinOn (S₀ ∪ S₁) (fun s => if s ∈ S₀ then T₀ s else T₁ s) (k' r)) →
        pinOn S₁ T₁ (pinOn S₀ T₀ (OComp.query (S := rom lam) () s' k')) =
          pinOn (S₀ ∪ S₁) (fun s => if s ∈ S₀ then T₀ s else T₁ s)
            (OComp.query (S := rom lam) () s' k') := by
      intro s' k' ih'
      by_cases h0 : s' ∈ S₀
      · rw [pinOn_query_mem T₀ h0, pinOn_query_mem _ (Finset.mem_union_left S₁ h0), ih', if_pos h0]
      · by_cases h1 : s' ∈ S₁
        · rw [pinOn_query_not_mem T₀ h0, pinOn_query_mem T₁ h1,
            pinOn_query_mem _ (Finset.mem_union_right S₀ h1), ih', if_neg h0]
        · have hu : s' ∉ S₀ ∪ S₁ := fun hh => (Finset.mem_union.1 hh).elim h0 h1
          rw [pinOn_query_not_mem T₀ h0, pinOn_query_not_mem T₁ h1, pinOn_query_not_mem _ hu]
          exact congrArg _ (funext fun r => ih' r)
    exact key s k ih
  | sample n k ih =>
    simp only [pinOn]
    exact congrArg _ (funext fun r => ih r)

/-- Under every oracle g, `pinOn S T c` runs as c runs under g with the table put over it. Not used
by the join, which needs the logs too (`withTrace_pinOn`). -/
theorem runEager_pinOn (S : Finset (List Bool)) (T : List Bool → Dig lam) (g : Fam (rom lam))
    (c : OComp (rom lam) α) : (pinOn S T c).runEager g = c.runEager (over S T g) := by
  induction c with
  | pure a => rfl
  | query o s k ih =>
    cases o
    by_cases hs : s ∈ S
    · simp only [pinOn, if_pos hs, OComp.runEager, over_mem T g hs]
      exact ih _
    · simp only [pinOn, if_neg hs, OComp.runEager, over_not_mem T g hs]
      exact ih _
  | sample n k ih => simp only [pinOn, OComp.runEager, ih]

/-- The one value of `pinOn S T c` under g, in the run in which every coin toss yields 0, is that of
c under g with the table put over it. -/
theorem det_pinOn (S : Finset (List Bool)) (T : List Bool → Dig lam) (g : Fam (rom lam))
    (c : OComp (rom lam) α) : (pinOn S T c).det g = c.det (over S T g) := by
  induction c with
  | pure a => rfl
  | query o s k ih =>
    cases o
    by_cases hs : s ∈ S
    · simp only [pinOn, if_pos hs, OComp.det, over_mem T g hs]
      exact ih _
    · simp only [pinOn, if_neg hs, OComp.det, over_not_mem T g hs]
      exact ih _
  | sample n k ih => simp only [pinOn, OComp.det, ih]

/-- `pinOn S T c` asks no more than c. -/
theorem queryBound_pinOn (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (c : OComp (rom lam) α) : ∀ t, c.QueryBound t → (pinOn S T c).QueryBound t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | query o s k ih =>
    cases o
    intro t h
    cases t with
    | zero => exact h.elim
    | succ t =>
      by_cases hs : s ∈ S
      · simp only [pinOn, if_pos hs]
        exact (ih _ t (h _)).mono (Nat.le_succ t)
      · simp only [pinOn, if_neg hs]
        exact fun r => ih r t (h r)
  | sample n k ih => exact fun t h r => ih r t (h r)

/-- `pinOn S T c` tosses no coin if c tosses none. -/
theorem noCoin_pinOn (S : Finset (List Bool)) (T : List Bool → Dig lam) (c : OComp (rom lam) α)
    (h : c.NoCoin) : (pinOn S T c).NoCoin := by
  induction c with
  | pure a => trivial
  | query o s k ih =>
    cases o
    by_cases hs : s ∈ S
    · simp only [pinOn, if_pos hs]
      exact ih _ (h _)
    · simp only [pinOn, if_neg hs]
      exact fun r => ih r (h r)
  | sample n k _ => exact h.elim

/-- The entries of a log at strings outside S. -/
noncomputable def offSet (S : Finset (List Bool)) (σ : Trace (rom lam)) : Trace (rom lam) :=
  σ.filter fun e => decide ((e.2.1 : List Bool) ∉ S)

/-- The log of `pinOn S T c` under g is the log of c under g with the table put over it, without the
entries at strings of S. -/
theorem withTrace_pinOn (S : Finset (List Bool)) (T : List Bool → Dig lam) (g : Fam (rom lam))
    (c : OComp (rom lam) α) :
    (pinOn S T c).withTrace.runEager g =
      (c.withTrace.runEager (over S T g)).map fun o => (o.1, offSet S o.2) := by
  induction c with
  | pure a => simp [pinOn, OComp.withTrace, OComp.runEager, PMF.pure_map, offSet]
  | query o s k ih =>
    cases o
    by_cases hs : s ∈ S
    · simp only [pinOn, if_pos hs, OComp.withTrace, OComp.runEager, over_mem T g hs,
        OComp.runEager_bind, PMF.map_bind, PMF.pure_map]
      rw [ih _, ← PMF.bind_pure_comp]
      refine congrArg _ (funext fun out => ?_)
      simp [offSet, hs]
    · simp only [pinOn, if_neg hs, OComp.withTrace, OComp.runEager, over_not_mem T g hs,
        OComp.runEager_bind, PMF.map_bind, PMF.pure_map]
      rw [ih (g () s), PMF.bind_map]
      refine congrArg _ (funext fun out => ?_)
      simp [offSet, hs]
  | sample n k ih =>
    simp only [pinOn, OComp.withTrace, OComp.runEager, PMF.map_bind, ih]

/-! ## A committer, then a prover -/

/-- An outcome of "a committer, then a prover", with the entries at strings of S left out of both
logs. -/
noncomputable def offBoth (S : Finset (List Bool))
    (w : ((β × Trace (rom lam)) × δ) × Trace (rom lam)) :
    ((β × Trace (rom lam)) × δ) × Trace (rom lam) :=
  (((w.1.1.1, offSet S w.1.1.2), w.1.2), offSet S w.2)

/-- The committer and the prover that answer by the table run, under every oracle g, as the
committer and the prover run under g with the table put over it; their logs lack the entries at
strings of S. -/
theorem twoExp_pinOn (S : Finset (List Bool)) (T : List Bool → Dig lam) (g : Fam (rom lam))
    (C : OComp (rom lam) β) (P : β → OComp (rom lam) δ) :
    (twoExp (pinOn S T C) fun x => pinOn S T (P x)).withTrace.runEager g =
      ((twoExp C P).withTrace.runEager (over S T g)).map (offBoth S) := by
  rw [twoExp_withTrace, twoExp_withTrace]
  unfold bothExp
  simp only [OComp.runEager_bind, OComp.runEager, withTrace_pinOn, PMF.map_bind, PMF.bind_map,
    PMF.pure_map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  refine congrArg _ (funext fun x => congrArg _ (funext fun y => ?_))
  simp [offBoth, offSet, List.filter_append]

/-- **A bound for every committer and prover that answer by a table is a bound for those that ask.**
E is an event on the outcome of "a committer C, then a prover P", which may depend on the oracle,
and so on its values at the strings of the fixed finite set S. Asked: for each outcome the oracles
under which it lies in E are a measurable set; the event does not get lost when the entries at
strings of S are left out of both logs; and, for every table T, the committer and the prover that
answer their own queries at strings of S by T bring the event about, at the oracle with T put over
it, with probability at most b. Then C and P bring it about with probability at most b. By `hm` that
probability is a true average. -/
theorem Pr_twoExp_le_of_pinned (S : Finset (List Bool)) (C : OComp (rom lam) β)
    (P : β → OComp (rom lam) δ)
    (E : Fam (rom lam) → Set (((β × Trace (rom lam)) × δ) × Trace (rom lam))) (b : ℝ≥0∞)
    (hm : ∀ w, MeasurableSet {g | w ∈ E g}) (hoff : ∀ g w, w ∈ E g → offBoth S w ∈ E g)
    (h : ∀ T, Rom.Pr (twoExp (pinOn S T C) fun x => pinOn S T (P x)).withTrace
      (fun g => E (over S T g)) ≤ b) :
    Rom.Pr (twoExp C P).withTrace E ≤ b := by
  refine lintegral_le_of_over S _ (measurable_PrCoins_dep _ E hm) b fun T => le_trans ?_ (h T)
  unfold Rom.Pr
  refine lintegral_mono fun g => ?_
  unfold PrCoins
  rw [twoExp_pinOn, pr_map]
  exact pr_mono _ fun w hw => hoff _ w hw

/-- The oracles under which an algorithm's one value, in the run in which every coin toss yields 0,
lies in A are a measurable set. -/
theorem measurableSet_det {S : OSpec} {γ : Type} (c : OComp S γ) (A : Set γ) :
    MeasurableSet {g : Fam S | c.det g ∈ A} := by
  induction c with
  | pure a => by_cases h : a ∈ A <;> simp [OComp.det, h]
  | query o q k ih =>
    have e : {g : Fam S | (OComp.query o q k).det g ∈ A} =
        ⋃ r : S.Rng o, ({g : Fam S | g o q = r} ∩ {g : Fam S | (k r).det g ∈ A}) := by
      ext g
      simp [OComp.det]
    rw [e]
    refine MeasurableSet.iUnion fun r => MeasurableSet.inter ?_ (ih r)
    have hev : Measurable fun g : Fam S => g o q :=
      (measurable_pi_apply q).comp (measurable_pi_apply o)
    exact hev (MeasurableSet.singleton r)
  | sample n k ih => exact ih 0

/-- The condition on measurability passes to the event under the oracle with a table put over
it. -/
theorem measurableSet_over {γ : Type} (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (E : Fam (rom lam) → Set γ) (hm : ∀ w, MeasurableSet {g | w ∈ E g}) (w : γ) :
    MeasurableSet {g | w ∈ E (over S T g)} :=
  measurable_over S T (hm w)

/-- **The same in two steps: the strings of the second step may depend on the values at the first.**
S₀ is fixed; S₁ T₀ is the second set, given the table T₀ at the first. At a string that lies in
both, the first step's value stands. Asked: the condition on measurability; that the event does not
get lost when the entries at S₀, or at S₁ T₀ for any T₀, are left out of both logs; and the bound
for every pair of tables. -/
theorem Pr_twoExp_le_of_pinned₂ (S₀ : Finset (List Bool))
    (S₁ : (List Bool → Dig lam) → Finset (List Bool)) (C : OComp (rom lam) β)
    (P : β → OComp (rom lam) δ)
    (E : Fam (rom lam) → Set (((β × Trace (rom lam)) × δ) × Trace (rom lam))) (b : ℝ≥0∞)
    (hm : ∀ w, MeasurableSet {g | w ∈ E g}) (hoff₀ : ∀ g w, w ∈ E g → offBoth S₀ w ∈ E g)
    (hoff₁ : ∀ T₀ g w, w ∈ E g → offBoth (S₁ T₀) w ∈ E g)
    (h : ∀ T₀ T₁, Rom.Pr (twoExp (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ C))
        fun x => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P x))).withTrace
      (fun g => E (over S₀ T₀ (over (S₁ T₀) T₁ g))) ≤ b) :
    Rom.Pr (twoExp C P).withTrace E ≤ b :=
  Pr_twoExp_le_of_pinned S₀ C P E b hm hoff₀ fun T₀ =>
    Pr_twoExp_le_of_pinned (S₁ T₀) (pinOn S₀ T₀ C) (fun x => pinOn S₀ T₀ (P x))
      (fun g => E (over S₀ T₀ g)) b (measurableSet_over S₀ T₀ E hm)
      (fun _ w hw => hoff₁ T₀ _ w hw) (h T₀)

end OnBytes.Slice
