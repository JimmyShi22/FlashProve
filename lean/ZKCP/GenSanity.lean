-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  ZKCP/GenSanity.lean -- the definitions of Gen.lean can be met, and the clauses they add can fail.

  Instances are numbers; R_yes = "x is even", R_no = "anything". There is one index, so nothing is
  said here about hiding an index (Sanity.lean, HashToy.lean and Separation.lean do that for
  Defs.lean), and no scheme here queries an oracle itself. What is tested is what Gen.lean adds. All
  results hold for every family S of oracles. G2 and G3 are the labels in the header of
  ZKCP/Gen.lean.
    quiet_isZKCPArgWith   quiet (empty proofs, V accepts) meets Gen's definition at B = 2 with
                          errors 0, 0, 0; for a batch the simulator is given only the instances of
                          the adversary's own slots, and answers for all oracles of the family.
    nosy_not_private      (G3) nosy puts the instances of the whole batch into every proof. It fails
                          privacy at B = 2: ζ(0, 1) ≥ 1/2. So a proof of an own slot that leaks a
                          neighbour's instance is excluded, in this sense:
                          `HasIndexPrivacyWith Ryn (nosy S) 2 Sim ζ` gives 1 ≤ ζ 0 1 + ζ 0 1.
    quiet_not_binding_yy  (G2) for R_no := R_yes the same quiet fails binding: ε(0, 0) ≥ 1. So it
                          matters which relation binding speaks of.
  Notation: ε(tC, tP): a function ℕ → ℕ → ℝ≥0∞, the `ε` of `HasIndexBinding`, handed on to
  `HasIndexBindingWith` (ZKCP/Gen.lean), where `Ct.QueryBound tC` and `(Pt st).QueryBound tP`.
-/
import ZKCP.Gen
import Rom.EagerLazy
import Rom.World
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal

namespace ZKCP.Gen.Sanity

open Rom (OSpec)
open Prob (pr sd expect)

/-- R_yes: x is even.  R_no: anything. -/
def Ryn : RelPair Unit ℕ Unit Unit :=
  ⟨fun _ x _ => x % 2 = 0, fun _ _ _ => True, fun _ _ _ _ => trivial, fun _ => ()⟩

/-- R_yes = R_no: x is even. -/
def Ryy : RelPair Unit ℕ Unit Unit :=
  ⟨fun _ x _ => x % 2 = 0, fun _ x _ => x % 2 = 0, fun _ _ _ h => h, fun _ => ()⟩

variable (S : OSpec)

/-- Empty keys, empty proofs, V accepts everything. -/
def quiet : Arg S Unit ℕ Unit Unit Unit Unit where
  C _ := .pure ((), ())
  P _ b := .pure ⟨b.map fun _ => (), by simp⟩
  V _ _ _ := .pure true

/-- As quiet, but every proof is the list of all instances of the batch. -/
def nosy : Arg S Unit ℕ Unit Unit Unit (List ℕ) where
  C _ := .pure ((), ())
  P _ b := .pure ⟨b.map fun _ => b.map Prod.fst, by simp⟩
  V _ _ _ := .pure true

def ext : Extractor S Unit ℕ Unit Unit Unit := ⟨fun _ _ => some (), fun _ _ _ _ _ => ()⟩

/-- The simulator: lazily sampled oracles (its state is the table), and an empty proof for each
instance that it is given. -/
@[reducible] def sim : Simulator S Unit Unit ℕ Unit where
  St := Rom.Table S
  init _ _ := PMF.pure ((), Rom.Table.empty S)
  answer T o q := Rom.lazyAnswer T o q
  prove T xs := PMF.pure (⟨xs.map fun _ => (), by simp⟩, T)

variable {S}

/-! ### Small facts -/

theorem Pr_pure {α : Type} (a : α) (T : Set α) [Decidable (a ∈ T)] :
    Rom.Pr (.pure a : Rom.OComp S α) (fun _ => T) = if a ∈ T then 1 else 0 := by
  classical
  simp only [Rom.Pr, Rom.PrCoins, Rom.OComp.runEager, Prob.pr_pure, MeasureTheory.lintegral_const,
    MeasureTheory.measure_univ, mul_one]
  congr

theorem PrCoins_bind_zero {α β : Type} (f : Rom.Fam S) (c : Rom.OComp S α) (g : α → Rom.OComp S β)
    (E : Set β) (h : ∀ a, Rom.PrCoins f (g a) E = 0) :
    Rom.PrCoins f (c.bind g) E = 0 := by
  unfold Rom.PrCoins at h ⊢
  rw [Rom.OComp.runEager_bind, Prob.pr_bind]
  simp only [h, Prob.expect_zero]

theorem set_of_mem {T : Rom.Table S} {o : S.ι} {q : S.Dom o} (hq : T o q = none) (r : S.Rng o)
    {o' : S.ι} {q' : S.Dom o'} {r' : S.Rng o'} (h : T o' q' = some r') :
    T.set o q r o' q' = some r' := by
  unfold Rom.Table.set
  by_cases ho : o' = o
  · subst ho
    rw [Function.update_self]
    by_cases hqq : q' = q
    · subst hqq; rw [hq] at h; simp at h
    · rw [Function.update_of_ne hqq]; exact h
  · rw [Function.update_of_ne ho]; exact h

/-- For empty proofs, what a batch releases is what the simulator makes from the own instances
alone. -/
theorem released_quiet (b : Batch ℕ Unit) :
    b.released (b.pairs.map fun _ => ()) = b.ownX.zip (b.ownX.map fun _ => ()) := by
  induction b with
  | nil => rfl
  | cons s rest ih =>
    simp only [Batch.released, Batch.pairs, Batch.ownX, List.map_map] at ih ⊢
    cases hs : s.2.2 <;> simp [hs, ih]

/-! ### The positive check -/

theorem verifyAll_quiet (l : List (ℕ × Unit)) : verifyAll (quiet S) () l = .pure true := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    have e : verifyAll (quiet S) () (s :: rest) = ((quiet S).V () s.1 s.2).bind fun c =>
        (verifyAll (quiet S) () rest).bind fun cs => .pure (c && cs) := rfl
    rw [e, ih]; rfl

/-- The real loop under lazy sampling from the table T is the ideal loop with the simulator's table
T (for `quiet S` and `sim S`). -/
theorem loops_agree (Z : ViewEnv S Unit ℕ Unit Unit) (V : AdvVerifier S ℕ Unit) :
    ∀ (n : ℕ) (v : View S Unit ℕ Unit) (T : Rom.Table S),
      ((realLoop (quiet S) Z () V n v).runLazy T).map Prod.fst = idealLoop (sim S) Z V n v T := by
  induction V with
  | halt => intro n v T; simp only [realLoop, idealLoop]; exact PMF.pure_map _ _
  | query o q k ih =>
    intro n v T
    simp only [realLoop, idealLoop, Rom.OComp.runLazy]
    unfold Rom.lazyAnswer
    cases h : T o q with
    | some r => simp only [ih, PMF.pure_bind]
    | none =>
      simp only [PMF.map_bind, ih, PMF.bind_map]
      rfl
  | sample m k ih =>
    intro n v T
    simp only [realLoop, idealLoop, Rom.OComp.runLazy, PMF.map_bind, ih]
  | request k ih =>
    intro n v T
    cases n with
    | zero => simp only [realLoop, idealLoop]; exact PMF.pure_map _ _
    | succ n =>
      cases hz : Z v with
      | none => simp only [realLoop, idealLoop, hz]; exact PMF.pure_map _ _
      | some b =>
        have hP : (quiet S).P () b.pairs = .pure ⟨b.pairs.map fun _ => (), by simp⟩ := rfl
        simp only [realLoop, idealLoop, hz]
        rw [hP]
        simp only [Rom.OComp.bind, released_quiet, ih, PMF.pure_bind]

theorem ideal_consistent (Z : ViewEnv S Unit ℕ Unit Unit) (V : AdvVerifier S ℕ Unit) :
    ∀ (n : ℕ) (v : View S Unit ℕ Unit) (T : Rom.Table S),
      (∀ (o : S.ι) (q : S.Dom o) (r : S.Rng o), (⟨o, q, r⟩ : Rom.QA S) ∈ v.trace → T o q = some r) →
      pr (idealLoop (sim S) Z V n v T) {v | ¬ TraceConsistent v.trace} = 0 := by
  classical
  have hpure : ∀ (v : View S Unit ℕ Unit) (T : Rom.Table S),
      (∀ (o : S.ι) (q : S.Dom o) (r : S.Rng o), (⟨o, q, r⟩ : Rom.QA S) ∈ v.trace → T o q = some r) →
      pr (PMF.pure v) {v : View S Unit ℕ Unit | ¬ TraceConsistent v.trace} = 0 := by
    intro v T hT
    rw [Prob.pr_pure, if_neg]
    simp only [Set.mem_setOf_eq, not_not]
    intro o q r r' h h'
    exact Option.some.inj ((hT o q r h).symm.trans (hT o q r' h'))
  induction V with
  | halt => intro n v T hT; simp only [idealLoop]; exact hpure v T hT
  | query o q k ih =>
    intro n v T hT
    simp only [idealLoop, Prob.pr_bind]
    unfold Rom.lazyAnswer
    cases hq : T o q with
    | some r =>
      refine (Prob.expect_pure _ _).trans ?_
      refine ih _ _ _ _ fun o' q' r' h => ?_
      rcases List.mem_append.mp h with h | h
      · exact hT o' q' r' h
      · simp only [List.mem_singleton] at h
        cases h; exact hq
    | none =>
      refine (Prob.expect_map _ _ _).trans ?_
      have : ∀ r : S.Rng o,
          pr (idealLoop (sim S) Z (k r) n { v with trace := v.trace ++ [⟨o, q, r⟩] } (T.set o q r))
              {v | ¬ TraceConsistent v.trace} = 0 := by
        intro r
        refine ih _ _ _ _ fun o' q' r' h => ?_
        rcases List.mem_append.mp h with h | h
        · exact set_of_mem hq r (hT o' q' r' h)
        · simp only [List.mem_singleton] at h
          cases h; exact Rom.Table.set_self T o q r
      exact (Prob.expect_congr _ this).trans (Prob.expect_zero _)
  | sample m k ih =>
    intro n v T hT
    simp only [idealLoop, Prob.pr_bind]
    have : ∀ r : Fin (m + 1),
        pr (idealLoop (sim S) Z (k r) n { v with coins := v.coins ++ [r.val] } T)
            {v | ¬ TraceConsistent v.trace} = 0 := by
      intro r
      refine ih r _ _ _ ?_
      exact hT
    exact (Prob.expect_congr _ this).trans (Prob.expect_zero _)
  | request k ih =>
    intro n v T hT
    cases n with
    | zero => simp only [idealLoop]; exact hpure v T hT
    | succ n =>
      cases hz : Z v with
      | none => simp only [idealLoop, hz]; exact hpure v T hT
      | some b =>
        simp only [idealLoop, hz, PMF.pure_bind]
        refine ih _ _ _ _ ?_
        exact hT

variable (S)

/-- Positive check: quiet meets Gen's definition for `Ryn` at B = 2, for every family of oracles,
with all errors 0. -/
theorem quiet_isZKCPArgWith :
    IsZKCPArgWith Ryn (quiet S) 2 (ext S) (sim S) 0 (fun _ _ => 0) (fun _ _ => 0) where
  completeness := by
    classical
    intro i b _
    have e : completenessExp (quiet S) i b =
        verifyAll (quiet S) () ((b.map Prod.fst).zip (b.map fun _ => ())) := rfl
    rw [e, verifyAll_quiet, Pr_pure]
    simp
  indexBinding := by
    classical
    intro tC tP St Ct Pt _ _
    have h0 : ∀ f, Rom.PrCoins f (bindingExp (quiet S) (ext S) Ct Pt) (bindingBad Ryn) = 0 := by
      intro f
      refine PrCoins_bind_zero f _ _ _ fun p => PrCoins_bind_zero f _ _ _ fun p' => ?_
      show pr (PMF.pure _) _ = 0
      rw [Prob.pr_pure, if_neg]
      rintro ⟨_, h | h⟩
      · exact h ⟨(), trivial⟩
      · exact h trivial
    simp [Rom.Pr, h0]
  indexPrivacy := by
    intro i Z _ tV Vt N _
    have hI : idealExp Ryn (sim S) Vt Z i N =
        idealLoop (sim S) Z (Vt ()) N ⟨(), [], [], []⟩ (Rom.Table.empty S) :=
      PMF.pure_bind _ _
    constructor
    · refine le_of_eq (Prob.sd_eq_zero_of_forall_eq fun T => ?_)
      have e : realExp (quiet S) Vt Z i N = realLoop (quiet S) Z () (Vt ()) N ⟨(), [], [], []⟩ :=
        rfl
      rw [Rom.Pr_eq_PrFrom, Rom.PrFrom_eq_lazy, e, loops_agree, hI]
    · rw [hI]
      exact ideal_consistent Z (Vt ()) N _ _ (by simp)

/-! ### The negative checks -/

/-- The adversary owns the first slot, with instance 0; the second slot, with instance a, is another
client's. -/
def envA (a : ℕ) : ViewEnv S Unit ℕ Unit (List ℕ) := fun _ => some [(0, (), true), (a, (), false)]

/-- Negative check (batches: G3 in the header of ZKCP/Gen.lean): a proof of an own slot that shows a
neighbour's instance is excluded, in this sense: `HasIndexPrivacyWith Ryn (nosy S) 2 Sim ζ` gives
1 ≤ ζ 0 1 + ζ 0 1.
Whatever the simulator, ζ(0, 1) ≥ 1/2, for an adversary that makes no query and requests one
batch. -/
theorem nosy_not_private (Sim : Simulator S Unit Unit ℕ (List ℕ)) (ζ : ℕ → ℕ → ℝ≥0∞)
    (h : HasIndexPrivacyWith Ryn (nosy S) 2 Sim ζ) : 1 ≤ ζ 0 1 + ζ 0 1 := by
  classical
  let Vt : Unit → AdvVerifier S ℕ (List ℕ) := fun _ => .request fun _ => .halt
  have hb : ∀ ivk, (Vt ivk).QueryBound 0 := fun _ _ => trivial
  have hv : ∀ a, a % 2 = 0 → (envA S a).IsValid Ryn 2 () := by
    intro a ha v b hbv
    simp only [envA, Option.some.injEq] at hbv
    subst hbv
    refine ⟨by simp [Batch.pairs], ?_⟩
    intro xw hxw
    simp only [Batch.pairs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hxw
    rcases hxw with rfl | rfl
    · rfl
    · exact ha
  let T : Set (View S Unit ℕ (List ℕ)) := {v | v.sessions = [[(0, [0, 2])]]}
  have hr : ∀ a,
      Rom.Pr (realExp (nosy S) Vt (envA S a) () 1) (fun _ => T) = if a = 2 then 1 else 0 := by
    intro a
    have e : realExp (nosy S) Vt (envA S a) () 1 = .pure ⟨(), [[(0, [0, a])]], [], []⟩ := rfl
    rw [e, Pr_pure]
    simp [T]
  have hid : idealExp Ryn Sim Vt (envA S 2) () 1 = idealExp Ryn Sim Vt (envA S 4) () 1 := rfl
  have h1 := (Prob.sd_le_iff.1 (h () (envA S 2) (hv 2 rfl) 0 Vt 1 hb).1 T).1
  have h2 := (Prob.sd_le_iff.1 (h () (envA S 4) (hv 4 rfl) 0 Vt 1 hb).1 T).2
  have hr2 : Rom.Pr (realExp (nosy S) Vt (envA S 2) () 1) (fun _ => T) = 1 := by rw [hr]; rfl
  have hr4 : Rom.Pr (realExp (nosy S) Vt (envA S 4) () 1) (fun _ => T) = 0 := by rw [hr]; rfl
  rw [hr2] at h1
  rw [hr4, ← hid, zero_add] at h2
  exact h1.trans (add_le_add h2 le_rfl)

/-- Negative check (two relations: G2 in the header of ZKCP/Gen.lean): if binding had to hold for
R_yes, quiet would fail: whatever the extractor, ε(0, 0) ≥ 1. -/
theorem quiet_not_binding_yy (ε : ℕ → ℕ → ℝ≥0∞) (h : HasIndexBinding Ryy (quiet S) ε) :
    1 ≤ ε 0 0 := by
  classical
  obtain ⟨E, hE⟩ := h
  have h0 := hE 0 0 Unit (.pure ((), ())) (fun _ => .pure (1, ())) trivial (fun _ => trivial)
  have e : bindingExp (quiet S) E (St := Unit) (.pure ((), ())) (fun _ => .pure (1, ()))
      = .pure ⟨true, E.Ei () [], 1, E.Ew () [] 1 () []⟩ := rfl
  have hbad : (⟨true, E.Ei () [], 1, E.Ew () [] 1 () []⟩ : BindingOutcome Unit ℕ Unit) ∈
      bindingBad Ryy := by
    refine ⟨rfl, Or.inl ?_⟩
    cases E.Ei () [] with
    | none => exact fun h => h
    | some i => rintro ⟨w, hw⟩; simp [Ryy] at hw
  rw [e, Pr_pure, if_pos hbad] at h0
  exact h0

end ZKCP.Gen.Sanity
