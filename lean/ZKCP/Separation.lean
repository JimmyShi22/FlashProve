-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  ZKCP/Separation.lean -- the formula of `Env` (ZKCP/Defs.lean) asks strictly less than its
  words.

  The formula of `Env` gives the environment only Z(i, x_1, π_1, ..., x_{j-1}, π_{j-1});
  its words (Z chooses from what has happened so far) ask more. Formula and words are after the
  work that this protocol builds on (lean/CREDITS.md, "Further work"); its prose says [after that
  work: that Z chooses after it has seen earlier proofs and what the adversary did, and that it
  stands for an adversarial client who chooses, as it goes, what to ask of the hidden index].
  This file exhibits one scheme, leaky, that
    (1) is a ZK-CP-ARG by the definitions of ZKCP/Defs.lean (IsZKCPArg), with errors 0, 0 and
        ζ(t_V, N) = N / 2^λ   (leaky_isZKCPArg);
    (2) hands the index to a client who makes one oracle query and whose view the environment sees:
        no
        simulator gives it strong index privacy with ζ(1, 1) < 1/2   (leaky_not_strong).

  The scheme.  The index is one secret bit i; every instance (a λ-bit string) is in every L(i).
  C(i) asks y := f(ε) and keeps isk = (i, y); ivk is empty. P puts i into the proof if x = y. V
  accepts everything.
  An environment that cannot see f names x = y with probability at most N / 2^λ. A client can
  compute y = f(ε).
-/
import ZKCP.Lemmas
noncomputable section -- Lean tags what it cannot compile

open MeasureTheory
open scoped ENNReal

namespace ZKCP.Separation

variable (lam : ℕ)

/-- Every instance is in every language; the public parameters say nothing. -/
def Rall : IndexedRelation Bool (Digest lam) Unit Unit := ⟨fun _ _ _ => True, fun _ => ()⟩

/-- The scheme with a trapdoor instance. -/
def leaky : Arg lam Bool (Digest lam) Unit Unit (Bool × Digest lam) (Option Bool) where
  C i := .query [] fun y => .pure ((), (i, y))
  P isk x _ := .pure (if x = isk.2 then some isk.1 else none)
  V _ _ _ := .pure true

/-! ### Part 1: leaky meets the definitions of ZKCP/Defs.lean -/

/-- The extractor: any index will do, since every instance is in every language. -/
def ext : Extractor lam Bool (Digest lam) Unit Unit (Option Bool) :=
  ⟨fun _ _ => some false, fun _ _ _ _ _ => ()⟩

/-- The simulator: a lazily sampled oracle (its state is the table), with f(ε) sampled at the start;
every proof is
"none". -/
def sim : Simulator lam Unit Unit (Digest lam) (Option Bool) where
  St := Cache lam
  init _ _ := (PMF.uniformOfFintype (Digest lam)).map fun y =>
    ((), Function.update (fun _ => none) [] (some y))
  answer c q := lazyAnswer c q
  prove c _ := PMF.pure (none, c)

variable {lam}

abbrev LView (lam : ℕ) : Type := View lam Unit (Digest lam) (Option Bool)
abbrev LEnv (lam : ℕ) : Type := Env Bool (Digest lam) Unit (Option Bool)
abbrev LAdv (lam : ℕ) : Type := AdvVerifier lam (Digest lam) (Option Bool)

/-- The instances that Z names in the next n sessions after a given history, if every proof from
now on is "none". -/
def futureX (Z : LEnv lam) (i : Bool) : ℕ → List (Digest lam × Option Bool) → List (Digest lam)
  | 0, _ => []
  | n + 1, h => (Z i h).1 :: futureX Z i n (h ++ [((Z i h).1, none)])

theorem length_futureX (Z : LEnv lam) (i : Bool) : ∀ n h, (futureX Z i n h).length = n := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih => intro h; simp [futureX, ih]

/-- As long as the trapdoor y is not among the instances to come, the real loop (oracle sampled
lazily from the table
c) and the ideal loop (simulator's table c) have the same law. -/
theorem loops_agree (Z : LEnv lam) (i : Bool) (y : Digest lam)
    (E : Set (LView lam)) (V : LAdv lam) :
    ∀ (n : ℕ) (v : LView lam) (c : Cache lam), y ∉ futureX Z i n v.sessions →
      PrFrom c (realLoop (leaky lam) (Z.onView i) (i, y) V n v) E =
        prob (idealLoop (sim lam) (Z.onView i) V n v c) E := by
  induction V with
  | halt => intro n v c _; simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure]
  | query q k ih =>
    intro n v c hy
    simp only [realLoop, idealLoop, PrFrom_query, prob_bind, sim]
    exact expect_congr _ fun out => ih _ _ _ _ hy
  | sample m k ih =>
    intro n v c hy
    simp only [realLoop, idealLoop, PrFrom_sample, prob_bind]
    exact expect_congr _ fun r => ih _ _ _ _ hy
  | request k ih =>
    intro n v c hy
    cases n with
    | zero => simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure]
    | succ n =>
      simp only [futureX, List.mem_cons, not_or] at hy
      have hne : (Z i v.sessions).1 ≠ y := fun e => hy.1 e.symm
      simp only [realLoop, idealLoop, Env.onView, leaky, OComp.bind, hne,
        if_false, sim, PMF.pure_bind]
      exact ih _ _ _ _ _ hy.2

/-- If two families agree outside a finite set S and the first is at most 1, the average of the
first is at most that of the second plus |S| / 2^λ. -/
theorem avg_le_of_agree (S : Finset (Digest lam)) (a b : Digest lam → ℝ≥0∞) (ha : ∀ y, a y ≤ 1)
    (hab : ∀ y, y ∉ S → a y = b y) :
    expect (PMF.uniformOfFintype (Digest lam)) a
      ≤ expect (PMF.uniformOfFintype (Digest lam)) b + S.card / 2 ^ lam := by
  classical
  have h : ∀ y, a y ≤ b y + (if y ∈ S then 1 else 0) := by
    intro y
    by_cases hy : y ∈ S
    · simp only [hy, if_true]; exact (ha y).trans le_add_self
    · simp only [hy, if_false, add_zero]; exact le_of_eq (hab y hy)
  refine (expect_mono _ h).trans ?_
  rw [expect_add]
  refine add_le_add le_rfl (le_of_eq ?_)
  rw [expect_uniform, ← Finset.mul_sum, Finset.sum_boole, mul_comm, div_eq_mul_inv]
  congr 1
  · congr 2; ext y; simp
  · simp

/-- Under the hypotheses below, the simulator's answers agree with its table, so the ideal trace
is consistent. -/
theorem ideal_consistent (Z : LEnv lam) (i : Bool) (V : LAdv lam) :
    ∀ (n : ℕ) (v : LView lam) (c : Cache lam), (∀ q r, (q, r) ∈ v.trace → c q = some r) →
      prob (idealLoop (sim lam) (Z.onView i) V n v c) {v | ¬ v.trace.Consistent} = 0 := by
  classical
  have hpure : ∀ (v : LView lam) (c : Cache lam), (∀ q r, (q, r) ∈ v.trace → c q = some r) →
      prob (PMF.pure v) {v : LView lam | ¬ v.trace.Consistent} = 0 := by
    intro v c hc
    rw [prob_pure, if_neg]
    simp only [Set.mem_setOf_eq, not_not]
    intro q r r' h h'
    have := (hc q r h).symm.trans (hc q r' h')
    exact Option.some.inj this
  induction V with
  | halt => intro n v c hc; simp only [idealLoop]; exact hpure v c hc
  | query q k ih =>
    intro n v c hc
    simp only [idealLoop, prob_bind]
    have hans : (sim lam).answer c q = lazyAnswer c q := rfl
    rw [hans]
    unfold lazyAnswer
    cases hq : c q with
    | some r =>
      refine (expect_pure _ _).trans ?_
      refine ih _ _ _ _ fun q' r' h => ?_
      rcases List.mem_append.mp h with h | h
      · exact hc q' r' h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        rw [h.1, h.2]; exact hq
    | none =>
      refine (expect_map _ _ _).trans ?_
      have : ∀ r : Digest lam, prob (idealLoop (sim lam) (Z.onView i) (k r) n
          { v with trace := v.trace ++ [(q, r)] } (Function.update c q (some r)))
          {v | ¬ v.trace.Consistent} = 0 := by
        intro r
        refine ih _ _ _ _ fun q' r' h => ?_
        rcases List.mem_append.mp h with h | h
        · have hne : q' ≠ q := fun e => by
            have := hc q' r' h; rw [e, hq] at this; simp at this
          rw [Function.update_of_ne hne]; exact hc q' r' h
        · simp only [List.mem_singleton, Prod.mk.injEq] at h
          rw [h.1, h.2, Function.update_self]
      simp [expect, this]
  | sample m k ih =>
    intro n v c hc
    simp only [idealLoop, prob_bind]
    have : ∀ r : Fin (m + 1), prob (idealLoop (sim lam) (Z.onView i) (k r) n
        { v with coins := v.coins ++ [r.val] } c) {v | ¬ v.trace.Consistent} = 0 :=
      fun r => ih _ _ _ _ hc
    simp [expect, this]
  | request k ih =>
    intro n v c hc
    cases n with
    | zero => simp only [idealLoop]; exact hpure v c hc
    | succ n =>
      simp only [idealLoop, Env.onView, sim, PMF.pure_bind]
      exact ih _ _ _ _ _ hc

theorem prob_run_bind_zero {α β : Type} (f : Oracle lam) (c : OComp lam α) (g : α → OComp lam β)
    (E : Set β) (h : ∀ a, prob ((g a).run f) E = 0) :
    prob ((c.bind g).run f) E = 0 := by
  rw [run_bind, prob_bind]; simp [expect, h]

theorem le_add_of_SD_le' {α : Type} {X Y : Set α → ℝ≥0∞} {z : ℝ≥0∞} (h : SD X Y ≤ z) (E : Set α) :
    Y E ≤ X E + z := by
  have h1 : Y E - X E ≤ z :=
    le_trans (le_trans (le_max_right _ _) (le_iSup (fun E => max (X E - Y E) (Y E - X E)) E)) h
  rw [add_comm]; exact tsub_le_iff_right.1 h1

variable (lam)

theorem leaky_private :
    HasIndexPrivacyWith (Rall lam) (leaky lam) (sim lam) (fun _ N => N / 2 ^ lam) := by
  classical
  intro i Z _ tV Vt N _
  have hR : ∀ T, Pr (realExp (leaky lam) Vt (Z.onView i) i N) (fun _ => T)
      = expect (PMF.uniformOfFintype (Digest lam)) fun y =>
          PrFrom (Function.update (fun _ => none) [] (some y))
            (realLoop (leaky lam) (Z.onView i) (i, y) (Vt ()) N ⟨(), [], [], []⟩) T := by
    intro T
    have e : realExp (leaky lam) Vt (Z.onView i) i N = .query [] fun y =>
        realLoop (leaky lam) (Z.onView i) (i, y) (Vt ()) N ⟨(), [], [], []⟩ := rfl
    rw [Pr_eq_PrFrom, e, PrFrom_query_miss rfl]
  have hI : ∀ T, prob (idealExp (Rall lam) (sim lam) Vt (Z.onView i) i N) T
      = expect (PMF.uniformOfFintype (Digest lam)) fun y =>
          prob (idealLoop (sim lam) (Z.onView i) (Vt ()) N ⟨(), [], [], []⟩
            (Function.update (fun _ => none) [] (some y))) T := by
    intro T
    simp only [idealExp, prob_bind, sim, expect_map]
  let S : Finset (Digest lam) := (futureX Z i N []).toFinset
  have hS : (S.card : ℝ≥0∞) / 2 ^ lam ≤ N / 2 ^ lam := by
    gcongr
    exact_mod_cast (List.toFinset_card_le _).trans (le_of_eq (length_futureX Z i N []))
  have hag : ∀ T y, y ∉ S →
      PrFrom (Function.update (fun _ => none) [] (some y))
        (realLoop (leaky lam) (Z.onView i) (i, y) (Vt ()) N ⟨(), [], [], []⟩) T
      = prob (idealLoop (sim lam) (Z.onView i) (Vt ()) N ⟨(), [], [], []⟩
          (Function.update (fun _ => none) [] (some y))) T := by
    intro T y hy
    exact loops_agree Z i y T (Vt ()) N _ _ (by simpa [S] using hy)
  have hle1 : ∀ (c : Cache lam) (m : OComp lam (LView lam)) T, PrFrom c m T ≤ 1 := by
    intro c m T
    calc PrFrom c m T ≤ ∫⁻ _, 1 ∂(U lam) := lintegral_mono fun _ => prob_le_one _ _
      _ = 1 := by simp
  refine ⟨iSup_le fun T => max_le ?_ ?_, ?_⟩
  · rw [tsub_le_iff_left]
    beta_reduce
    rw [hR, hI]
    exact (avg_le_of_agree S _ _ (fun y => hle1 _ _ _) (hag T)).trans (add_le_add le_rfl hS)
  · rw [tsub_le_iff_left]
    beta_reduce
    rw [hR, hI]
    exact (avg_le_of_agree S _ _ (fun y => prob_le_one _ _) fun y hy => (hag T y hy).symm).trans
      (add_le_add le_rfl hS)
  · rw [hI]
    have : ∀ y : Digest lam, prob (idealLoop (sim lam) (Z.onView i) (Vt ()) N ⟨(), [], [], []⟩
        (Function.update (fun _ => none) [] (some y))) {v | ¬ v.trace.Consistent} = 0 :=
      fun y => ideal_consistent Z i (Vt ()) N _ _ (by simp)
    simp [expect, this]

/-- (1) By the definitions of ZKCP/Defs.lean, leaky is a ZK-CP-ARG: completeness error 0, binding
    error 0, privacy error
N / 2^λ, whatever the number of oracle queries of the adversarial verifier. -/
theorem leaky_isZKCPArg :
    IsZKCPArg (Rall lam) (leaky lam) 0 (fun _ _ => 0) (fun _ N => N / 2 ^ lam) where
  completeness := by
    intro i x w _
    have e : completenessExp (leaky lam) i x w = .query [] fun _ => .pure true := rfl
    rw [Pr_eq_PrFrom, e, PrFrom_query_miss rfl]
    simp [PrFrom_pure, expect]
  indexBinding := by
    refine ⟨ext lam, ?_⟩
    intro tC tP St Ct Pt _ _
    have h0 : ∀ f,
        PrCoins f (bindingExp (leaky lam) (ext lam) Ct Pt) (bindingBad (Rall lam)) = 0 := by
      intro f
      unfold PrCoins
      refine prob_run_bind_zero f _ _ _ fun p => prob_run_bind_zero f _ _ _ fun p' => ?_
      show prob (PMF.pure _) _ = 0
      rw [prob_pure, if_neg]
      rintro ⟨_, h | h⟩
      · exact h ⟨(), trivial⟩
      · exact h trivial
    simp [Pr, h0]
  indexPrivacy := ⟨sim lam, leaky_private lam⟩

/-! ### Part 2: leaky fails as soon as the environment sees the adversary's view -/

/-- The client: ask the oracle at ε, then request one session. -/
def client : Unit → LAdv lam := fun _ => .query [] fun _ => .request fun _ _ => .halt

/-- The environment: name as instance the first oracle answer in the client's view. It does not use
i. -/
def steered : ViewEnv lam Unit (Digest lam) Unit (Option Bool) := fun v =>
  v.trace.head?.map fun e => (e.2, ())

/-- In the real experiment the client always receives the index. -/
theorem real_reveals (i : Bool) (T : Set (LView lam)) :
    Pr (realExp (leaky lam) (client lam) (steered lam) i 1) (fun _ => T)
      = expect (PMF.uniformOfFintype (Digest lam)) fun y =>
          PrFrom (Function.update (fun _ => none) [] (some y))
            (.pure ⟨(), [(y, some i)], [([], y)], []⟩) T := by
  have e : realExp (leaky lam) (client lam) (steered lam) i 1 = .query [] fun y => .query [] fun r =>
      .pure ⟨(), [(r, if r = y then some i else none)], [([], r)], []⟩ := rfl
  rw [Pr_eq_PrFrom, e, PrFrom_query_miss rfl]
  refine expect_congr _ fun y => ?_
  rw [PrFrom_query_hit (r := y) (by simp)]
  simp

/-- (2) No simulator gives leaky the strong form of index privacy: ζ(1, 1) ≥ 1/2, for one oracle
    query and one
session. -/
theorem leaky_not_strong (S : Simulator lam Unit Unit (Digest lam) (Option Bool)) (ζ : ℕ → ℕ → ℝ≥0∞)
    (h : HasStrongIndexPrivacyWith (Rall lam) (leaky lam) S ζ) : 1 ≤ ζ 1 1 + ζ 1 1 := by
  classical
  have hZ : ∀ i, (steered lam).IsValid (Rall lam) i := fun _ _ _ _ _ => trivial
  have hb : ∀ ivk, (client lam ivk).QueryBound 1 := fun _ _ _ _ => trivial
  let T : Set (LView lam) := {v | ∃ x, (x, some true) ∈ v.sessions}
  have hr : ∀ i : Bool, Pr (realExp (leaky lam) (client lam) (steered lam) i 1) (fun _ => T)
      = if i = true then 1 else 0 := by
    intro i
    rw [real_reveals]
    cases i
    · simp [PrFrom_pure, T, expect]
    · have : ∀ y : Digest lam, PrFrom (Function.update (fun _ => none) [] (some y))
          (.pure (⟨(), [(y, some true)], [([], y)], []⟩ : LView lam)) T = 1 := by
        intro y; rw [PrFrom_pure, if_pos]; exact ⟨y, by simp⟩
      simp only [this, expect_const, if_true]
  have hid : idealExp (Rall lam) S (client lam) (steered lam) true 1
      = idealExp (Rall lam) S (client lam) (steered lam) false 1 := rfl
  have h1 := le_add_of_SD_le (h true (steered lam) (hZ true) 1 (client lam) 1 hb).1 T
  have h2 := le_add_of_SD_le' (h false (steered lam) (hZ false) 1 (client lam) 1 hb).1 T
  beta_reduce at h1 h2
  rw [hr] at h1 h2
  rw [← hid] at h2
  simp only [if_true, Bool.false_eq_true, if_false, zero_add] at h1 h2
  exact h1.trans (add_le_add h2 le_rfl)

end ZKCP.Separation
