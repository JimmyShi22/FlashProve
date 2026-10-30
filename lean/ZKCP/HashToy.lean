-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/HashToy.lean: a toy that really uses the random oracle.

One-bit index i; the key is ivk = f(i, salt) for a random salt out of M+1; the relation is x = i;
the proof opens the commitment by sending the salt; V recomputes the hash. Results:

  `hash_complete`   completeness error 0.
  `hash_private`   strong index privacy with error ζ(t_V, N) = t_V / (M+1), with a simulator that
      programs the oracle and answers consistently.
  `hash_binding`   index binding with error ε(t_C, t_P) = (t_C² + t_P + 1) / 2^λ, with an extractor
      that reads tr_C.
  `hash_main_with`, `hash_main`   the three together: the first in the form `IsZKCPArgWith` (named
      form), the second in the form `IsZKCPArg`.
  `hash_extraction_correct`   i* = i for the honest committer.
  `unsalted_not_private`   without the salt, one oracle query breaks index privacy: every simulator
      has 2·ζ(1,0) + 2^(-λ) ≥ 1.
-/
import ZKCP.Sanity
import ZKCP.Optional
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

section HashToy
variable (lam M : ℕ)

/-- The string that is hashed: the bit, followed by the salt in unary.  Injective. -/
def enc (b : Bool) (s : ℕ) : Str := b :: List.replicate s true

lemma enc_inj {b b' : Bool} {s s' : ℕ} (h : enc b s = enc b' s') : b = b' ∧ s = s' := by
  simp only [enc, List.cons.injEq] at h
  refine ⟨h.1, ?_⟩
  have := congrArg List.length h.2
  simpa using this

/-- The salted hash commitment to one bit, opened by every proof. (The relation eqR, x = i, is in
Sanity.lean.) -/
def hashArg : Arg lam Bool Bool Unit (Digest lam) (Bool × Fin (M + 1)) (Fin (M + 1)) where
  C := fun i => .sample M fun s => .query (enc i s) fun d => .pure (d, (i, s))
  P := fun isk _ _ => .pure isk.2
  V := fun ivk x π => .query (enc x π) fun d => .pure (decide (d = ivk))

theorem hash_complete : HasCompletenessError eqR (hashArg lam M) 0 := by
  intro i x w hR
  have hx : x = i := hR
  subst hx
  have h0 : ∀ f : Oracle lam,
      PrCoins f (completenessExp (hashArg lam M) x x w) {b | b = false} = 0 := by
    intro f
    simp [PrCoins, completenessExp, sessionExp, hashArg, OComp.bind, OComp.run, prob_pure]
  rw [Pr, lintegral_congr h0]; simp

variable {lam}

/-- Program the point p of the table to the value d, unless the table already has an entry there. -/
def program (c : Cache lam) (p : Str) (d : Digest lam) : Cache lam :=
  match c p with
  | some _ => c
  | none => Function.update c p (some d)

lemma program_of_none {c : Cache lam} {p : Str} (h : c p = none) (d : Digest lam) :
    program c p d = Function.update c p (some d) := by simp [program, h]

lemma program_of_some {c : Cache lam} {p : Str} {r : Digest lam}
    (h : c p = some r) (d : Digest lam) : program c p d = c := by
  simp [program, h]

lemma CacheLE.program (c : Cache lam) (p : Str) (d : Digest lam) : CacheLE c (program c p d) := by
  cases h : c p with
  | none => rw [program_of_none h]; exact CacheLE.update h d
  | some r => rw [program_of_some h]; exact CacheLE.refl c

variable (lam)

/-- The simulator: a uniform key d and a salt s chosen at the start; a lazy oracle; at a session for
x it programs f(x, s) := d, unless V~ has already asked that point, and sends s. -/
def hashSim : Simulator lam Unit (Digest lam) Bool (Fin (M + 1)) where
  St := Digest lam × Fin (M + 1) × Cache lam
  init := fun _ _ => (PMF.uniformOfFintype (Fin (M + 1))).bind fun s =>
    (PMF.uniformOfFintype (Digest lam)).map fun d => (d, (d, s, fun _ => none))
  answer := fun st q => (lazyAnswer st.2.2 q).map fun out => (out.1, (st.1, st.2.1, out.2))
  prove := fun st x => PMF.pure (st.2.1, (st.1, st.2.1, program st.2.2 (enc x st.2.1) st.1))

variable {lam M}

/-- Shorthands for the types of this toy. -/
abbrev HView (lam M : ℕ) : Type := View lam (Digest lam) Bool (Fin (M + 1))
abbrev HEnv (lam M : ℕ) : Type := ViewEnv lam (Digest lam) Bool Unit (Fin (M + 1))
abbrev HAdv (lam M : ℕ) : Type := AdvVerifier lam Bool (Fin (M + 1))

/-- Probability, with a lazy oracle from table c, that V~ (`AdvVerifier`, ZKCP/Defs.lean) queries
the point p before its first session. -/
def hit {X Pf : Type} (p : Str) : AdvVerifier lam X Pf → Cache lam → ℝ≥0∞
  | .halt, _ => 0
  | .query q k, c => if q = p then 1 else expect (lazyAnswer c q) fun out => hit p (k out.1) out.2
  | .sample _ k, c => expect (PMF.uniformOfFintype _) fun r => hit p (k r) c
  | .request _, _ => 0

/-- Under the hypotheses below, after the first session the real and the ideal experiment coincide
exactly. -/
lemma opened_eq {i : Bool} {Z : HEnv lam M} (hZ : Z.IsValid eqR i) (s : Fin (M + 1))
    (d : Digest lam) (E : Set (HView lam M)) (Vt : HAdv lam M) :
    ∀ (n : ℕ) (v : HView lam M) (c : Cache lam), c (enc i s) = some d →
      PrFrom c (realLoop (hashArg lam M) Z (i, s) Vt n v) E =
        prob (idealLoop (hashSim lam M) Z Vt n v (d, s, c)) E := by
  induction Vt with
  | halt => intro n v c _; simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure]
  | query q k ih =>
    intro n v c hc
    simp only [realLoop, idealLoop, prob_bind, hashSim, expect_map]
    cases hq : c q with
    | some r =>
      rw [PrFrom_query_hit hq]
      simp only [lazyAnswer, hq, expect_pure]
      exact ih _ _ _ _ hc
    | none =>
      rw [PrFrom_query_miss hq]
      simp only [lazyAnswer, hq, expect_map]
      refine expect_congr _ fun r => ih _ _ _ _ ?_
      have hne : enc i s ≠ q := fun e => by rw [e, hq] at hc; cases hc
      rw [Function.update_of_ne hne]; exact hc
  | sample m k ih =>
    intro n v c hc
    simp only [realLoop, idealLoop, PrFrom_sample, prob_bind]
    exact expect_congr _ fun r => ih _ _ _ _ hc
  | request k ih =>
    intro n v c hc
    cases n with
    | zero => simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure]
    | succ n =>
      simp only [realLoop, idealLoop]
      cases hz : Z v with
      | none => simp only [pure_eq, PrFrom_pure, prob_pure]
      | some xw =>
        obtain ⟨x, w⟩ := xw
        have hx : x = i := hZ v x w hz
        subst hx
        simp only [hashArg, OComp.bind, prob_bind, hashSim, expect_pure, program_of_some hc]
        exact ih _ _ _ _ _ hc

/-- Under the hypotheses below, before the first session the real and the ideal experiment differ
only if V~ queries the committed point. -/
lemma closed_le {i : Bool} {Z : HEnv lam M} (hZ : Z.IsValid eqR i) (s : Fin (M + 1))
    (d : Digest lam) (E : Set (HView lam M)) (Vt : HAdv lam M) :
    ∀ (n : ℕ) (v : HView lam M) (c : Cache lam), c (enc i s) = none →
      (PrFrom (Function.update c (enc i s) (some d)) (realLoop (hashArg lam M) Z (i, s) Vt n v) E ≤
        prob (idealLoop (hashSim lam M) Z Vt n v (d, s, c)) E + hit (enc i s) Vt c) ∧
      (prob (idealLoop (hashSim lam M) Z Vt n v (d, s, c)) E ≤
        PrFrom (Function.update c (enc i s) (some d)) (realLoop (hashArg lam M) Z (i, s) Vt n v) E +
          hit (enc i s) Vt c) := by
  induction Vt with
  | halt =>
    intro n v c _
    simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure, hit, add_zero]
    exact ⟨le_rfl, le_rfl⟩
  | query q k ih =>
    intro n v c hc
    by_cases hqp : q = enc i s
    · simp only [hit, if_pos hqp]
      exact ⟨le_trans (PrFrom_le_one _ _ _) le_add_self, le_trans (prob_le_one _ _) le_add_self⟩
    · have hc1 : Function.update c (enc i s) (some d) q = c q := Function.update_of_ne hqp _ _
      simp only [hit, if_neg hqp, realLoop, idealLoop, prob_bind, hashSim, expect_map]
      cases hq : c q with
      | some r =>
        rw [PrFrom_query_hit (hc1.trans hq)]
        simp only [lazyAnswer, hq, expect_pure]
        exact ih _ _ _ _ hc
      | none =>
        rw [PrFrom_query_miss (hc1.trans hq)]
        simp only [lazyAnswer, hq, expect_map]
        have hcomm : ∀ r : Digest lam,
            Function.update (Function.update c (enc i s) (some d)) q (some r) =
              Function.update (Function.update c q (some r)) (enc i s) (some d) := fun r =>
          Function.update_comm (Ne.symm hqp) _ _ _
        have hn : ∀ r : Digest lam, Function.update c q (some r) (enc i s) = none := fun r => by
          rw [Function.update_of_ne (Ne.symm hqp)]; exact hc
        simp only [hcomm]
        exact ⟨expect_le_add _ fun r => (ih r n _ _ (hn r)).1,
          expect_le_add _ fun r => (ih r n _ _ (hn r)).2⟩
  | sample m k ih =>
    intro n v c hc
    simp only [hit, realLoop, idealLoop, PrFrom_sample, prob_bind]
    exact ⟨expect_le_add _ fun r => (ih r n _ _ hc).1, expect_le_add _ fun r => (ih r n _ _ hc).2⟩
  | request k _ =>
    intro n v c hc
    cases n with
    | zero =>
      simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure, hit, add_zero]
      exact ⟨le_rfl, le_rfl⟩
    | succ n =>
      simp only [realLoop, idealLoop, hit, add_zero]
      cases hz : Z v with
      | none =>
        simp only [pure_eq, PrFrom_pure, prob_pure]
        exact ⟨le_rfl, le_rfl⟩
      | some xw =>
        obtain ⟨x, w⟩ := xw
        have hx : x = i := hZ v x w hz
        subst hx
        simp only [hashArg, OComp.bind, prob_bind, hashSim, expect_pure, program_of_none hc]
        have := opened_eq hZ s d E (k x s) n { v with sessions := v.sessions ++ [(x, s)] }
          (Function.update c (enc x s) (some d)) (Function.update_self _ _ _)
        exact ⟨le_of_eq this, le_of_eq this.symm⟩

/-- Under the hypotheses below, the simulator answers consistently: V~'s trace is always inside its
table, and the table only grows. -/
lemma hashSim_consistent (Z : HEnv lam M) (s : Fin (M + 1)) (d : Digest lam) (Vt : HAdv lam M) :
    ∀ (n : ℕ) (v : HView lam M) (c : Cache lam), TraceIn v.trace c →
      prob (idealLoop (hashSim lam M) Z Vt n v (d, s, c)) {v | ¬ v.trace.Consistent} = 0 := by
  induction Vt with
  | halt => intro n v c h; simp only [idealLoop]; exact prob_pure_inconsistent_eq_zero h
  | query q k ih =>
    intro n v c h
    simp only [idealLoop, prob_bind, hashSim, expect_map]
    exact expect_lazyAnswer_eq_zero c q _ fun r c' hc hq => ih r n _ c' ((h.mono hc).snoc hq)
  | sample m k ih =>
    intro n v c h
    simp only [idealLoop, prob_bind]
    have : ∀ r, prob
          (idealLoop (hashSim lam M) Z (k r) n { v with coins := v.coins ++ [r.val] } (d, s, c))
          {v | ¬ v.trace.Consistent} = 0 :=
      fun r => ih r n _ c h
    simp only [this, expect_zero]
  | request k ih =>
    intro n v c h
    cases n with
    | zero => simp only [idealLoop]; exact prob_pure_inconsistent_eq_zero h
    | succ n =>
      simp only [idealLoop]
      cases Z v with
      | none => exact prob_pure_inconsistent_eq_zero h
      | some xw =>
        simp only [prob_bind, hashSim, expect_pure]
        exact ih _ _ n _ _ (h.mono (CacheLE.program c _ d))

/-- A t-query V~ hits at most t of the M+1 candidate points, in expectation. -/
lemma sum_hit_le {X Pf : Type} (i : Bool) (Vt : AdvVerifier lam X Pf) :
    ∀ (t : ℕ) (c : Cache lam), Vt.QueryBound t → ∑ s : Fin (M + 1), hit (enc i s) Vt c ≤ t := by
  induction Vt with
  | halt => intro t c _; simp [hit]
  | query q k ih =>
    intro t c hb
    cases t with
    | zero => exact absurd hb (by simp [AdvVerifier.QueryBound])
    | succ t =>
      have hb' : ∀ r, (k r).QueryBound t := hb
      have h1 : ∀ s : Fin (M + 1), hit (enc i s) (.query q k) c ≤
          (if q = enc i s then 1 else 0) +
            expect (lazyAnswer c q) fun out => hit (enc i s) (k out.1) out.2 := by
        intro s
        by_cases e : q = enc i s
        · simp only [hit, if_pos e]; exact le_self_add
        · simp only [hit, if_neg e, zero_add]; exact le_rfl
      have h2 : ∑ s : Fin (M + 1), (if q = enc i s then (1 : ℝ≥0∞) else 0) ≤ 1 := by
        by_cases ex : ∃ s₀ : Fin (M + 1), q = enc i s₀
        · obtain ⟨s₀, hs₀⟩ := ex
          rw [Finset.sum_eq_single s₀]
          · simp [hs₀]
          · intro s _ hne
            rw [if_neg]
            intro e
            exact hne (Fin.ext (enc_inj (e.symm.trans hs₀)).2)
          · intro h; exact absurd (Finset.mem_univ _) h
        · have ex' : ∀ s₀ : Fin (M + 1), q ≠ enc i s₀ := fun s₀ e => ex ⟨s₀, e⟩
          simp [ex']
      calc ∑ s : Fin (M + 1), hit (enc i s) (.query q k) c
          ≤ ∑ s : Fin (M + 1), ((if q = enc i s then 1 else 0) +
              expect (lazyAnswer c q) fun out => hit (enc i s) (k out.1) out.2) :=
            Finset.sum_le_sum fun s _ => h1 s
        _ = (∑ s : Fin (M + 1), (if q = enc i s then (1 : ℝ≥0∞) else 0)) +
              expect (lazyAnswer c q) fun out =>
                ∑ s : Fin (M + 1), hit (enc i s) (k out.1) out.2 := by
            rw [Finset.sum_add_distrib, expect_finset_sum]
        _ ≤ 1 + t := add_le_add h2 (expect_le_of_le _ fun out => ih _ _ _ (hb' _))
        _ = ((t + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
  | sample m k ih =>
    intro t c hb
    have hb' : ∀ r, (k r).QueryBound t := hb
    simp only [hit]
    rw [← expect_finset_sum]
    exact expect_le_of_le _ fun r => ih _ _ _ (hb' r)
  | request k _ => intro t c _; simp [hit]

/-- Strong index privacy of the salted hash commitment: ζ(t_V, N) = t_V / (M+1), for every number of
sessions. -/
theorem hash_private : HasStrongIndexPrivacyWith eqR (hashArg lam M) (hashSim lam M)
    fun tV _ => (tV : ℝ≥0∞) / ((M + 1 : ℕ) : ℝ≥0∞) := by
  intro i Z hZ tV Vt N hV
  have hbound : (expect (PMF.uniformOfFintype (Fin (M + 1))) fun s =>
      expect (PMF.uniformOfFintype (Digest lam)) fun d => hit (enc i s) (Vt d) fun _ => none) ≤
      (tV : ℝ≥0∞) / ((M + 1 : ℕ) : ℝ≥0∞) := by
    rw [expect_comm]
    refine expect_le_of_le _ fun d => ?_
    rw [expect_uniform, ← Finset.mul_sum, Fintype.card_fin, ENNReal.div_eq_inv_mul]
    gcongr
    exact sum_hit_le i (Vt d) tV _ (hV d)
  have hreal : ∀ E, Pr (realExp (hashArg lam M) Vt Z i N) (fun _ => E) =
      expect (PMF.uniformOfFintype (Fin (M + 1))) fun s => expect (PMF.uniformOfFintype (Digest lam)) fun d =>
        PrFrom (Function.update (fun _ => none) (enc i s) (some d))
          (realLoop (hashArg lam M) Z (i, s) (Vt d) N ⟨d, [], [], []⟩) E := by
    intro E
    rw [Pr_eq_PrFrom]
    simp only [realExp, hashArg, bind_eq, OComp.bind, PrFrom_sample]
    refine expect_congr _ fun s => ?_
    rw [PrFrom_query_miss rfl]
  have hideal : ∀ E, prob (idealExp eqR (hashSim lam M) Vt Z i N) E =
      expect (PMF.uniformOfFintype (Fin (M + 1))) fun s => expect (PMF.uniformOfFintype (Digest lam)) fun d =>
        prob (idealLoop (hashSim lam M) Z (Vt d) N ⟨d, [], [], []⟩ (d, s, fun _ => none)) E := by
    intro E
    simp only [idealExp, hashSim, prob_bind, expect_bind, expect_map]
  constructor
  · refine SD_le_of_forall (fun E => ?_) (fun E => ?_)
    · rw [hreal, hideal]
      refine le_trans ?_ (add_le_add le_rfl hbound)
      refine le_trans
        (expect_mono _ fun s => expect_le_add _ fun d => (closed_le hZ s d E (Vt d) N _ _ rfl).1) ?_
      rw [expect_add]
    · rw [hreal, hideal]
      refine le_trans ?_ (add_le_add le_rfl hbound)
      refine le_trans
        (expect_mono _ fun s => expect_le_add _ fun d => (closed_le hZ s d E (Vt d) N _ _ rfl).2) ?_
      rw [expect_add]
  · rw [hideal]
    have : ∀ (s : Fin (M + 1)) (d : Digest lam),
        prob (idealLoop (hashSim lam M) Z (Vt d) N ⟨d, [], [], []⟩ (d, s, fun _ => none))
            {v | ¬ v.trace.Consistent} = 0 :=
      fun s d => hashSim_consistent Z s d (Vt d) N _ _ (TraceIn.nil _)
    simp only [this, expect_zero]

/-! ### Index binding of the hash toy: the extractor reads the committer's trace -/

section BindingTools
variable {α β γ : Type}

lemma bind_assoc' (m : OComp lam α) (g : α → OComp lam β) (h : β → OComp lam γ) :
    (m.bind g).bind h = m.bind fun a => (g a).bind h := by
  induction m with
  | pure a => rfl
  | query q k ih => simp only [OComp.bind, ih]
  | sample n k ih => simp only [OComp.bind, ih]

lemma withTrace_bind_fst (m : OComp lam α) (g : α → OComp lam β) :
    (m.withTrace.bind fun o => g o.1) = m.bind g := by
  induction m with
  | pure a => rfl
  | query q k ih => simp only [OComp.withTrace, OComp.bind, bind_assoc', ih]
  | sample n k ih => simp only [OComp.withTrace, OComp.bind, ih]

/-- 1 / 2^λ. -/
def u (lam : ℕ) : ℝ≥0∞ := (Fintype.card (Digest lam) : ℝ≥0∞)⁻¹

open Classical in
/-- A uniform digest falls into a set S of forbidden values with probability at most |S| / 2^λ. -/
lemma expect_uniform_le (S : Finset (Digest lam)) (F : Digest lam → ℝ≥0∞) (Y : ℝ≥0∞)
    (h1 : ∀ r, F r ≤ 1) (h2 : ∀ r, r ∉ S → F r ≤ Y) :
    expect (PMF.uniformOfFintype (Digest lam)) F ≤ Y + (S.card : ℝ≥0∞) * u lam := by
  refine le_trans (expect_le_prob_add _ F (↑S) Y h1 fun r hr => h2 r (by simpa using hr)) ?_
  rw [add_comm]
  gcongr
  rw [prob_eq_expect, expect_uniform, ← Finset.mul_sum, mul_comm]
  simp [u]

lemma cast_mul_mono {a b : ℕ} (h : a ≤ b) (x : ℝ≥0∞) : (a : ℝ≥0∞) * x ≤ (b : ℝ≥0∞) * x := by
  gcongr

/-- No two distinct points of the table have the same value. -/
def NoColl (c : Cache lam) : Prop := ∀ q q' r, c q = some r → c q' = some r → q = q'

/-- Table c' is table c extended by exactly the entries of the trace tr. -/
def Ext (c : Cache lam) (tr : Trace lam) (c' : Cache lam) : Prop :=
  ∀ q r, c' q = some r ↔ (c q = some r ∨ (q, r) ∈ tr)

/-- Birthday bound. Run a t-query m lazily from a collision-free table whose values lie in S. Except
with probability t(|S|+t)/2^λ the final table is collision-free (and it is the old table extended by
m's trace). -/
lemma phase1 (B : ℝ≥0∞) (m : OComp lam α) :
    ∀ (t : ℕ) (c : Cache lam) (S : Finset (Digest lam)) (F : α × Trace lam → Cache lam → ℝ≥0∞),
      m.QueryBound t → NoColl c → (∀ q r, c q = some r → r ∈ S) → (∀ o c', F o c' ≤ 1) →
      (∀ a tr c', NoColl c' → Ext c tr c' → F (a, tr) c' ≤ B) →
      expect (m.withTrace.lazyRun c) (fun o => F o.1 o.2) ≤
        B + ((t * (S.card + t) : ℕ) : ℝ≥0∞) * u lam := by
  classical
  induction m with
  | pure a =>
    intro t c S F _ hn _ _ hB
    simp only [OComp.withTrace, OComp.lazyRun, expect_pure]
    exact le_trans (hB a [] c hn (fun q r => by simp)) le_self_add
  | sample n k ih =>
    intro t c S F hb hn hS h1 hB
    simp only [OComp.withTrace, OComp.lazyRun, expect_bind]
    exact expect_le_of_le _ fun r => ih r t c S F (hb r) hn hS h1 hB
  | query q k ih =>
    intro t c S F hb hn hS h1 hB
    cases t with
    | zero => exact absurd hb (by simp [OComp.QueryBound])
    | succ t =>
      have hb' : ∀ r, (k r).QueryBound t := hb
      simp only [OComp.withTrace, OComp.lazyRun, OComp.lazyRun_bind, expect_bind, expect_pure]
      cases hq : c q with
      | some r =>
        simp only [lazyAnswer, hq, expect_pure]
        refine le_trans
          (ih r t c S (fun o c' => F (o.1, (q, r) :: o.2) c') (hb' r) hn hS (fun _ _ => h1 _ _) ?_)
          ?_
        · intro a tr c' hn' he
          refine hB a _ c' hn' fun q0 r0 => ?_
          rw [he q0 r0, List.mem_cons]
          constructor
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · rintro (h | h | h)
            · exact Or.inl h
            · rw [Prod.mk.injEq] at h; exact Or.inl (by rw [h.1, h.2]; exact hq)
            · exact Or.inr h
        · exact add_le_add le_rfl (cast_mul_mono (by nlinarith) _)
      | none =>
        simp only [lazyAnswer, hq, expect_map]
        refine le_trans (expect_uniform_le S _ (B + ((t * (S.card + 1 + t) : ℕ) : ℝ≥0∞) * u lam)
          (fun r => expect_le_of_le _ fun _ => h1 _ _) fun r hr => ?_) ?_
        · have := ih r t (Function.update c q (some r)) (insert r S)
            (fun o c' => F (o.1, (q, r) :: o.2) c') (hb' r) ?_ ?_ (fun _ _ => h1 _ _) ?_
          · rwa [Finset.card_insert_of_notMem hr] at this
          · intro q1 q2 r' e1 e2
            by_cases a1 : q1 = q <;> by_cases a2 : q2 = q
            · rw [a1, a2]
            · rw [a1, Function.update_self] at e1
              rw [Function.update_of_ne a2] at e2
              cases e1
              exact absurd (hS _ _ e2) hr
            · rw [a2, Function.update_self] at e2
              rw [Function.update_of_ne a1] at e1
              cases e2
              exact absurd (hS _ _ e1) hr
            · rw [Function.update_of_ne a1] at e1
              rw [Function.update_of_ne a2] at e2
              exact hn _ _ _ e1 e2
          · intro q1 r' e1
            by_cases a1 : q1 = q
            · rw [a1, Function.update_self] at e1
              cases e1
              exact Finset.mem_insert_self _ _
            · rw [Function.update_of_ne a1] at e1
              exact Finset.mem_insert_of_mem (hS _ _ e1)
          · intro a tr c' hn' he
            refine hB a _ c' hn' fun q0 r0 => ?_
            rw [he q0 r0, List.mem_cons, Prod.mk.injEq]
            by_cases a0 : q0 = q
            · subst a0
              rw [Function.update_self, hq]
              constructor
              · rintro (h | h)
                · cases h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                · exact Or.inr (Or.inr h)
              · rintro (h | h | h)
                · cases h
                · rw [h.2]; exact Or.inl rfl
                · exact Or.inr h
            · rw [Function.update_of_ne a0]
              constructor
              · rintro (h | h)
                · exact Or.inl h
                · exact Or.inr (Or.inr h)
              · rintro (h | h | h)
                · exact Or.inl h
                · exact absurd h.1 a0
                · exact Or.inr h
        · rw [add_assoc, ← add_mul, ← Nat.cast_add]
          exact add_le_add le_rfl (cast_mul_mono (by nlinarith) _)

/-- Target bound. Let G be a property of tables that survives every new entry whose value is not
ivk. Run a t-query m lazily from a table with G. Except with probability t/2^λ the final table has
G. -/
lemma phase2 (B : ℝ≥0∞) (ivk : Digest lam) (G : Cache lam → Prop)
    (hG : ∀ c q r, G c → r ≠ ivk → G (Function.update c q (some r))) (m : OComp lam α) :
    ∀ (t : ℕ) (c : Cache lam) (F : α → Cache lam → ℝ≥0∞),
      m.QueryBound t → G c → (∀ a c', F a c' ≤ 1) → (∀ a c', G c' → F a c' ≤ B) →
      expect (m.lazyRun c) (fun o => F o.1 o.2) ≤ B + (t : ℝ≥0∞) * u lam := by
  classical
  induction m with
  | pure a =>
    intro t c F _ hg _ hB
    simp only [OComp.lazyRun, expect_pure]
    exact le_trans (hB a c hg) le_self_add
  | sample n k ih =>
    intro t c F hb hg h1 hB
    simp only [OComp.lazyRun, expect_bind]
    exact expect_le_of_le _ fun r => ih r t c F (hb r) hg h1 hB
  | query q k ih =>
    intro t c F hb hg h1 hB
    cases t with
    | zero => exact absurd hb (by simp [OComp.QueryBound])
    | succ t =>
      have hb' : ∀ r, (k r).QueryBound t := hb
      simp only [OComp.lazyRun, expect_bind]
      cases hq : c q with
      | some r =>
        simp only [lazyAnswer, hq, expect_pure]
        refine le_trans (ih r t c F (hb' r) hg h1 hB) ?_
        exact add_le_add le_rfl (cast_mul_mono (Nat.le_succ t) _)
      | none =>
        simp only [lazyAnswer, hq, expect_map]
        refine le_trans (expect_uniform_le {ivk} _ (B + (t : ℝ≥0∞) * u lam)
          (fun r => expect_le_of_le _ fun _ => h1 _ _) fun r hr => ?_) ?_
        · exact ih r t _ F (hb' r) (hG c q r hg (by simpa using hr)) h1 hB
        · rw [add_assoc, ← add_mul]
          simp

end BindingTools

/-- The extractor: i* is the first bit of the first query in tr_C that was answered by ivk; ⊥ if
there is none. -/
def hashExt : Extractor lam Bool Bool Unit (Digest lam) (Fin (M + 1)) where
  Ei := fun ivk trC => (trC.find? fun e => decide (e.2 = ivk)).bind fun e => e.1.head?
  Ew := fun _ _ _ _ _ => ()

/-- Index binding of the salted hash commitment: ε(t_C, t_P) = (t_C² + t_P + 1) / 2^λ. -/
theorem hash_binding : HasIndexBindingWith eqR (hashArg lam M) (hashExt (lam := lam) (M := M))
    fun tC tP => ((tC * tC + tP + 1 : ℕ) : ℝ≥0∞) * u lam := by
  classical
  intro tC tP St Ct Pt hC hP
  have hexp : bindingExp (hashArg lam M) hashExt Ct Pt = Ct.withTrace.bind fun o1 =>
      (Pt o1.1.2).bind fun xp => .query (enc xp.1 xp.2) fun d =>
        .pure (⟨decide (d = o1.1.1), (hashExt (lam := lam) (M := M)).Ei o1.1.1 o1.2, xp.1, ()⟩ :
          BindingOutcome Bool Bool Unit) := by
    simp only [bindingExp, bind_eq, pure_eq, hashArg, hashExt, OComp.bind]
    congr 1
    funext o1
    exact withTrace_bind_fst (Pt o1.1.2) (fun xp =>
      .query (enc xp.1 xp.2) fun d =>
        .pure (⟨decide (d = o1.1.1),
            (List.find? (fun e => decide (e.2 = o1.1.1)) o1.2).bind fun e => List.head? e.1,
            xp.1,
            ()⟩ : BindingOutcome Bool Bool Unit))
  rw [Pr_eq_PrFrom, hexp, PrFrom_bind]
  refine le_trans
    (phase1 (((tP + 1 : ℕ) : ℝ≥0∞) * u lam) Ct tC (fun _ => none) ∅
      (fun o c' =>
        PrFrom c' ((Pt o.1.2).bind fun xp =>
            .query (enc xp.1 xp.2) fun d =>
              .pure (⟨decide (d = o.1.1), (hashExt (lam := lam) (M := M)).Ei o.1.1 o.2,
                  xp.1, ()⟩ : BindingOutcome Bool Bool Unit))
          (bindingBad eqR))
      hC (fun q q' r h => by cases h) (fun q r h => by cases h) (fun _ _ => PrFrom_le_one _ _ _) ?_)
    ?_
  · rintro ⟨ivk, st⟩ tr c' hn he
    simp only
    rw [PrFrom_bind]
    have hGc : ∀ (x : Bool) (s : ℕ), c' (enc x s) = some ivk →
        (hashExt (lam := lam) (M := M)).Ei ivk tr = some x := by
      intro x s h
      have hm : (enc x s, ivk) ∈ tr := ((he _ _).1 h).resolve_left (by simp)
      cases hf : tr.find? (fun e => decide (e.2 = ivk)) with
      | none =>
        have := List.find?_eq_none.1 hf _ hm
        simp at this
      | some e =>
        have h2 : e.2 = ivk := by simpa using List.find?_some hf
        have h3 : e ∈ tr := List.mem_of_find?_eq_some hf
        have h4 : c' e.1 = some ivk := (he _ _).2 (Or.inr (by rw [← h2]; exact h3))
        have h5 : e.1 = enc x s := hn _ _ _ h4 h
        simp [hashExt, hf, h5, enc]
    refine le_trans
      (phase2 (u lam) ivk
        (fun c =>
          ∀ (x : Bool) (s : ℕ),
            c (enc x s) = some ivk → (hashExt (lam := lam) (M := M)).Ei ivk tr = some x)
        ?_ (Pt st) tP c'
        (fun xp c2 =>
          PrFrom c2 (.query (enc xp.1 xp.2) fun d =>
              .pure (⟨decide (d = ivk), (hashExt (lam := lam) (M := M)).Ei ivk tr,
                  xp.1, ()⟩ : BindingOutcome Bool Bool Unit))
            (bindingBad eqR))
        (hP st) hGc (fun _ _ => PrFrom_le_one _ _ _) ?_) ?_
    · intro c q r hg hr x s h
      by_cases e : enc x s = q
      · rw [e, Function.update_self] at h
        cases h
        exact absurd rfl hr
      · rw [Function.update_of_ne e] at h
        exact hg x s h
    · intro xp c2 hg
      beta_reduce
      cases hq : c2 (enc xp.1 xp.2) with
      | some r =>
        rw [PrFrom_query_hit hq, PrFrom_pure, if_neg]
        · exact zero_le _
        · rw [mem_bad_iff]
          rintro ⟨h1, h2⟩
          have hr : r = ivk := by simpa using h1
          exact h2 (hg _ _ (by rw [hq, hr]))
      | none =>
        rw [PrFrom_query_miss hq]
        simp only [PrFrom_pure]
        refine le_trans
          (expect_uniform_le {ivk} _ 0 (fun r => by split_ifs <;> simp) fun r hr => ?_) (by simp)
        rw [if_neg]
        rw [mem_bad_iff]
        rintro ⟨h1, _⟩
        exact hr (by simpa using h1)
    · rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
  · rw [← add_mul, ← Nat.cast_add]
    exact cast_mul_mono (by simp; omega) _

lemma u_eq : u lam = ((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹ := by simp [u]

/-- The form `IsZKCPArgWith` (named form), proved for a scheme that hashes. -/
theorem hash_main_with : IsZKCPArgWith eqR (hashArg lam M) hashExt (hashSim lam M) 0
    (fun tC tP => ((tC * tC + tP + 1 : ℕ) : ℝ≥0∞) / ((2 ^ lam : ℕ) : ℝ≥0∞))
    (fun tV _ => (tV : ℝ≥0∞) / ((M + 1 : ℕ) : ℝ≥0∞)) where
  completeness := hash_complete lam M
  indexBinding := by simpa only [div_eq_mul_inv, ← u_eq] using hash_binding
  indexPrivacy := hash_private

/-- `hash_main_with` in the form `IsZKCPArg`. -/
theorem hash_main : IsZKCPArg eqR (hashArg lam M) 0
    (fun tC tP => ((tC * tC + tP + 1 : ℕ) : ℝ≥0∞) / ((2 ^ lam : ℕ) : ℝ≥0∞))
    (fun tV _ => (tV : ℝ≥0∞) / ((M + 1 : ℕ) : ℝ≥0∞)) :=
  hash_main_with.toIsZKCPArg

/-- For the honest committer the extractor finds the committed index, always [after the work that
this protocol builds on (lean/CREDITS.md, "Further work"): i* = i]. -/
theorem hash_extraction_correct :
    HasExtractionError (hashArg lam M) (hashExt (lam := lam) (M := M)) 0 := by
  intro i
  have h0 : ∀ f : Oracle lam, PrCoins f ((hashArg lam M).C i).withTrace
      {o | (hashExt (lam := lam) (M := M)).Ei o.1.1 o.2 ≠ some i} = 0 := by
    intro f
    simp [PrCoins, hashArg, OComp.withTrace, OComp.bind, OComp.run, prob_bind, prob_pure,
      hashExt, enc, expect_zero]
  rw [Pr, lintegral_congr h0]; simp

/-- The salt is needed. With a single possible salt (M = 0) one oracle query tells the two indices
apart: every simulator has 2·ζ(1,0) + 2^(-λ) ≥ 1. So the definition sees the difference between
t_V = 0 and t_V = 1. -/
theorem unsalted_not_private (ζ : ℕ → ℕ → ℝ≥0∞) (h : HasIndexPrivacy eqR (hashArg lam 0) ζ) :
    1 ≤ ζ 1 0 + ζ 1 0 + u lam := by
  classical
  obtain ⟨S, hS⟩ := h
  let Z : Env Bool Bool Unit (Fin (0 + 1)) := fun i _ => (i, ())
  let Vt : Digest lam → AdvVerifier lam Bool (Fin (0 + 1)) := fun _ =>
    .query (enc true 0) fun _ => .halt
  have hV : ∀ ivk, (Vt ivk).QueryBound 1 := fun _ _ => trivial
  have d₁ := (hS true Z (fun _ => rfl) 1 Vt 0 hV).1
  have d₂ := (hS false Z (fun _ => rfl) 1 Vt 0 hV).1
  have e : idealExp eqR S Vt (Z.onView false) false 0 =
      idealExp eqR S Vt (Z.onView true) true 0 := by
    simp only [idealExp, idealLoop, Vt, eqR]
  rw [e] at d₂
  let E : Set (View lam (Digest lam) Bool (Fin (0 + 1))) := {v | v.trace = [(enc true 0, v.ivk)]}
  have r₁ : Pr (realExp (hashArg lam 0) Vt (Z.onView true) true 0) (fun _ => E) = 1 := by
    rw [Pr_eq_PrFrom]
    simp only [realExp, hashArg, bind_eq, OComp.bind, realLoop, Vt, pure_eq, PrFrom_sample]
    have hin : ∀ s : Fin (0 + 1), PrFrom (fun _ => none) (OComp.query (enc true ↑s) fun d =>
        OComp.query (enc true 0) fun r => OComp.pure
          ({ ivk := d, sessions := [], trace := [] ++ [(enc true 0, r)], coins := [] } :
            View lam (Digest lam) Bool (Fin (0 + 1)))) E = 1 := by
      intro s
      have hs : (s : ℕ) = 0 := by omega
      rw [hs, PrFrom_query_miss rfl]
      have : ∀ d : Digest lam, PrFrom (Function.update (fun _ => none) (enc true 0) (some d))
          (OComp.query (enc true 0) fun r => OComp.pure
            ({ ivk := d, sessions := [], trace := [] ++ [(enc true 0, r)], coins := [] } :
              View lam (Digest lam) Bool (Fin (0 + 1)))) E = 1 := by
        intro d
        rw [PrFrom_query_hit (Function.update_self _ _ _), PrFrom_pure, if_pos]
        simp [E]
      simp only [this, expect_const]
    simp only [hin, expect_const]
  have r₂ : Pr (realExp (hashArg lam 0) Vt (Z.onView false) false 0) (fun _ => E) ≤ u lam := by
    rw [Pr_eq_PrFrom]
    simp only [realExp, hashArg, bind_eq, OComp.bind, realLoop, Vt, pure_eq, PrFrom_sample]
    refine expect_le_of_le _ fun s => ?_
    rw [PrFrom_query_miss rfl]
    refine expect_le_of_le _ fun d => ?_
    have hne : enc true 0 ≠ enc false ↑s := fun e => by simpa using (enc_inj e).1
    rw [PrFrom_query_miss (by rw [Function.update_of_ne hne])]
    simp only [PrFrom_pure]
    refine le_trans
      (expect_uniform_le {d} _ 0 (fun r => by split_ifs <;> simp) fun r hr => ?_) (by simp)
    rw [if_neg]
    intro hm
    apply hr
    simpa [E] using hm
  have a₁ := le_add_of_SD_le d₁ E
  have a₂ := le_add_of_SD_le d₂ Eᶜ
  rw [r₁] at a₁
  have a₃ : (1 : ℝ≥0∞) ≤ u lam + (prob (idealExp eqR S Vt (Z.onView true) true 0) Eᶜ + ζ 1 0) := by
    rw [← Pr_add_compl (realExp (hashArg lam 0) Vt (Z.onView false) false 0) E]
    exact add_le_add r₂ a₂
  have s : (1 : ℝ≥0∞) + 1 ≤ 1 + (ζ 1 0 + ζ 1 0 + u lam) := by
    calc (1 : ℝ≥0∞) + 1 ≤ (prob (idealExp eqR S Vt (Z.onView true) true 0) E + ζ 1 0) +
          (u lam + (prob (idealExp eqR S Vt (Z.onView true) true 0) Eᶜ + ζ 1 0)) := add_le_add a₁ a₃
      _ = (prob (idealExp eqR S Vt (Z.onView true) true 0) E +
              prob (idealExp eqR S Vt (Z.onView true) true 0) Eᶜ) +
            (ζ 1 0 + ζ 1 0 + u lam) := by ring
      _ = 1 + (ζ 1 0 + ζ 1 0 + u lam) := by rw [prob_add_compl]
  exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 s

end HashToy
end ZKCP
